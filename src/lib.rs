extern crate syn;
extern crate synom;
extern crate proc_macro2;
extern crate mitochondria;
extern crate literalext;

use std::collections::HashMap;
use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::io::Read;
use std::io::Error as IoError;
use std::io::ErrorKind as IoErrorKind;
use std::fs::File;
use std::fmt;

use proc_macro2::Span;

use syn::{Item, ItemMod, ParseError, MetaItem, MetaNameValue, Lit, LitKind};
use syn::fold::Folder;

use mitochondria::OnceCell;

use literalext::LiteralExt;

macro_rules! try_opt {
    ($e:expr) => {
        match $e {
            Some(e) => e,
            None => return None,
        }
    }
}

// XXX(nika): Use failure here instead?
#[derive(Debug)]
pub enum Error {
    Parse(ParseError),
    Io(IoError),
    WhileParsing(PathBuf, Box<Error>),
}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}
impl From<IoError> for Error {
    fn from(e: IoError) -> Self {
        Error::Io(e)
    }
}
impl From<proc_macro2::LexError> for Error {
    fn from(e: proc_macro2::LexError) -> Self {
        Error::Parse(e.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Parse(ref e) => {
                write!(f, "Parse Error: ")?;
                e.fmt(f)
            }
            Error::Io(ref e) => {
                write!(f, "IO Error: ")?;
                e.fmt(f)
            }
            Error::WhileParsing(ref pb, ref cause) => {
                write!(f, "Error while parsing {}: ", pb.display())?;
                cause.fmt(f)
            }
        }
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str { "" }
}

struct FileInfo {
    path: PathBuf,
    source: String,
    lines: OnceCell<Vec<usize>>,
}

impl FileInfo {
    fn lines(&self) -> &[usize] {
        self.lines.init_once(|| {
            let mut lines = vec![0];
            let mut prev = 0;
            while let Some(len) = self.source[prev..].find('\n') {
                prev += len + 1;
                lines.push(prev);
            }
            lines
        })
    }
}

thread_local! {
    static NAME_MAP: RefCell<HashMap<String, FileInfo>> =
        RefCell::new(HashMap::new());
}

fn strip_shebang(mut content: &str) -> &str {
    // Strip the BOM if it is present
    const BOM: &'static str = "\u{feff}";
    if content.starts_with(BOM) {
        content = &content[BOM.len()..];
    }

    // Strip a shebang if it is present.
    if content.starts_with("#!") && !content.starts_with("#![") {
        if let Some(idx) = content.find('\n') {
            content = &content[idx..];
        } else {
            content = "";
        }
    }

    content
}

/// Parse a file, while also extracting information about the file's internal
/// name used by proc_macro.
fn parse_file_internal(s: &str) -> Result<(syn::File, Option<String>), Error> {
    let buf = synom::SynomBuffer::new(s.parse()?);
    let (rest, file) = <syn::File as synom::Synom>::parse(buf.begin())?;

    if rest.eof() {
        // NOTE: If we successfully parse, we want to peek at the first
        // token, and extract its source_file() information, so that we
        // can know what the artificial file name proc-macro generated
        // for us for the string we gave it was.
        let source_file = buf.begin()
            .token_tree()
            .map(|(_, t)| t.span.source_file().as_str().to_owned());

        Ok((file, source_file))
    } else if rest == buf.begin() {
        Err(ParseError::new("failed to parse anything").into())
    } else {
        Err(ParseError::new("failed to parse all tokens").into())
    }
}

/// This is a lot like syn::parse_file, except that it records the real name of
/// the file in TLS alongside proc_macro's generated name for the file. This
/// allows mapping spans back to their real filenames.
pub fn parse_real_file<P: AsRef<Path>>(path: P) -> Result<syn::File, Error> {
    let path = path.as_ref();

    let mut f = File::open(path)?;
    let mut s = String::new();
    f.read_to_string(&mut s)?;

    let (file, name) = parse_file_internal(strip_shebang(&s))
        .map_err(|e| Error::WhileParsing(path.to_owned(), Box::new(e)))?;

    // NOTE: If we didn't get a name, that means that the source file contained
    // no tokens, so we don't have to record any information.
    if let Some(name) = name {
        NAME_MAP.with(|nm| {
            let mut nm = nm.borrow_mut();
            assert!(!nm.contains_key(&name));
            nm.insert(name, FileInfo {
                path: path.to_owned(),
                source: s,
                lines: OnceCell::new(),
            });
        });
    }

    Ok(file)
}

fn discover_mod_path(path: &Path, module: &ItemMod) -> Result<PathBuf, Error> {
    // Determine the path of the inner module's file
    for attr in &module.attrs {
        match attr.meta_item() {
            Some(MetaItem::NameValue(MetaNameValue {
                ref ident,
                lit: Lit {
                    value: LitKind::Other(ref lit),
                    ..
                },
                ..
            })) => if ident.as_ref() == "path" {
                if let Some(s) = lit.parse_string() {
                    let explicit = path.join(&s[..]);
                    return Ok(explicit);
                }
            },
            _ => {}
        }
    }

    let mut subdir = path.join(module.ident.as_ref());
    subdir.push("mod.rs");
    if subdir.is_file() {
        return Ok(subdir);
    }

    let adjacent = path.join(&format!("{}.rs", module.ident));
    if adjacent.is_file() {
        return Ok(adjacent);
    }

    Err(IoError::new(
        IoErrorKind::NotFound,
        format!("No file with module definition for `mod {}`", module.ident),
    ).into())
}

fn load_mod(base: &Path, module: &ItemMod) -> Result<Vec<Item>, Error> {
    let path = discover_mod_path(base, module)?;
    Ok(parse_real_file(path)?.items)
}

struct Fld<'a, 'b> {
    error: &'a mut Option<Error>,
    base: &'b Path,
}
impl<'a, 'b> Folder for Fld<'a, 'b> {
    fn fold_item_mod(&mut self, mut m: ItemMod) -> ItemMod {
        // If we saw an error, we can start to abort early.
        if self.error.is_some() {
            return m;
        }

        m.content = match m.content {
            None => match load_mod(self.base, &m) {
                Ok(items) => Some((Default::default(), items)),
                Err(err) => {
                    *self.error = Some(err);
                    None
                }
            }
            Some((brace, its)) => {
                // If we're in an inline module we need to change base, and
                // parse with a new one.
                let new_base = self.base.join(m.ident.as_ref());
                let mut folder = Fld {
                    error: self.error,
                    base: &new_base,
                };
                let its = its.into_iter()
                    .map(|i| folder.fold_item(i))
                    .collect::<Vec<_>>();
                Some((brace, its))
            }
        };
        m
    }
}

pub fn parse_crate<P: AsRef<Path>>(path: P) -> Result<syn::File, Error> {
    let path = path.as_ref();
    let file = parse_real_file(path)?;

    let mut err = None;

    // NOTE: We can unwrap parent() here because we just read a file, so it
    // should have a parent directory.
    let file = Fld {
        error: &mut err,
        base: path.parent().unwrap(),
    }.fold_file(file);

    if let Some(err) = err {
        return Err(Error::WhileParsing(path.to_owned(), Box::new(err)));
    }

    Ok(file)
}

/// This extension trait is implemented on Span objects and provides tools for
/// extracting information which is not provided by the proc_macro2 span
/// implementation.
pub trait SpanExt {
    /// Get the path to the real file backing this span. If the real file is not
    /// know, returns None.
    fn file_path(&self) -> Option<PathBuf>;

    /// Get the raw text which this span represents. Can return None if this
    /// span doesn't represent a real file.
    fn raw_text(&self) -> Option<String>;
}

impl SpanExt for Span {
    fn file_path(&self) -> Option<PathBuf> {
        let s = self.source_file();
        NAME_MAP.with(|nm| {
            let nm = nm.borrow();
            let fi = try_opt!(nm.get(s.as_str()));
            Some(fi.path.clone())
        })
    }

    fn raw_text(&self) -> Option<String> {
        //  Unfortunately we don't have byte offsets exposed to us, so we have
        //  to re-discover them :'-(
        let start = self.start();
        let end = self.end();
        let s = self.source_file();

        NAME_MAP.with(|nm| {
            let nm = nm.borrow();
            let fi = try_opt!(nm.get(s.as_str()));

            let lines = fi.lines();
            let start_off = lines[start.line - 1] + start.column;
            let end_off = lines[end.line - 1] + end.column;
            Some(fi.source[start_off..end_off].to_owned())
        })
    }
}
