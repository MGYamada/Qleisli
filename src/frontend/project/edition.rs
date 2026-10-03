//! Edition selection is frontend configuration, not IR acceptance evidence.
//! Read only the manifest schema and edition; qargo owns package management.

use std::fs;
use std::io::Read;
use std::path::Path;

use super::{LoadFailure, error, io_error, located_error, source_file};
use crate::frontend::{CURRENT_EDITION, ast::Span};

const MAX_MANIFEST_BYTES: u64 = 65_536;

#[cfg(test)]
std::thread_local! { static PARSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

// Called once per discovered directory. A nested directory inherits the already
// checked parent edition; its own manifest, when present, must pass afresh.
pub(super) fn check_anchored(
    directory: &Path,
    anchor: &fs::File,
    root: bool,
) -> Result<(), LoadFailure> {
    let path = directory.join("Qargo.toml");
    match source_file::kind(anchor, directory, "Qargo.toml".as_ref()) {
        Ok(source_file::Kind::File) => {}
        Ok(_) => {
            return Err(error(
                &path,
                Span::default(),
                "Qargo.toml must be a regular, non-symlink file",
            ));
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return if root {
                check_directory(directory.parent().unwrap_or(directory))
            } else {
                Ok(())
            };
        }
        Err(e) => return Err(io_error(&path, e)),
    }
    let file =
        match source_file::child(anchor, directory, std::ffi::OsStr::new("Qargo.toml"), false) {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                return if root {
                    check_directory(directory.parent().unwrap_or(directory))
                } else {
                    Ok(())
                };
            }
            Err(e) => return Err(io_error(&path, e)),
        };
    if !file.metadata().map_err(|e| io_error(&path, e))?.is_file() {
        return Err(error(
            &path,
            Span::default(),
            "Qargo.toml must be a regular, non-symlink file",
        ));
    }
    let mut bytes = Vec::new();
    file.take(MAX_MANIFEST_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| io_error(&path, e))?;
    if bytes.len() as u64 > MAX_MANIFEST_BYTES {
        return Err(error(
            &path,
            Span::default(),
            "Qargo.toml exceeds the 65536-byte manifest limit",
        ));
    }
    let source = String::from_utf8(bytes)
        .map_err(|_| error(&path, Span::default(), "Qargo.toml is not valid UTF-8"))?;
    check_manifest(&path, &source)
}

pub(super) fn check_directory(directory: &Path) -> Result<(), LoadFailure> {
    read_directory(directory).map(|_| ())
}

pub(super) fn read_directory(
    directory: &Path,
) -> Result<(std::path::PathBuf, String), LoadFailure> {
    for ancestor in directory.ancestors() {
        let path = ancestor.join("Qargo.toml");
        match fs::symlink_metadata(&path) {
            Err(failure) if failure.kind() == std::io::ErrorKind::NotFound => continue,
            Err(failure) => return Err(io_error(&path, failure)),
            Ok(metadata) if !metadata.file_type().is_file() => {
                return Err(error(
                    &path,
                    Span::default(),
                    "Qargo.toml must be a regular, non-symlink file",
                ));
            }
            Ok(_) => {}
        }
        // Do not skip a malformed, unreadable or symlinked nearer manifest.
        let file = source_file::open(&path).map_err(|failure| io_error(&path, failure))?;
        let mut bytes = Vec::new();
        file.take(MAX_MANIFEST_BYTES + 1)
            .read_to_end(&mut bytes)
            .map_err(|failure| io_error(&path, failure))?;
        if bytes.len() as u64 > MAX_MANIFEST_BYTES {
            return Err(error(
                &path,
                Span::default(),
                "Qargo.toml exceeds the 65536-byte manifest limit",
            ));
        }
        let source = String::from_utf8(bytes)
            .map_err(|_| error(&path, Span::default(), "Qargo.toml is not valid UTF-8"))?;
        check_manifest(&path, &source)?;
        return Ok((path, source));
    }
    Err(error(
        &directory.join("Qargo.toml"),
        Span::default(),
        "missing Qargo.toml: add schema-version = 2 and [qrate] edition = \"2026\" to the source tree's top-level directory",
    ))
}

pub(super) fn check_manifest(path: &Path, source: &str) -> Result<(), LoadFailure> {
    #[cfg(test)]
    PARSES.with(|count| count.set(count.get() + 1));
    let invalid = |message| {
        located_error(
            path,
            source,
            Span {
                start: 0,
                end: source.len(),
            },
            "project",
            message,
        )
    };
    let manifest = source.parse::<toml::Table>().map_err(|failure| {
        let range = failure.span().unwrap_or(0..source.len());
        located_error(
            path,
            source,
            Span {
                start: range.start,
                end: range.end,
            },
            "project",
            format!("invalid Qargo.toml: {failure}"),
        )
    })?;
    if manifest
        .get("schema-version")
        .and_then(toml::Value::as_integer)
        != Some(2)
    {
        return Err(invalid("Qargo.toml requires schema-version = 2".to_owned()));
    }
    let edition = manifest
        .get("qrate")
        .and_then(toml::Value::as_table)
        .and_then(|qrate| qrate.get("edition"))
        .and_then(toml::Value::as_str)
        .ok_or_else(|| invalid("Qargo.toml requires an explicit string [qrate].edition; add edition = \"2026\" (there is no default)".to_owned()))?;
    if edition != CURRENT_EDITION {
        return Err(invalid(format!(
            "unsupported Qleisli edition {edition:?}; only \"{CURRENT_EDITION}\" is supported"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_load_parses_each_manifest_once_even_with_many_empty_sources() {
        let path = std::env::temp_dir().join(format!(
            "qleisli-edition-cache-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&path).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(path.clone());
        fs::write(
            path.join("Qargo.toml"),
            "schema-version=2\n[qrate]\nedition='2026'\n",
        )
        .unwrap();
        fs::create_dir(path.join("nested")).unwrap();
        for i in 0..32 {
            fs::write(path.join(format!("file{i}.qli")), "").unwrap();
            fs::write(path.join(format!("nested/file{i}.qlt")), "").unwrap();
        }
        let before = PARSES.with(|count| count.get());
        super::super::Project::load_with_policy(&path, super::super::SourcePolicy::default())
            .unwrap();
        assert_eq!(
            PARSES.with(|count| count.get()) - before,
            2,
            "one local manifest and one embedded stdlib manifest"
        );
    }
}
