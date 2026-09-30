//! Edition selection is frontend configuration, not IR acceptance evidence.
//! Read only the manifest schema and edition; qargo owns package management.

use std::fs;
use std::io::Read;
use std::path::Path;

use super::{LoadFailure, error, io_error, located_error, source_file};
use crate::frontend::{CURRENT_EDITION, ast::Span};

const MAX_MANIFEST_BYTES: u64 = 65_536;

pub(super) fn check_directory(directory: &Path) -> Result<(), LoadFailure> {
    for ancestor in directory.ancestors() {
        let path = ancestor.join("Qargo.toml");
        match fs::symlink_metadata(&path) {
            Err(failure) if failure.kind() == std::io::ErrorKind::NotFound => continue,
            Err(failure) => return Err(io_error(&path, failure)),
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
        return check_manifest(&path, &source);
    }
    Err(error(
        &directory.join("Qargo.toml"),
        Span::default(),
        "missing Qargo.toml: add schema-version = 2 and [qrate] edition = \"2026\" to the source tree's top-level directory",
    ))
}

pub(super) fn check_manifest(path: &Path, source: &str) -> Result<(), LoadFailure> {
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
