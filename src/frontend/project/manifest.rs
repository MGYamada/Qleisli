//! Additive host configuration. Legacy Project::load still uses its explicit
//! caller root; qrate root selection is opt-in and grants no acceptance evidence.

use super::{Diagnostic, Span, edition, error, io_error, located_error};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// Select the explicitly declared `[source].root` beneath a qrate directory.
/// This does not implement qargo package/dependency/test/doc orchestration.
pub fn qrate_source_root(directory: &Path) -> Result<PathBuf, Diagnostic> {
    let root = fs::canonicalize(directory).map_err(|e| io_error(directory, e).into_diagnostic())?;
    let (path, source) =
        edition::read_directory(&root).map_err(super::LoadFailure::into_diagnostic)?;
    let fail = |message| {
        located_error(
            &path,
            &source,
            Span {
                start: 0,
                end: source.len(),
            },
            "project",
            message,
        )
        .into_diagnostic()
    };
    if path.parent() != Some(root.as_path()) {
        return Err(fail(
            "--qrate requires Qargo.toml in the selected qrate directory",
        ));
    }
    let manifest: toml::Table = source.parse().expect("edition parser validated TOML");
    let relative = manifest
        .get("source")
        .and_then(toml::Value::as_table)
        .and_then(|source| source.get("root"))
        .and_then(toml::Value::as_str)
        .ok_or_else(|| fail("--qrate requires an explicit string [source].root"))?;
    let mut selected = root;
    let mut count = 0;
    for component in Path::new(relative).components() {
        let Component::Normal(name) = component else {
            return Err(fail(
                "[source].root must be a nonempty relative directory path without parent traversal",
            ));
        };
        if name == "target" {
            return Err(fail("[source].root cannot select a target build directory"));
        }
        selected.push(name);
        count += 1;
        let metadata = fs::symlink_metadata(&selected)
            .map_err(|e| io_error(&selected, e).into_diagnostic())?;
        if !metadata.is_dir() || metadata.file_type().is_symlink() {
            return Err(error(
                &selected,
                Span::default(),
                "[source].root must traverse only non-symlink directories",
            )
            .into_diagnostic());
        }
    }
    if count == 0 {
        return Err(fail(
            "[source].root must select a nonempty relative directory path",
        ));
    }
    Ok(selected)
}

/// Report unused manifest keys without rejecting previously accepted metadata.
/// Known fields follow qargo's schema-2 local manifest; metadata validation
/// beyond edition and opt-in source selection remains qargo's responsibility.
pub fn manifest_warnings(directory: &Path) -> Result<Vec<Diagnostic>, Diagnostic> {
    let directory =
        fs::canonicalize(directory).map_err(|e| io_error(directory, e).into_diagnostic())?;
    let (path, source) =
        edition::read_directory(&directory).map_err(super::LoadFailure::into_diagnostic)?;
    let manifest: toml::Table = source.parse().expect("edition parser validated TOML");
    let mut unused = Vec::new();
    for (key, value) in manifest {
        let allowed: &[&str] = match key.as_str() {
            "schema-version" => continue,
            "qrate" => &["name", "version", "edition"],
            "source" | "tests" | "docs" => &["root"],
            _ => {
                unused.push(key);
                continue;
            }
        };
        if let Some(table) = value.as_table() {
            for nested in table
                .keys()
                .filter(|nested| !allowed.contains(&nested.as_str()))
            {
                unused.push(format!("{key}.{nested}"));
            }
        }
    }
    unused.sort();
    Ok(unused.into_iter().map(|key| located_error(&path,&source,
        Span{start:0,end:source.len()},"project",
        format!("unused manifest key `{key}` in {}; this Qleisli command ignores it; check the schema-2 spelling (qargo may reject unsupported metadata)",path.display()))
        .into_diagnostic()).collect())
}
