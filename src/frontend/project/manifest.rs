//! Additive host configuration. Legacy Project::load still uses its explicit
//! caller root; qrate root selection is opt-in and grants no acceptance evidence.

use super::{Diagnostic, Span, edition, error, io_error, located_error};
use std::fs;
use std::path::{Component, Path, PathBuf};

/// A selected qrate root whose path is never re-canonicalized during loading.
/// On Unix, discovery and reads are relative to the held directory identity;
/// replacing a pathname cannot redirect them into the replacement tree.
/// File contents may still change concurrently; this is not a filesystem snapshot.
pub struct QrateSource {
    root: PathBuf,
    directory: fs::File,
}

impl QrateSource {
    /// Select a qrate root and acquire it without following replacement links.
    pub fn select(directory: &Path) -> Result<Self, Diagnostic> {
        let root = qrate_source_root(directory)?;
        let directory = super::source_file::open_directory(&root)
            .map_err(|e| io_error(&root, e).into_diagnostic())?;
        Ok(Self { root, directory })
    }

    /// Selected source identity for diagnostics; do not canonicalize it again.
    pub fn path(&self) -> &Path {
        &self.root
    }

    pub(super) fn unchanged(&self) -> Result<(), super::LoadFailure> {
        let current =
            super::source_file::open_directory(&self.root).map_err(|e| io_error(&self.root, e))?;
        let held = self
            .directory
            .metadata()
            .map_err(|e| io_error(&self.root, e))?;
        let current = current.metadata().map_err(|e| io_error(&self.root, e))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            if (held.dev(), held.ino()) != (current.dev(), current.ino()) {
                return Err(error(
                    &self.root,
                    Span::default(),
                    "selected source root was replaced",
                ));
            }
        }
        #[cfg(not(unix))]
        let _ = (held, current); // Other targets retain the filesystem trust assumption.
        Ok(())
    }

    /// Load this selection without resolving a replacement symlink to another tree.
    pub fn load_with_policy(
        &self,
        policy: super::SourcePolicy,
    ) -> Result<super::Project, Diagnostic> {
        self.unchanged()
            .map_err(super::LoadFailure::into_diagnostic)?;
        let project = super::Project::load_anchored(&self.root, &self.directory, policy)
            .map_err(super::LoadFailure::into_diagnostic)?;
        self.unchanged()
            .map_err(super::LoadFailure::into_diagnostic)?;
        Ok(project)
    }
}

/// Select the explicitly declared `[source].root` beneath a qrate directory.
/// This does not implement qargo package/dependency/test/doc orchestration.
/// This legacy path-only query does not retain directory identity. For subsequent
/// loading/checking/compilation use [`QrateSource`] instead.
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
        let name = match component {
            Component::CurDir => continue,
            Component::Normal(name) => name,
            Component::ParentDir => {
                return Err(fail("[source].root cannot contain parent traversal"));
            }
            _ => return Err(fail("[source].root must be a relative directory path")),
        };
        if name.as_encoded_bytes().eq_ignore_ascii_case(b"target") {
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
                unused.push((key, false));
                continue;
            }
        };
        if let Some(table) = value.as_table() {
            for nested in table
                .keys()
                .filter(|nested| !allowed.contains(&nested.as_str()))
            {
                unused.push((format!("{key}.{nested}"), false));
            }
        } else {
            unused.push((key, true));
        }
    }
    unused.sort();
    Ok(unused.into_iter().map(|(key, non_table)| located_error(&path,&source,
        Span{start:0,end:source.len()},"project",
        if non_table {
            format!("manifest key `{key}` must be a table; this Qleisli command ignores it; check the schema-2 spelling")
        } else {
            format!("unused manifest key `{key}`; this Qleisli command ignores it; check the schema-2 spelling (qargo may reject unsupported metadata)")
        })
        .into_diagnostic()).collect())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    #[test]
    fn a_transient_root_replacement_between_identity_checks_is_rejected() {
        let path = std::env::temp_dir().join(format!(
            "qleisli-root-aba-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&path).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(path.clone());
        fs::write(
            path.join("Qargo.toml"),
            "schema-version=2\n[qrate]\nedition='2026'\n[source]\nroot='src'\n",
        )
        .unwrap();
        fs::create_dir(path.join("src")).unwrap();
        fs::write(path.join("src/main.qli"), "observe fn main()->Bit{1}").unwrap();
        let selected = QrateSource::select(&path).unwrap();
        // Schedule exactly the previously vulnerable interval. The two public
        // pre/post pathname checks both succeed; loading must still reject B.
        assert!(selected.unchanged().is_ok());
        fs::rename(path.join("src"), path.join("saved")).unwrap();
        fs::create_dir(path.join("src")).unwrap();
        fs::write(path.join("src/main.qli"), "observe fn main()->Bit{0}").unwrap();
        let result = super::super::Project::load_anchored(
            selected.path(),
            &selected.directory,
            super::super::SourcePolicy::default(),
        );
        // The traversal primitive itself remains anchored to A, even while the
        // original name resolves to B (and without relying on more path checks).
        let mut original = super::super::source_file::child(
            &selected.directory,
            selected.path(),
            "main.qli".as_ref(),
            false,
        )
        .unwrap();
        let mut source = String::new();
        std::io::Read::read_to_string(&mut original, &mut source).unwrap();
        assert!(source.contains("{1}"));
        fs::remove_dir_all(path.join("src")).unwrap();
        fs::rename(path.join("saved"), path.join("src")).unwrap();
        assert!(selected.unchanged().is_ok());
        assert!(result.err().unwrap().error.message.contains("replaced"));
        selected
            .load_with_policy(super::super::SourcePolicy::default())
            .unwrap();
    }
}
