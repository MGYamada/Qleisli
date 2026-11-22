//! Edition selection is frontend configuration, not IR acceptance evidence.
//! User manifests select schema and edition. qlirgo owns package management.
//! Only the embedded std also requires this distribution's exact product version.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

use super::{BundledRegistry, LoadFailure, error, io_error, located_error, source_file};
use crate::edition::Edition;
use crate::frontend::ast::Span;

/// The exact validated manifest selected for a source, retained without rereading.
/// This requested context confers no native acceptance or source preservation proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EditionManifest {
    path: PathBuf,
    source: Arc<str>,
    bytes_read: u64,
    edition: Edition,
}

impl EditionManifest {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn source(&self) -> &str {
        &self.source
    }
    pub(super) fn bytes_read(&self) -> u64 {
        self.bytes_read
    }
    pub fn edition(&self) -> Edition {
        self.edition
    }
}

fn capture(path: &Path, source: String) -> Result<EditionManifest, LoadFailure> {
    let (_, edition) = parse_manifest(path, &source)?;
    Ok(EditionManifest {
        path: path.into(),
        bytes_read: source.len() as u64,
        source: source.into(),
        edition,
    })
}

const MAX_MANIFEST_BYTES: u64 = 65_536;
const EDITION_SELECTION: &str = "The edition selects the constitutional regime independently of \
    the compiler release and source grammar.";

#[cfg(test)]
std::thread_local! { static PARSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }

// Only these compile-time embedded bytes are invariant across loads. External
// manifests and source judgments always run afresh through their normal paths.
pub(super) fn check_bundled() -> Result<(), LoadFailure> {
    static RESULT: OnceLock<Result<(), LoadFailure>> = OnceLock::new();
    RESULT
        .get_or_init(|| {
            check_bundled_manifest(
                Path::new(BundledRegistry::manifest_path()),
                BundledRegistry::manifest(),
            )
        })
        .clone()
}

const CANONICAL: &str = "Qlirgo.toml";
const LEGACY: &str = "Qargo.toml";

// Called once per discovered directory. A nested directory inherits the already
// checked parent edition; its own manifest, when present, must pass afresh.
pub(super) fn read_anchored(
    directory: &Path,
    anchor: &fs::File,
) -> Result<Option<EditionManifest>, LoadFailure> {
    select(directory, Some(anchor))
}

fn select(
    directory: &Path,
    anchor: Option<&fs::File>,
) -> Result<Option<EditionManifest>, LoadFailure> {
    let canonical = read_manifest(directory, anchor, CANONICAL)?;
    let legacy = read_manifest(directory, anchor, LEGACY)?;
    let (name, bytes, extra_bytes) = match (canonical, legacy) {
        (Some(canonical), Some(legacy)) => {
            if canonical != legacy {
                return Err(error(
                    &directory.join(CANONICAL),
                    Span::default(),
                    "Qlirgo.toml and Qargo.toml must have identical bytes",
                ));
            }
            (CANONICAL, canonical, legacy.len() as u64)
        }
        (Some(bytes), None) => (CANONICAL, bytes, 0),
        (None, Some(bytes)) => (LEGACY, bytes, 0),
        (None, None) => return Ok(None),
    };
    let path = directory.join(name);
    let source = String::from_utf8(bytes)
        .map_err(|_| error(&path, Span::default(), format!("{name} is not valid UTF-8")))?;
    let mut manifest = capture(&path, source)?;
    manifest.bytes_read += extra_bytes;
    Ok(Some(manifest))
}

fn read_manifest(
    directory: &Path,
    anchor: Option<&fs::File>,
    name: &str,
) -> Result<Option<Vec<u8>>, LoadFailure> {
    let path = directory.join(name);
    let non_regular = || {
        error(
            &path,
            Span::default(),
            format!("{name} must be a regular, non-symlink file"),
        )
    };
    let regular = match anchor {
        Some(anchor) => source_file::kind(anchor, directory, name.as_ref())
            .map(|kind| matches!(kind, source_file::Kind::File)),
        None => fs::symlink_metadata(&path).map(|meta| meta.is_file()),
    };
    match regular {
        Ok(true) => {}
        Ok(false) => return Err(non_regular()),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(io_error(&path, e)),
    }
    let file = match anchor {
        Some(anchor) => source_file::child(anchor, directory, name.as_ref(), false),
        None => source_file::open(&path),
    }
    .map_err(|e| io_error(&path, e))?;
    if !file.metadata().map_err(|e| io_error(&path, e))?.is_file() {
        return Err(non_regular());
    }
    let mut bytes = Vec::new();
    file.take(MAX_MANIFEST_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| io_error(&path, e))?;
    if bytes.len() as u64 > MAX_MANIFEST_BYTES {
        return Err(error(
            &path,
            Span::default(),
            format!("{name} exceeds the 65536-byte manifest limit"),
        ));
    }
    Ok(Some(bytes))
}

pub(super) fn read_directory(directory: &Path) -> Result<EditionManifest, LoadFailure> {
    for ancestor in directory.ancestors() {
        if let Some(manifest) = select(ancestor, None)? {
            return Ok(manifest);
        }
    }
    Err(error(
        &directory.join(CANONICAL),
        Span::default(),
        format!(
            "missing {CANONICAL}: add schema-version = 2 and [qrate] edition = \"2026\" \
             to the source tree's top-level directory. {EDITION_SELECTION}"
        ),
    ))
}

#[cfg(test)]
pub(super) fn check_manifest(path: &Path, source: &str) -> Result<(), LoadFailure> {
    parse_manifest(path, source).map(|_| ())
}

// Distribution identity is a packaging precondition, never semantic authority.
// User qrates keep their own versions and are not subject to this private gate.
fn check_bundled_manifest(path: &Path, source: &str) -> Result<(), LoadFailure> {
    let (manifest, _) = parse_manifest(path, source)?;
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
    let qrate = manifest.get("qrate").and_then(toml::Value::as_table);
    if qrate
        .and_then(|qrate| qrate.get("name"))
        .and_then(toml::Value::as_str)
        != Some("std")
    {
        return Err(invalid(
            "bundled std requires string [qrate].name = \"std\"; select the matching Qleisli distribution"
                .to_owned(),
        ));
    }
    let version = qrate.and_then(|qrate| qrate.get("version"));
    if version.and_then(toml::Value::as_str) != Some(env!("CARGO_PKG_VERSION")) {
        let actual = match version {
            None => "<missing>".to_owned(),
            Some(toml::Value::String(version)) => format!("{version:?}"),
            Some(_) => "<non-string>".to_owned(),
        };
        return Err(invalid(format!(
            "bundled std requires string [qrate].version = \"{}\"; actual {actual}; select the matching Qleisli distribution rather than another std version",
            env!("CARGO_PKG_VERSION")
        )));
    }
    Ok(())
}

fn parse_manifest(path: &Path, source: &str) -> Result<(toml::Table, Edition), LoadFailure> {
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
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(CANONICAL);
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
            format!("invalid {name}: {failure}"),
        )
    })?;
    if manifest
        .get("schema-version")
        .and_then(toml::Value::as_integer)
        != Some(2)
    {
        return Err(invalid(format!("{name} requires schema-version = 2")));
    }
    let edition = manifest
        .get("qrate")
        .and_then(toml::Value::as_table)
        .and_then(|qrate| qrate.get("edition"))
        .and_then(toml::Value::as_str)
        .ok_or_else(|| {
            invalid(format!(
                "{name} requires an explicit string [qrate].edition. \
                 Add edition = \"2026\" under [qrate]. {EDITION_SELECTION}"
            ))
        })?;
    let edition = edition
        .parse::<Edition>()
        .map_err(|failure| invalid(format!("{failure}. {EDITION_SELECTION}")))?;
    Ok((manifest, edition))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_manifest_accounting_checks_capacity_and_overflow_before_commit() {
        use super::super::{SourceBudget, SourcePolicy};
        let path = Path::new("Qargo.toml");
        let mut budget = SourceBudget {
            policy: SourcePolicy::Bounded {
                source_bytes: 1,
                project_bytes: 64,
            },
            used: 0,
        };
        budget
            .charge_manifest(path, 64)
            .unwrap_or_else(|e| panic!("{}", e.error));
        assert_eq!(budget.used, 64);
        assert!(budget.charge_manifest(path, 1).is_err());
        assert_eq!(budget.used, 64);
        assert!(budget.charge_manifest(path, u64::MAX).is_err());
        assert_eq!(budget.used, 64);
        let mut legacy = SourceBudget {
            policy: SourcePolicy::Legacy,
            used: 0,
        };
        assert!(legacy.charge_manifest(path, u64::MAX).is_ok());
    }
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
        // Initialize the process-wide embedded result before measuring this
        // thread's external parses; another test may already have initialized it.
        check_bundled().unwrap_or_else(|e| panic!("{}", e.error));
        for _ in 0..2 {
            let before = PARSES.with(|count| count.get());
            check_bundled().unwrap_or_else(|e| panic!("{}", e.error));
            super::super::Project::load_with_policy(&path, super::super::SourcePolicy::default())
                .unwrap();
            assert_eq!(
                PARSES.with(|count| count.get()) - before,
                1,
                "one fresh local parse; no repeat embedded parse"
            );
        }
        fs::write(
            path.join("Qargo.toml"),
            "schema-version=2\n[qrate]\nedition='2027'\n",
        )
        .unwrap();
        let failure =
            super::super::Project::load_with_policy(&path, super::super::SourcePolicy::default())
                .unwrap_err();
        assert!(failure.message.contains("unsupported Qleisli edition"));
    }

    #[test]
    fn first_manifest_observations_remain_valid_user_controls() {
        let source = fs::read(Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "tests/fixtures/authoring_sessions/canonical-std-pair-v030/first-observations.txt",
        ))
        .unwrap();
        let first = crate::interchange::json::parse(&source).unwrap();
        let cases = first.field("cases").unwrap().array().unwrap();
        assert_eq!(cases.len(), 15);
        let stdout = first.field("stdout").unwrap().text().unwrap();
        for case in cases {
            let id = case.field("id").unwrap().text().unwrap();
            let source = case.field("source").unwrap().text().unwrap();
            assert_eq!(
                case.field("first_current_result").unwrap().text().unwrap(),
                "ok"
            );
            assert!(stdout.contains(&format!("canonical-std-observation {id} ok\n")));
            let before = PARSES.with(|count| count.get());
            check_manifest(Path::new("user/Qargo.toml"), source)
                .unwrap_or_else(|e| panic!("{id}: {}", e.error));
            assert_eq!(PARSES.with(|count| count.get()) - before, 1);
        }
    }

    #[test]
    fn embedded_std_requires_exact_name_and_complete_product_version() {
        let path = Path::new(BundledRegistry::manifest_path());
        let source = BundledRegistry::manifest();
        let product = env!("CARGO_PKG_VERSION");
        check_bundled_manifest(path, source).unwrap_or_else(|e| panic!("{}", e.error));
        let name_line = "name = \"std\"";
        let version_line = format!("version = \"{product}\"");
        assert_eq!(source.matches(name_line).count(), 1);
        assert_eq!(source.matches(&version_line).count(), 1);
        let mut mutants = vec![
            (
                "missing-name",
                source.replacen(name_line, "", 1),
                "name",
                None,
            ),
            (
                "wrong-name",
                source.replacen(name_line, "name = \"other\"", 1),
                "name",
                None,
            ),
            (
                "name-not-string",
                source.replacen(name_line, "name = 17", 1),
                "name",
                None,
            ),
            (
                "missing-version",
                source.replacen(&version_line, "", 1),
                "version",
                Some("<missing>".to_owned()),
            ),
            (
                "version-not-string",
                source.replacen(&version_line, "version = 17", 1),
                "version",
                Some("<non-string>".to_owned()),
            ),
        ];
        // Preserve the first release/prerelease fault families while generating
        // current-product mutants; historical observation bytes stay untouched.
        let different = |candidate: String| {
            if candidate == product {
                "0.0.0-stale-canonical-std-test".to_owned()
            } else {
                candidate
            }
        };
        let core = product.split(['-', '+']).next().unwrap();
        for (id, version) in [
            ("older-version", different("0.2.9".to_owned())),
            ("newer-version", different("0.3.1".to_owned())),
            ("release-versus-beta", different(core.to_owned())),
            ("other-prerelease", different(format!("{core}-other"))),
            ("leading-v", format!("v{product}")),
            ("version-whitespace", format!("{product} ")),
            ("different-build-identifier", format!("{product}+different")),
        ] {
            mutants.push((
                id,
                source.replacen(&version_line, &format!("version = \"{version}\""), 1),
                "version",
                Some(format!("{version:?}")),
            ));
        }
        assert_eq!(mutants.len(), 12);
        for (id, source, field, expected_actual) in mutants {
            let before = PARSES.with(|count| count.get());
            let failure = check_bundled_manifest(path, &source)
                .err()
                .unwrap_or_else(|| panic!("{id}: mismatched bundled identity was accepted"));
            assert_eq!(PARSES.with(|count| count.get()) - before, 1, "{id}");
            assert_eq!(failure.code, "project", "{id}");
            assert_eq!(failure.error.path, path, "{id}");
            assert_eq!(
                failure.error.span,
                Span {
                    start: 0,
                    end: source.len()
                },
                "{id}"
            );
            assert_eq!(failure.coordinates, Some((1, 1)), "{id}");
            assert!(
                failure.error.message.contains(&format!("[qrate].{field}")),
                "{id}"
            );
            assert!(
                failure
                    .error
                    .message
                    .contains("matching Qleisli distribution"),
                "{id}"
            );
            if let Some(expected_actual) = expected_actual {
                assert!(
                    failure
                        .error
                        .message
                        .contains(&format!("version = \"{product}\"")),
                    "{id}"
                );
                assert!(
                    failure
                        .error
                        .message
                        .contains(&format!("; actual {expected_actual};")),
                    "{id}"
                );
            }
            // The same strings remain valid ordinary user manifests.
            check_manifest(Path::new("user/Qargo.toml"), &source)
                .unwrap_or_else(|e| panic!("{id}: {}", e.error));
        }
        // A string diagnostic must quote embedded controls and quotes rather
        // than introducing a second diagnostic line.
        let quoted = source.replacen(&version_line, r#"version = "stale\n\"id""#, 1);
        let failure = check_bundled_manifest(path, &quoted).err().unwrap();
        assert!(failure.error.message.contains(r#"; actual "stale\n\"id";"#));
        assert!(!failure.error.message.contains('\n'));
        check_manifest(Path::new("user/Qargo.toml"), &quoted)
            .unwrap_or_else(|e| panic!("{}", e.error));
    }

    #[test]
    fn embedded_pair_gate_preserves_schema_edition_and_toml_diagnostics() {
        let path = Path::new(BundledRegistry::manifest_path());
        for source in [
            "schema-version=1\n[qrate]\nedition='2026'\n",
            "schema-version=2\n[qrate]\nedition='2027'\n",
            "schema-version=2\n[qrate]\nedition=2026\n",
            "schema-version=2\n[qrate]\nedition='2026'\n[qrate]\n",
        ] {
            let generic = check_manifest(path, source).err().unwrap();
            let bundled = check_bundled_manifest(path, source).err().unwrap();
            assert_eq!(bundled.code, generic.code);
            assert_eq!(bundled.coordinates, generic.coordinates);
            assert_eq!(bundled.error.path, generic.error.path);
            assert_eq!(bundled.error.span, generic.error.span);
            assert_eq!(bundled.error.message, generic.error.message);
        }
    }
}
