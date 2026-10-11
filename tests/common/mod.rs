//! Temporary source projects and native acceptance shared by integration tests.
#![allow(dead_code)]

use std::fs;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

/// Verify the explicit namespace/coherent file chain without changing originals.
pub(super) fn current_namespace_fixture(path: &Path) -> PathBuf {
    // Python's standard library supplies the repository's fixture hashing,
    // without adding a Rust dependency or changing production acceptance.
    let output = Command::new("python3")
        .args([
            "-B",
            "-c",
            r#"import sys
from pathlib import Path
root = Path(sys.argv[1])
sys.path.insert(0, str(root / 'scripts'))
from current_source_fixtures import current_source_file
print(current_source_file(Path(sys.argv[2])))
"#,
        ])
        .arg(env!("CARGO_MANIFEST_DIR"))
        .arg(path)
        .output()
        .expect("Python 3 is required for recorded fixture identity checks");
    assert!(
        output.status.success(),
        "source fixture selection failed for {}: {}",
        path.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    let selected = String::from_utf8(output.stdout).expect("fixture paths must be UTF-8");
    PathBuf::from(selected.trim_end_matches('\n'))
}

/// Read the current source only after checking every recorded migration link.
pub(super) fn current_source_text(relative: &str) -> String {
    let selected = current_namespace_fixture(&Path::new(env!("CARGO_MANIFEST_DIR")).join(relative));
    fs::read_to_string(selected).expect("current source fixture")
}

/// Select current corpus snapshots only for registered logical project roots.
pub(super) fn current_corpus_projects(paths: &[PathBuf]) -> Vec<PathBuf> {
    select_corpus_projects(paths, "positive")
}

/// Keep the complete rejection inventory separate from the positive corpus.
pub(super) fn current_corpus_counterexamples(paths: &[PathBuf]) -> Vec<PathBuf> {
    select_corpus_projects(paths, "negative")
}

fn select_corpus_projects(paths: &[PathBuf], kind: &str) -> Vec<PathBuf> {
    let output = Command::new("python3")
        .args([
            "-B",
            "-c",
            r#"import sys
from pathlib import Path
root = Path(sys.argv[1])
sys.path.insert(0, str(root / 'scripts'))
from check_input_corpus import check_manifest, current_negatives, current_project, local, require
corpus = root / 'corpus'
manifest = check_manifest(corpus)
kind = sys.argv[2]
require(kind in ('positive', 'negative'), 'unknown corpus inventory')
cases = manifest['cases'] if kind == 'positive' else current_negatives(corpus)
known = {local(corpus, case['project']): case for case in cases}
require(len(known) == len(cases), 'duplicate logical corpus project')
requested = [Path(path).resolve() for path in sys.argv[3:]]
require(len(set(requested)) == len(requested), 'duplicate requested corpus project')
require(set(requested) == set(known), 'logical corpus inventory differs from registered projects')
selected = []
for project in requested:
    require(project in known, 'unregistered logical corpus project: ' + str(project))
    selected.append(current_project(known[project], corpus))
require(len(set(selected)) == len(selected), 'duplicate selected corpus project')
for project in selected:
    print(project)
"#,
        ])
        .arg(env!("CARGO_MANIFEST_DIR"))
        .arg(kind)
        .args(paths)
        .output()
        .expect("Python 3 is required for recorded corpus identity checks");
    assert!(
        output.status.success(),
        "current corpus project selection failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let selected = String::from_utf8(output.stdout).expect("corpus paths must be UTF-8");
    let selected: Vec<_> = selected.lines().map(PathBuf::from).collect();
    assert_eq!(
        selected.len(),
        paths.len(),
        "missing current corpus project"
    );
    selected
}

pub(super) struct SourceRoot(pub(super) PathBuf);

impl SourceRoot {
    pub(super) fn new(source: &str) -> Self {
        let root = loop {
            let path = std::env::temp_dir().join(format!(
                "qleisli-test-{}-{}",
                std::process::id(),
                NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
            ));
            // Creation is atomic across test executables. Skip directories
            // left by earlier runs instead of reusing or deleting them.
            match fs::create_dir(&path) {
                Ok(()) => break Self(path),
                Err(error) if error.kind() == ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("cannot create {}: {error}", path.display()),
            }
        };
        // Own the directory before writing so a failed write still cleans up.
        root.write("Qargo.toml", include_str!("../Qargo.toml"));
        root.write("main.qli", source);
        root
    }

    pub(super) fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }
}

impl Drop for SourceRoot {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[allow(dead_code)]
pub(super) fn accept(
    raw: qleisli::ir::RawProgram,
) -> Result<qleisli::AcceptedProgram, qleisli::interchange::Error> {
    qleisli::interchange::native::Kernel::selected()?.accept_raw(raw)
}
