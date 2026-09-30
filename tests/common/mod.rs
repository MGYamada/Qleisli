//! Temporary source projects shared by integration tests.

use std::fs;
use std::io::ErrorKind;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

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
