//! Filesystem adapter only. The library importer never resolves source labels.
use super::options::Options;
use qleisli::frontend::compile::compile_project_with_policy;
use qleisli::frontend::diagnostic::Diagnostic;
use qleisli::interchange::{self, Version};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

pub(super) enum Failure {
    Source(Diagnostic),
    Artifact(interchange::Error),
}
impl From<Diagnostic> for Failure {
    fn from(error: Diagnostic) -> Self {
        Self::Source(error)
    }
}
impl From<interchange::Error> for Failure {
    fn from(error: interchange::Error) -> Self {
        Self::Artifact(error)
    }
}
fn io_error(error: impl std::fmt::Display) -> Failure {
    Failure::Source(Diagnostic {
        code: "project",
        message: error.to_string(),
        primary: None,
    })
}
fn read(path: &Path) -> Result<Vec<u8>, Failure> {
    if path.to_str().is_none() {
        return Err(io_error("artifact path is not valid UTF-8"));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(io_error)?
        .take((16 << 20) + 1)
        .read_to_end(&mut bytes)
        .map_err(io_error)?;
    if bytes.len() > 16 << 20 {
        return Err(interchange::Error {
            code: "limit",
            message: "artifact exceeds 16 MiB".into(),
            json_pointer: String::new(),
        }
        .into());
    }
    Ok(bytes)
}

/// No destination overwrite, including symlinks. The temporary file and
/// destination share one directory/filesystem; hard-link installation is atomic.
pub(super) fn write_new(path: &Path, bytes: &[u8]) -> Result<(), Failure> {
    static SERIAL: AtomicU64 = AtomicU64::new(0);
    struct Temporary(PathBuf);
    impl Drop for Temporary {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    for _ in 0..128 {
        let name = parent.join(format!(
            ".qleisli-ir-{}-{}.tmp",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        let mut file = match OpenOptions::new().write(true).create_new(true).open(&name) {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => return Err(io_error(e)),
        };
        let temporary = Temporary(name);
        file.write_all(bytes).map_err(io_error)?;
        file.sync_all().map_err(io_error)?;
        drop(file);
        fs::hard_link(&temporary.0, path).map_err(io_error)?;
        return Ok(());
    }
    Err(io_error(
        "could not exclusively create a temporary artifact sibling",
    ))
}

pub(super) enum Success {
    Emitted(String),
    Verified(bool),
}
pub(super) fn execute(options: &Options) -> Result<Success, Failure> {
    if options.command == "emit-ir" {
        let output = options.output.as_ref().expect("parsed output path");
        let label = output
            .to_str()
            .ok_or_else(|| io_error("output path is not valid UTF-8"))?;
        let program = compile_project_with_policy(&options.path, options.policy)?;
        let bytes = interchange::export(&program, None, Version::V2)?;
        write_new(output, &bytes)?;
        Ok(Success::Emitted(label.into()))
    } else {
        let bytes = read(&options.path)?;
        let request = options.against.as_deref().map(read).transpose()?;
        let imported = interchange::import(&bytes, request.as_deref())?;
        Ok(Success::Verified(imported.request_checked))
    }
}
