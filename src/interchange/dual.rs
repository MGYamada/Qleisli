//! Opt-in VM-28 intersection of Rust QIRF verification and a fresh native Lean
//! check. The selected executable must be built/audited from the matching
//! kernel sources. This adapter does not attest a binary or prove compilation,
//! decoding, source preservation or Rust execution. It never falls back.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

mod runtime;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::{Error, Imported, Result};
use crate::VerifiedProgram;

/// An explicitly selected native checker; no PATH search or runtime download.
#[derive(Clone, Debug)]
pub struct Kernel {
    executable: PathBuf,
}

/// Fresh dual acceptance bound to complete, immutable artifact/request bytes.
/// No constructor accepts a serialized success receipt. Execution uses the
/// program reconstructed from these exact bytes by the Rust importer.
#[derive(Debug)]
pub struct Checked {
    artifact: Arc<[u8]>,
    request: Option<Arc<[u8]>>,
    imported: Imported,
    native_exact_work: usize,
}

impl Kernel {
    pub fn new(executable: impl AsRef<Path>) -> Self {
        Self {
            executable: executable.as_ref().to_owned(),
        }
    }

    /// Both checkers must accept the same complete input. Either rejection,
    /// unsupported form, exhausted capacity or transport failure blocks use.
    /// A separate request is optional and checked independently on both sides.
    pub fn check(&self, artifact: &[u8], request: Option<&[u8]>) -> Result<Checked> {
        if artifact.is_empty()
            || artifact.len() > 16 << 20
            || request.is_some_and(|r| r.is_empty() || r.len() > 16 << 20)
        {
            return Err(Error::limit(
                "dual input must contain 1..16777216 bytes per file",
            ));
        }
        let artifact: Arc<[u8]> = Arc::from(artifact);
        let request: Option<Arc<[u8]>> = request.map(Arc::from);
        let imported = super::import(&artifact, request.as_deref())?;
        let mut packet =
            Vec::with_capacity(12 + artifact.len() + request.as_ref().map_or(0, |r| r.len()));
        packet.extend_from_slice(b"QLV1");
        packet.extend_from_slice(&(artifact.len() as u32).to_le_bytes());
        packet.extend_from_slice(&(request.as_ref().map_or(0, |r| r.len()) as u32).to_le_bytes());
        packet.extend_from_slice(&artifact);
        if let Some(request) = &request {
            packet.extend_from_slice(request);
        }
        let executable = std::fs::canonicalize(&self.executable)
            .map_err(|e| Error::new("io", format!("cannot resolve Lean dual checker: {e}")))?;
        let native_exact_work = runtime::check(&executable, packet, request.is_some())?;
        Ok(Checked {
            artifact,
            request,
            imported,
            native_exact_work,
        })
    }
}

impl Checked {
    pub fn artifact(&self) -> &[u8] {
        &self.artifact
    }
    pub fn request(&self) -> Option<&[u8]> {
        self.request.as_deref()
    }
    pub fn imported(&self) -> &Imported {
        &self.imported
    }
    pub fn program(&self) -> &VerifiedProgram {
        &self.imported.program
    }
    pub fn native_exact_work(&self) -> usize {
        self.native_exact_work
    }
    /// Consume the report, retaining the exact reconstructed executable body.
    pub fn into_program(self) -> VerifiedProgram {
        self.imported.program
    }
}
