//! Bounded diagnostic observations of successful native invocations.
//! These counts and paths confer no acceptance authority or binary identity.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::interchange::native_packet::Scope;

const MAX_CHECKER_PATHS: usize = 1_024;
const MAX_CHECKER_PATH_BYTES: usize = 1 << 20;

/// Immutable diagnostic snapshot of actual successful finite-native decisions.
/// A path names the executable used for an invocation; it does not attest its
/// bytes. Counts include repeated decisions and separate contract requests,
/// and do not describe the enclosing source entry's request or meaning.
/// This snapshot cannot be supplied as acceptance evidence.
#[derive(Clone, Debug)]
pub struct NativeDecisionSummary {
    // Each checker has fixed ordinary/contract/carrier/ordinary-result/qmatch modes
    // x request-absent/present counters, without retaining artifacts or requests.
    checkers: BTreeMap<PathBuf, [[[usize; 2]; 3]; 5]>,
    path_bytes: usize,
    decisions: usize,
    requests_checked: usize,
    complete: bool,
}

impl NativeDecisionSummary {
    fn new() -> Self {
        Self {
            checkers: BTreeMap::new(),
            path_bytes: 0,
            decisions: 0,
            requests_checked: 0,
            complete: true,
        }
    }

    /// Distinct canonical paths captured from the actual invocation subjects.
    /// No path is resolved again while reading this snapshot.
    pub fn checker_paths(&self) -> impl ExactSizeIterator<Item = &Path> {
        self.checkers.keys().map(PathBuf::as_path)
    }

    pub fn decisions(&self) -> usize {
        self.decisions
    }

    /// Number of successful invocations with a separate native request.
    /// This does not make any request-less enclosing root request-checked.
    pub fn requests_checked(&self) -> usize {
        self.requests_checked
    }

    /// False if a diagnostic capacity was reached. Native decisions themselves
    /// are unchanged, but the snapshot must not be reported as exhaustive.
    pub fn complete(&self) -> bool {
        self.complete
    }

    fn record(&mut self, checker: &Path, mode: &str, requested: bool, scope: Scope) {
        self.decisions = increment(self.decisions, &mut self.complete);
        if requested {
            self.requests_checked = increment(self.requests_checked, &mut self.complete);
        }
        let mode = match mode {
            "--qirf-native" => 0,
            "--qirf-contract" => 1,
            "--carrier-pure-check" => 2,
            "--ordinary-root-check" => 3,
            "--qmatch-source-check" => 4,
            _ => {
                self.complete = false;
                return;
            }
        };
        let scope = scope as usize;
        if !self.checkers.contains_key(checker) {
            let bytes = checker.as_os_str().len();
            if self.checkers.len() == MAX_CHECKER_PATHS
                || bytes > MAX_CHECKER_PATH_BYTES.saturating_sub(self.path_bytes)
            {
                self.complete = false;
                return;
            }
            self.path_bytes += bytes;
            self.checkers.insert(checker.to_owned(), [[[0; 2]; 3]; 5]);
        }
        let count = &mut self
            .checkers
            .get_mut(checker)
            .expect("recorded checker path")[mode][scope][usize::from(requested)];
        *count = increment(*count, &mut self.complete);
    }
}

fn increment(value: usize, complete: &mut bool) -> usize {
    value.checked_add(1).unwrap_or_else(|| {
        *complete = false;
        usize::MAX
    })
}

/// A scoped observer shared by kernel clones and kernels reconstructed from
/// their accepted programs. Private construction prevents receipt injection.
#[derive(Clone, Debug)]
pub(crate) struct DecisionLog(Arc<Mutex<NativeDecisionSummary>>);

impl DecisionLog {
    pub(super) fn new() -> Self {
        Self(Arc::new(Mutex::new(NativeDecisionSummary::new())))
    }

    pub(crate) fn summary(&self) -> NativeDecisionSummary {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
    }

    pub(super) fn record(&self, checker: &Path, mode: &str, requested: bool, scope: Scope) {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .record(checker, mode, requested, scope);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interchange::native::Kernel;

    #[test]
    fn snapshots_keep_paths_modes_scopes_and_request_counts_separate() {
        let log = DecisionLog::new();
        let a = Path::new("/checker/a");
        let b = Path::new("/checker/b");
        log.record(a, "--qirf-native", false, Scope::Inspection);
        let before = log.summary();
        log.record(a, "--qirf-native", true, Scope::Execution);
        log.record(b, "--qirf-contract", true, Scope::Caller);
        let after = log.summary();
        assert_eq!(before.decisions(), 1);
        assert_eq!(before.requests_checked(), 0);
        assert_eq!(after.decisions(), 3);
        assert_eq!(after.requests_checked(), 2);
        assert_eq!(after.checker_paths().collect::<Vec<_>>(), [a, b]);
        assert_eq!(after.checkers[a][0][0][0], 1);
        assert_eq!(after.checkers[a][0][1][1], 1);
        assert_eq!(after.checkers[b][1][2][1], 1);
        assert!(after.complete());
    }

    #[test]
    fn capacity_limits_never_claim_an_exhaustive_snapshot() {
        let mut report = NativeDecisionSummary::new();
        for index in 0..MAX_CHECKER_PATHS {
            report.record(
                &PathBuf::from(format!("/checker/{index}")),
                "--qirf-native",
                false,
                Scope::Execution,
            );
        }
        assert!(report.complete());
        report.record(
            Path::new("/checker/excess"),
            "--qirf-native",
            true,
            Scope::Execution,
        );
        assert!(!report.complete());
        assert_eq!(report.checker_paths().len(), MAX_CHECKER_PATHS);
        assert_eq!(report.decisions(), MAX_CHECKER_PATHS + 1);
        assert_eq!(report.requests_checked(), 1);
        let mut report = NativeDecisionSummary::new();
        report.record(
            Path::new(&"x".repeat(MAX_CHECKER_PATH_BYTES + 1)),
            "--qirf-native",
            false,
            Scope::Inspection,
        );
        assert!(!report.complete());
        assert_eq!(report.checker_paths().len(), 0);
        let mut report = NativeDecisionSummary::new();
        report.decisions = usize::MAX;
        report.record(
            Path::new("/checker/a"),
            "--qirf-native",
            false,
            Scope::Inspection,
        );
        assert!(!report.complete());
        assert_eq!(report.decisions(), usize::MAX);
    }

    const ARTIFACT: &[u8] =
        include_bytes!("../../../tests/fixtures/verification_v022/finite/t.v2.qirf");
    const REQUEST: &[u8] = br#"{"format":"qleisli.request","version":1,"signature":{"tag":"bit"},"meaning":{"tag":"phase8","table":[0,1]},"source_snapshot":null}"#;

    #[test]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn successful_invocations_include_cloned_and_reconstructed_kernels_only_in_their_scope() {
        let selected = Kernel::selected(crate::edition::Edition::E2026).unwrap();
        let (kernel, log) = selected.recording();
        let (separate, separate_log) = kernel.recording();
        let program = kernel.check(ARTIFACT, None).unwrap().into_program();
        let clone = kernel.clone();
        clone.inspect(ARTIFACT, Some(REQUEST)).unwrap();
        program.kernel().check_program(&program).unwrap();
        let mut budget = crate::contract::exact::Budget::new(crate::contract::DEFAULT_EXACT_WORK);
        let meaning = crate::contract::meaning::FiniteMeaning::phase(
            crate::contract::BasisType::Bit,
            vec![0, 1],
        )
        .unwrap()
        .matrix(&mut budget)
        .unwrap();
        let boundary = crate::interchange::finite_leaf::UnitaryBoundary::new(
            crate::contract::BasisType::Bit,
            program.raw().quantum_inputs[0].clone(),
            program.output_ports()[0].clone(),
        )
        .unwrap();
        clone.check_leaf(ARTIFACT, &boundary, &meaning).unwrap();
        // A malformed proposal, a native request rejection and a missing
        // executable cannot be counted as successful native decisions.
        assert!(clone.inspect(b"invalid", None).is_err());
        let wrong = std::str::from_utf8(REQUEST)
            .unwrap()
            .replace("[0,1]", "[0,4]");
        assert!(clone.inspect(ARTIFACT, Some(wrong.as_bytes())).is_err());
        let missing = Kernel {
            edition: selected.edition(),
            executable: PathBuf::from("/nonexistent/qleisli-observer-checker"),
            decisions: Some(log.clone()),
        };
        assert!(missing.inspect(ARTIFACT, None).is_err());
        // The original unobserved kernel and a newly scoped observer do not
        // contribute to the first operation's diagnostic snapshot.
        selected.inspect(ARTIFACT, None).unwrap();
        separate.inspect(ARTIFACT, None).unwrap();
        let summary = log.summary();
        assert!(summary.complete());
        assert_eq!(summary.decisions(), 4);
        assert_eq!(summary.requests_checked(), 2);
        assert_eq!(
            summary.checker_paths().collect::<Vec<_>>(),
            [program.checker()]
        );
        assert_eq!(separate_log.summary().decisions(), 1);
        assert_eq!(separate_log.summary().requests_checked(), 0);
        assert_eq!(summary.checkers[program.checker()][1][1][1], 1);
        // Merely retaining an observer snapshot never adds an entry request.
        assert!(program.request().is_none());
    }

    #[test]
    #[cfg(unix)]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn actual_invocation_paths_survive_selection_symlink_changes() {
        use std::os::unix::fs::symlink;
        use std::sync::atomic::{AtomicU64, Ordering};
        static SERIAL: AtomicU64 = AtomicU64::new(0);
        let selected = std::env::var_os("QLEISLI_KERNEL").unwrap();
        let selected = std::fs::canonicalize(selected).unwrap();
        let directory = std::env::temp_dir().join(format!(
            "qleisli-decision-observer-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let a = directory.join("checker-a");
        let b = directory.join("checker-b");
        for path in [&a, &b] {
            if std::fs::hard_link(&selected, path).is_err() {
                std::fs::copy(&selected, path).unwrap();
            }
        }
        let a = std::fs::canonicalize(a).unwrap();
        let b = std::fs::canonicalize(b).unwrap();
        let link = directory.join("selected");
        symlink(&a, &link).unwrap();
        let (kernel, log) = Kernel::new(&link, crate::edition::Edition::E2026).recording();
        let program = kernel.check(ARTIFACT, None).unwrap().into_program();
        assert_eq!(program.checker(), a);
        std::fs::remove_file(&link).unwrap();
        symlink(&b, &link).unwrap();
        kernel.clone().inspect(ARTIFACT, Some(REQUEST)).unwrap();
        // A kernel reconstructed from an earlier accepted program retains its
        // own canonical target, while sharing the diagnostic observer.
        program.kernel().inspect(ARTIFACT, None).unwrap();
        std::fs::remove_file(&link).unwrap();
        let summary = log.summary();
        assert!(summary.complete());
        assert_eq!(summary.decisions(), 3);
        assert_eq!(summary.requests_checked(), 1);
        assert_eq!(summary.checker_paths().collect::<Vec<_>>(), [&*a, &*b]);
    }
}
