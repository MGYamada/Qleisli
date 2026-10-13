//! Bounded native process transport and strict response framing.
//! A decoded response proposes reconstruction obligations; it is not evidence.
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::{Error, Result};
use crate::interchange::native_packet::{self, Scope, View};

#[derive(Clone, Copy)]
pub(super) enum Mode {
    Inspect,
    Request,
    Fourier,
    Instrument,
    QpeInstrument,
}
impl Mode {
    fn description(self) -> &'static str {
        match self {
            Self::Inspect => "artifact inspection",
            Self::Request => "composition-request checking",
            Self::Fourier => "independent Fourier-request checking",
            Self::Instrument => "composition-instrument checking",
            Self::QpeInstrument => "named-QPE instrument checking",
        }
    }
    fn argument(self) -> &'static str {
        match self {
            Self::Inspect => "--hierarchy-pending",
            Self::Request => "--hierarchy-request-pending",
            Self::Fourier => "--hierarchy-fourier-pending",
            Self::Instrument => "--instrument-pending",
            Self::QpeInstrument => "--qpe-instrument-pending",
        }
    }
    fn header(self) -> &'static str {
        match self {
            Self::Inspect => "qleisli.hierarchy-pending 4",
            Self::Request => "qleisli.hierarchy-request-pending 4",
            Self::Fourier => "qleisli.hierarchy-fourier-pending 4",
            Self::Instrument => "qleisli.instrument-pending 4",
            Self::QpeInstrument => "qleisli.qpe-instrument-pending 4",
        }
    }
    fn maximum(self) -> usize {
        match self {
            Self::Inspect => 1_100_000,
            Self::Request | Self::Fourier | Self::Instrument | Self::QpeInstrument => 2_200_000,
        }
    }
}
pub(super) struct Response {
    pub(super) checker: PathBuf,
    pub(super) work: usize,
    pub(super) exact_work: usize,
    pub(super) indices: Vec<usize>,
    pub(super) pairs: Vec<usize>,
    pub(super) hadamards: Vec<usize>,
}

#[cfg(test)]
fn response_indices(bytes: &[u8], mode: Mode) -> Result<Response> {
    response_bound(bytes, mode, Scope::Inspection, Path::new(""))
}

fn response_bound(bytes: &[u8], mode: Mode, scope: Scope, checker: &Path) -> Result<Response> {
    // Main rejects a product-version mismatch before dispatching to a mode,
    // using the common failure frame. Only this exact failure is recognized;
    // a generic success frame never authorizes hierarchical reconstruction.
    if bytes == b"qleisli.qirf-native 2\nerror\nversion\n" {
        return Err(Error::new(
            "version",
            format!(
                "Lean {}: native checker product version does not match {}",
                mode.description(),
                env!("CARGO_PKG_VERSION")
            ),
        ));
    }
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid runtime response UTF-8"))?;
    let mut lines = text.split('\n');
    if lines.next() != Some(mode.header()) {
        return Err(Error::format("unknown runtime response"));
    }
    match lines.next() {
        Some("pending") => {}
        Some("error") => {
            let code = match lines.next() {
                Some("limit") => "limit",
                Some("contract") => "contract",
                Some("invalid_ir") => "invalid_ir",
                Some("format") => "format",
                Some("decoded_view") => "decoded_view",
                _ => return Err(Error::format("unknown runtime failure")),
            };
            if lines.next() != Some("") || lines.next().is_some() {
                return Err(Error::format("trailing runtime failure data"));
            }
            let detail = if code == "limit" {
                "a checking capacity was exceeded; aggregate structural-work allowance is 2000000 and shared exact-work allowance is 10000000; required work is unavailable in the native failure reply"
            } else {
                "the native checker rejected the artifact or request"
            };
            return Err(Error::new(
                code,
                format!("Lean {}: {detail}", mode.description()),
            ));
        }
        _ => return Err(Error::format("unknown runtime response status")),
    }
    if lines.next() != Some(scope.name()) {
        return Err(Error::format("native execution scope disagrees"));
    }
    let integer = |s: Option<&str>, maximum: usize| -> Result<usize> {
        let s = s.ok_or_else(|| Error::format("truncated runtime response"))?;
        if s.is_empty()
            || s.len() > 10
            || !s.bytes().all(|b| b.is_ascii_digit())
            || (s.len() > 1 && s.starts_with('0'))
        {
            return Err(Error::format("invalid runtime integer"));
        }
        let n = s
            .parse::<usize>()
            .map_err(|_| Error::limit("runtime integer overflow"))?;
        if n > maximum {
            return Err(Error::limit("runtime response exceeds its bound"));
        }
        Ok(n)
    };
    let work = integer(lines.next(), 2_000_000)?;
    let exact_work = integer(lines.next(), 10_000_000)?;
    let count = integer(lines.next(), 100_000)?;
    let indices = (0..count)
        .map(|_| integer(lines.next(), 99_999))
        .collect::<Result<_>>()?;
    let pairs = match mode {
        Mode::Inspect => Vec::new(),
        Mode::Request | Mode::Fourier | Mode::Instrument | Mode::QpeInstrument => {
            let count = integer(
                lines.next(),
                if matches!(mode, Mode::Fourier) {
                    8
                } else {
                    100_000
                },
            )?;
            (0..count)
                .map(|_| integer(lines.next(), 99_999))
                .collect::<Result<_>>()?
        }
    };
    let hadamards = if matches!(mode, Mode::QpeInstrument) {
        let count = integer(lines.next(), 16)?;
        (0..count)
            .map(|_| integer(lines.next(), 99_999))
            .collect::<Result<_>>()?
    } else {
        Vec::new()
    };
    if lines.next() != Some("") || lines.next().is_some() {
        return Err(Error::format("trailing runtime response data"));
    }
    Ok(Response {
        checker: checker.to_owned(),
        work,
        exact_work,
        indices,
        pairs,
        hadamards,
    })
}

pub(super) fn check(
    executable: &Path,
    bytes: Vec<u8>,
    mode: Mode,
    view: Option<&[u8]>,
) -> Result<Response> {
    let (bytes, scope) = native_packet::encode(
        &bytes,
        view.map(|graph| View {
            graph,
            caller: None,
        }),
    )?;
    let checker = std::fs::canonicalize(executable)
        .map_err(|error| Error::new("io", format!("cannot resolve Lean checker: {error}")))?;
    crate::interchange::process::invoke(
        &checker,
        bytes,
        mode.argument(),
        Duration::from_secs(60),
        mode.maximum(),
        |bytes| response_bound(bytes, mode, scope, &checker),
    )
}

#[cfg(test)]
mod response_diagnostics_tests {
    use super::{Mode, response_indices};

    #[test]
    fn isometry_hierarchy_version_failure_is_explicit_and_never_accepts_generic_frames() {
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            let error = response_indices(b"qleisli.qirf-native 2\nerror\nversion\n", mode)
                .err()
                .unwrap();
            assert_eq!(error.code, "version");
            assert!(
                error
                    .to_string()
                    .contains("native checker product version does not match")
            );
            for frame in [
                b"qleisli.qirf-native 2\nerror\nversion\nextra\n".as_slice(),
                b"qleisli.qirf-native 2\nerror\nversion".as_slice(),
                b"qleisli.qirf-native 2\nerror\ninvalid_ir\n".as_slice(),
                b"qleisli.qirf-native 2\nok\n".as_slice(),
                b"qleisli.qirf-native 1\nerror\nversion\n".as_slice(),
            ] {
                assert_eq!(response_indices(frame, mode).err().unwrap().code, "format");
            }
        }
    }

    #[test]
    fn native_v4_requires_bounded_exact_work_and_rejects_legacy_acceptance() {
        for mode in [
            Mode::Inspect,
            Mode::Fourier,
            Mode::Request,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            let suffix = if matches!(mode, Mode::QpeInstrument) {
                "0\n"
            } else {
                ""
            };
            let pairs = if matches!(mode, Mode::Inspect) {
                ""
            } else {
                "0\n"
            };
            let valid = format!(
                "{}\npending\ninspection\n12\n36\n0\n{pairs}{suffix}",
                mode.header()
            );
            let response = response_indices(valid.as_bytes(), mode).unwrap();
            assert_eq!(response.work, 12);
            assert_eq!(response.exact_work, 36);
            for malformed in [
                valid.replacen("pending 4", "pending 1", 1),
                valid.replacen("pending 4", "pending 2", 1),
                valid.replacen("pending 4", "pending 3", 1),
                valid.replacen("inspection", "execution", 1),
                valid.replacen("\n36\n", "\n10000001\n", 1),
                valid.replacen("\n36\n", "\n036\n", 1),
                format!("{valid}extra\n"),
            ] {
                assert!(response_indices(malformed.as_bytes(), mode).is_err());
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn nonzero_runtime_exit_preserves_framing_errors_and_checker_rejections() {
        // Never rewrite an executable while parallel tests can spawn children:
        // inherited write descriptors can cause Linux ETXTBSY even after the
        // parent's write has closed. This immutable fixture varies via stdin.
        let executable = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v030/execution-view-binding/framing-rejection.sh");
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            for (case, expected) in [
                ("complete", "contract"),
                ("extra", "format"),
                ("missing-newline", "format"),
            ] {
                let error = crate::interchange::process::invoke(
                    &executable,
                    format!("{case}\n").into_bytes(),
                    mode.argument(),
                    std::time::Duration::from_secs(5),
                    mode.maximum(),
                    |bytes| response_indices(bytes, mode),
                )
                .err()
                .unwrap();
                assert_eq!(error.code, expected, "{}", error.message);
            }
        }
    }

    #[test]
    fn every_failure_mode_requires_exact_eof_after_the_final_newline() {
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            for code in ["limit", "contract", "invalid_ir", "format"] {
                let reply = format!("{}\nerror\n{code}\n", mode.header());
                assert_eq!(
                    response_indices(reply.as_bytes(), mode).err().unwrap().code,
                    code
                );
                for malformed in [
                    reply.trim_end().to_owned(),
                    format!("{reply}extra\n"),
                    format!("{reply}x"),
                    format!("{reply}\n"),
                ] {
                    let error = response_indices(malformed.as_bytes(), mode).err().unwrap();
                    assert_eq!(error.code, "format");
                    assert!(
                        error.message.contains("runtime failure data"),
                        "{}",
                        error.message
                    );
                }
            }
        }
    }

    #[test]
    fn framed_obligations_remain_mode_specific_and_reject_malformed_counts() {
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            let pairs = if matches!(mode, Mode::Inspect) {
                ""
            } else {
                "1\n7\n"
            };
            let hadamards = if matches!(mode, Mode::QpeInstrument) {
                "1\n3\n"
            } else {
                ""
            };
            let reply = format!(
                "{}\npending\ninspection\n42\n{}2\n0\n9\n{pairs}{hadamards}",
                mode.header(),
                "36\n"
            );
            let response = response_indices(reply.as_bytes(), mode).unwrap();
            assert_eq!(response.work, 42);
            assert_eq!(response.indices, [0, 9]);
            assert_eq!(
                response.pairs,
                if pairs.is_empty() { vec![] } else { vec![7] }
            );
            assert_eq!(
                response.hadamards,
                if hadamards.is_empty() {
                    vec![]
                } else {
                    vec![3]
                }
            );
            for bad in [
                reply.trim_end().to_owned(),
                format!("{reply}extra\n"),
                reply.replacen("\n42\n", "\n042\n", 1),
                reply.replacen("\n42\n", "\n2000001\n", 1),
            ] {
                assert!(response_indices(bad.as_bytes(), mode).is_err());
            }
        }
    }

    #[test]
    fn capacity_failure_identifies_the_selected_native_check_without_a_work_claim() {
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            let reply = format!("{}\nerror\nlimit\n", mode.header());
            let error = match response_indices(reply.as_bytes(), mode) {
                Err(error) => error,
                Ok(_) => panic!("capacity rejection must not produce a check report"),
            };
            assert_eq!(error.code, "limit");
            assert!(error.message.contains(mode.description()));
            assert!(error.message.contains("2000000"));
            assert!(error.message.contains("required work is unavailable"));
        }
        let reply = b"qleisli.qpe-instrument-pending 4\nerror\ncontract\n";
        let error = response_indices(reply, Mode::QpeInstrument).err().unwrap();
        assert_eq!(error.code, "contract");
        assert!(!error.message.contains("capacity"));
    }
}

#[cfg(all(test, unix))]
mod checker_path_tests {
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    use crate::interchange::{hierarchical::Kernel, json};

    #[test]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    fn all_native_modes_retain_invoked_canonical_paths_after_alias_and_target_moves() {
        use std::os::unix::fs::symlink;
        static SERIAL: AtomicU64 = AtomicU64::new(0);
        let original = std::fs::canonicalize(std::env::var_os("QLEISLI_KERNEL").unwrap()).unwrap();
        let directory = std::env::temp_dir().join(format!(
            "qleisli-hierarchy-checker-path-{}-{}",
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
        let other = directory.join("other-checker");
        if std::fs::hard_link(&original, &other).is_err() {
            std::fs::copy(&original, &other).unwrap();
        }
        let other = std::fs::canonicalize(other).unwrap();
        let alias = directory.join("checker-alias");
        symlink(&original, &alias).unwrap();
        let kernel = Kernel::new(&alias);
        let inputs = json::parse(include_bytes!(
            "../../../tests/fixtures/verification_v030/execution-view-binding/hierarchy-mode-inputs.json"
        ))
        .unwrap();
        let mut reports = Vec::new();
        for row in inputs.field("rows").unwrap().array().unwrap() {
            if !row.field("accept").unwrap().boolean().unwrap() {
                continue;
            }
            let payload = json::encode(row.field("artifact").unwrap()).unwrap();
            let request = row.field("request").ok().map(|r| json::encode(r).unwrap());
            let candidate = row
                .field("candidate")
                .ok()
                .map(|r| json::encode(r).unwrap());
            let report = match row.field("mode").unwrap().text().unwrap() {
                "inspect" => kernel.inspect_native(&payload),
                "request" | "fourier" => {
                    kernel.check_against_native(&payload, request.as_deref().unwrap())
                }
                "instrument" => {
                    kernel.check_instrument_native(&payload, request.as_deref().unwrap())
                }
                "qpeInstrument" => kernel.check_qpe_instrument_native(
                    &payload,
                    request.as_deref().unwrap(),
                    candidate.as_deref().unwrap(),
                ),
                mode => panic!("unexpected mode {mode}"),
            }
            .unwrap();
            assert_eq!(report.request(), request.as_deref());
            assert_eq!(report.candidate(), candidate.as_deref());
            assert_eq!(
                report.checker(),
                if reports.is_empty() {
                    &original
                } else {
                    &other
                }
            );
            reports.push(report);
            if reports.len() == 1 {
                std::fs::remove_file(&alias).unwrap();
                symlink(&other, &alias).unwrap();
            }
        }
        assert_eq!(reports.len(), 5);
        std::fs::remove_file(&alias).unwrap();
        std::fs::rename(&other, directory.join("moved-checker")).unwrap();
        assert_eq!(reports[0].checker(), original);
        for report in &reports[1..] {
            assert_eq!(report.checker(), other);
            assert!(!report.checker().exists());
        }
    }
}
