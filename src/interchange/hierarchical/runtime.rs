//! Bounded native process transport and strict response framing.
//! A decoded response proposes reconstruction obligations; it is not evidence.
use std::path::Path;
use std::time::Duration;

use super::{Error, Result};

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
            Self::Inspect => "qleisli.hierarchy-pending 3",
            Self::Request => "qleisli.hierarchy-request-pending 3",
            Self::Fourier => "qleisli.hierarchy-fourier-pending 3",
            Self::Instrument => "qleisli.instrument-pending 3",
            Self::QpeInstrument => "qleisli.qpe-instrument-pending 3",
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
    pub(super) work: usize,
    pub(super) exact_work: usize,
    pub(super) indices: Vec<usize>,
    pub(super) pairs: Vec<usize>,
    pub(super) hadamards: Vec<usize>,
}

fn response_indices(bytes: &[u8], mode: Mode) -> Result<Response> {
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
        work,
        exact_work,
        indices,
        pairs,
        hadamards,
    })
}

pub(super) fn check(executable: &Path, bytes: Vec<u8>, mode: Mode) -> Result<Response> {
    crate::interchange::process::invoke(
        executable,
        bytes,
        mode.argument(),
        Duration::from_secs(60),
        mode.maximum(),
        |bytes| response_indices(bytes, mode),
    )
}

#[cfg(test)]
mod response_diagnostics_tests {
    use super::{Mode, response_indices};

    #[test]
    fn native_v3_requires_bounded_exact_work_and_rejects_legacy_acceptance() {
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
            let valid = format!("{}\npending\n12\n36\n0\n{pairs}{suffix}", mode.header());
            let response = response_indices(valid.as_bytes(), mode).unwrap();
            assert_eq!(response.work, 12);
            assert_eq!(response.exact_work, 36);
            for malformed in [
                valid.replacen("pending 3", "pending 1", 1),
                valid.replacen("pending 3", "pending 2", 1),
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
        use std::{
            fs,
            os::unix::fs::PermissionsExt,
            time::{SystemTime, UNIX_EPOCH},
        };
        let directory = std::env::temp_dir().join(format!(
            "qleisli-runtime-frame-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let executable = directory.join("checker");
        for mode in [
            Mode::Inspect,
            Mode::Request,
            Mode::Fourier,
            Mode::Instrument,
            Mode::QpeInstrument,
        ] {
            let good = format!("{}\nerror\ncontract\n", mode.header());
            for (reply, expected) in [
                (good.clone(), "contract"),
                (format!("{good}extra\n"), "format"),
                (good.trim_end().to_owned(), "format"),
            ] {
                fs::write(
                    &executable,
                    format!("#!/bin/sh\nprintf '%s' '{reply}'\nexit 1\n"),
                )
                .unwrap();
                fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
                let error = super::check(&executable, vec![], mode).err().unwrap();
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
                "{}\npending\n42\n{}2\n0\n9\n{pairs}{hadamards}",
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
        let reply = b"qleisli.qpe-instrument-pending 3\nerror\ncontract\n";
        let error = response_indices(reply, Mode::QpeInstrument).err().unwrap();
        assert_eq!(error.code, "contract");
        assert!(!error.message.contains("capacity"));
    }
}
