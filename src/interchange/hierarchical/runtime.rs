//! Bounded native process transport and strict response framing.
//! A decoded response proposes reconstruction obligations; it is not evidence.
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

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
            Self::Inspect => "qleisli.hierarchy-pending 1",
            Self::Request => "qleisli.hierarchy-request-pending 1",
            Self::Fourier => "qleisli.hierarchy-fourier-pending 1",
            Self::Instrument => "qleisli.instrument-pending 1",
            Self::QpeInstrument => "qleisli.qpe-instrument-pending 1",
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
            if matches!(mode, Mode::QpeInstrument)
                && (lines.next() != Some("") || lines.next().is_some())
            {
                return Err(Error::format("trailing QPE runtime failure data"));
            }
            let detail = if code == "limit" {
                "a checking capacity was exceeded; aggregate structural-work allowance is 2000000; required work is unavailable in the native failure reply"
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
        indices,
        pairs,
        hadamards,
    })
}

pub(super) fn check(executable: &Path, bytes: Vec<u8>, mode: Mode) -> Result<Response> {
    response_indices(&invoke(executable, bytes, mode)?, mode)
}

fn invoke(executable: &Path, bytes: Vec<u8>, mode: Mode) -> Result<Vec<u8>> {
    let mut child = Command::new(executable)
        .arg(mode.argument())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| Error::new("io", format!("cannot start Lean runtime: {e}")))?;
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let writer = std::thread::spawn(move || stdin.write_all(&bytes));
    let reader = std::thread::spawn(move || {
        let mut output = Vec::new();
        stdout
            .take((mode.maximum() + 1) as u64)
            .read_to_end(&mut output)
            .map(|_| output)
    });
    let deadline = Instant::now() + Duration::from_secs(60);
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) if Instant::now() < deadline => std::thread::sleep(Duration::from_millis(10)),
            Ok(None) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(Error::limit("Lean runtime inspection timed out"));
            }
            Err(e) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(Error::new("io", format!("Lean runtime wait failed: {e}")));
            }
        }
    };
    let written = writer
        .join()
        .map_err(|_| Error::new("io", "runtime input thread failed"))?;
    let output = reader
        .join()
        .map_err(|_| Error::new("io", "runtime output thread failed"))?
        .map_err(|e| Error::new("io", format!("runtime output failed: {e}")))?;
    let status = status?;
    if output.len() > mode.maximum() {
        return Err(Error::limit("runtime response exceeds limit"));
    }
    if !status.success() {
        return match response_indices(&output, mode) {
            Err(error) => Err(error),
            Ok(_) => Err(Error::new("io", "failed runtime returned success data")),
        };
    }
    written.map_err(|e| Error::new("io", format!("runtime input failed: {e}")))?;
    Ok(output)
}

#[cfg(test)]
mod response_diagnostics_tests {
    use super::{Mode, response_indices};

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
                "{}\npending\n42\n2\n0\n9\n{pairs}{hadamards}",
                mode.header()
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
        let reply = b"qleisli.qpe-instrument-pending 1\nerror\ncontract\n";
        let error = response_indices(reply, Mode::QpeInstrument).err().unwrap();
        assert_eq!(error.code, "contract");
        assert!(!error.message.contains("capacity"));
    }
}
