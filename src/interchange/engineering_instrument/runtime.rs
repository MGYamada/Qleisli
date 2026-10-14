//! Strict engineering-only process response; exact acceptance is a different protocol.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use std::path::Path;
use std::time::Duration;

use super::{Error, Result};

fn response(bytes: &[u8]) -> Result<usize> {
    let text = std::str::from_utf8(bytes)
        .map_err(|_| Error::format("invalid engineering response UTF-8"))?;
    let lines: Vec<_> = text.split('\n').collect();
    if lines.first() != Some(&"qleisli.engineering-instrument-native 1") {
        return Err(Error::format("unknown engineering response protocol"));
    }
    match lines.as_slice() {
        [_, "error", code, ""] => {
            let code = match *code {
                "limit" => "limit",
                "contract" => "contract",
                "invalid_ir" => "invalid_ir",
                "format" => "format",
                "decoded_view" => "decoded_view",
                "version" => "kernel",
                _ => return Err(Error::format("unknown engineering rejection")),
            };
            Err(Error::new(
                code,
                if code == "kernel" {
                    "native checker product version differs from the Rust package"
                } else {
                    "Lean engineering checker rejected the artifact/request; no fallback"
                },
            ))
        }
        [_, "engineering-checked", "execution", work, ""] => {
            if work.is_empty()
                || work.len() > 8
                || !work.bytes().all(|b| b.is_ascii_digit())
                || work.len() > 1 && work.starts_with('0')
            {
                return Err(Error::format("noncanonical engineering work count"));
            }
            let work: usize = work
                .parse()
                .map_err(|_| Error::format("invalid engineering work count"))?;
            if work > crate::contract::DEFAULT_EXACT_WORK {
                return Err(Error::format("engineering work bound disagrees"));
            }
            Ok(work)
        }
        _ => Err(Error::format("malformed/trailing engineering response")),
    }
}

pub(super) fn check(executable: &Path, packet: Vec<u8>) -> Result<usize> {
    invoke(executable, packet, Duration::from_secs(60))
}

fn invoke(executable: &Path, packet: Vec<u8>, timeout: Duration) -> Result<usize> {
    crate::interchange::process::invoke(
        executable,
        packet,
        "--qirf-engineering-instrument-native",
        timeout,
        256,
        response,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engineering_reply_is_strict_and_separate_from_exact_acceptance() {
        let good = "qleisli.engineering-instrument-native 1\nengineering-checked\nexecution\n42\n";
        assert_eq!(response(good.as_bytes()).unwrap(), 42);
        for bad in [
            good.replace("native 1", "native 2"),
            good.replace("engineering-checked", "accepted"),
            good.replace("execution", "inspection"),
            good.replace("execution", "caller"),
            good.replace("42", "042"),
            good.replace("42", "10000001"),
            good.trim_end().to_owned(),
            format!("{good}\n"),
            format!("{good}extra"),
            "qleisli.qirf-native 2\naccepted\nexecution\n42\n1\n".into(),
            "qleisli.qirf-native 1\naccepted\n42\n1\n".into(),
            "qleisli.engineering-pure-native 1\nengineering-checked\nexecution\n42\n".into(),
            "qleisli.engineering-instrument-native 1\nerror\nunknown\n".into(),
        ] {
            assert!(response(bad.as_bytes()).is_err(), "{bad}");
        }
        assert_eq!(
            response(b"qleisli.engineering-instrument-native 1\nerror\ncontract\n")
                .unwrap_err()
                .code,
            "contract"
        );
        assert_eq!(
            response(b"qleisli.engineering-instrument-native 1\nerror\nversion\n")
                .unwrap_err()
                .code,
            "kernel"
        );
    }

    #[test]
    #[cfg(unix)]
    fn incompatible_missing_failed_and_timed_out_checkers_never_fall_back() {
        use std::os::unix::fs::symlink;
        use std::time::{Instant, SystemTime, UNIX_EPOCH};
        let directory = std::env::temp_dir().join(format!(
            "qleisli-engineering-process-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v030/execution-view-binding/process-failure.sh");
        for (case, expected) in [
            ("failed-acceptance", "format"),
            ("contract", "format"),
            ("large-output", "limit"),
            ("sleep", "limit"),
            ("inherited-pipe", "limit"),
            ("empty", "format"),
        ] {
            let executable = directory.join(case);
            symlink(&fixture, &executable).unwrap();
            let start = Instant::now();
            assert_eq!(
                invoke(&executable, vec![0; 4096], Duration::from_secs(1))
                    .unwrap_err()
                    .code,
                expected,
                "{case}"
            );
            assert!(start.elapsed() < Duration::from_secs(2));
        }
        assert_eq!(
            invoke(
                &directory.join("missing"),
                vec![],
                Duration::from_millis(100)
            )
            .unwrap_err()
            .code,
            "io"
        );
    }
}
