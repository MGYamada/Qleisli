//! Strict engineering-only process response; exact acceptance is a different protocol.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use std::path::Path;
use std::time::Duration;

use super::Result;

#[cfg(test)]
fn response(bytes: &[u8]) -> Result<usize> {
    crate::interchange::native_context::engineering_response(
        bytes,
        crate::edition::Edition::E2026,
        crate::interchange::native_context::Mode::EngineeringPure,
    )
    .map(|value| value.exact_work)
}

pub(super) fn check(
    executable: &Path,
    packet: Vec<u8>,
    edition: crate::edition::Edition,
) -> Result<crate::interchange::native_context::WorkDecision> {
    invoke_bound(executable, packet, Duration::from_secs(60), edition)
}

#[cfg(test)]
fn invoke(executable: &Path, packet: Vec<u8>, timeout: Duration) -> Result<usize> {
    invoke_bound(executable, packet, timeout, crate::edition::Edition::E2026)
        .map(|value| value.exact_work)
}

fn invoke_bound(
    executable: &Path,
    packet: Vec<u8>,
    timeout: Duration,
    edition: crate::edition::Edition,
) -> Result<crate::interchange::native_context::WorkDecision> {
    let mode = crate::interchange::native_context::Mode::EngineeringPure;
    crate::interchange::process::invoke(
        executable,
        packet,
        mode.argument(),
        timeout,
        256,
        |bytes| crate::interchange::native_context::engineering_response(bytes, edition, mode),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn engineering_reply_is_strict_and_separate_from_exact_acceptance() {
        let good = format!(
            "qleisli.native-result 3
engineering-checked
2026
{}
--engineering-pure-check
execution
42
",
            env!("CARGO_PKG_VERSION")
        );
        assert_eq!(response(good.as_bytes()).unwrap(), 42);
        for bad in [
            good.replace("result 3", "result 2"),
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
            "qleisli.native-result 3\nerror\nunknown\n".into(),
        ] {
            assert!(response(bad.as_bytes()).is_err(), "{bad}");
        }
        assert_eq!(
            response(b"qleisli.native-result 3\nerror\ncontract\n")
                .unwrap_err()
                .code,
            "contract"
        );
        assert_eq!(
            response(b"qleisli.native-result 3\nerror\nversion\n")
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
            .join("tests/fixtures/verification_v030/native-edition-context/process-failure.sh");
        for (case, expected) in [
            ("failed-acceptance", "format"),
            ("contract", "contract"),
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
