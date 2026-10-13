//! Bounded process IO. A process status and a strictly framed reply must agree.
use std::path::Path;
#[cfg(test)]
use std::time::{Duration, Instant};

use super::{Error, Result};
use crate::interchange::native_packet::Scope;
use crate::interchange::process::TransportLimits;

pub(super) const REJECTION_MESSAGE: &str =
    "Lean native checker rejected the artifact/request; no fallback";

#[cfg(test)]
fn response(bytes: &[u8], requested: bool) -> Result<usize> {
    response_bound(bytes, requested, Scope::Inspection)
}

fn response_bound(bytes: &[u8], requested: bool, scope: Scope) -> Result<usize> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid native response UTF-8"))?;
    let lines: Vec<_> = text.split('\n').collect();
    if lines.first() != Some(&"qleisli.qirf-native 2") {
        return Err(Error::format("unknown native response protocol"));
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
                _ => return Err(Error::format("unknown native rejection")),
            };
            Err(Error::new(
                code,
                if code == "kernel" {
                    "native checker product version differs from the Rust package"
                } else {
                    REJECTION_MESSAGE
                },
            ))
        }
        [_, "accepted", checked_scope, work, flag, ""] => {
            if *checked_scope != scope.name() {
                return Err(Error::format("native execution scope disagrees"));
            }
            if work.is_empty()
                || work.len() > 8
                || !work.bytes().all(|b| b.is_ascii_digit())
                || work.len() > 1 && work.starts_with('0')
            {
                return Err(Error::format("noncanonical native work count"));
            }
            let work: usize = work
                .parse()
                .map_err(|_| Error::format("invalid native work count"))?;
            if work > 10_000_000 || *flag != if requested { "1" } else { "0" } {
                return Err(Error::format(
                    "native work bound or request coverage disagrees",
                ));
            }
            Ok(work)
        }
        _ => Err(Error::format("malformed/trailing native response")),
    }
}

pub(super) fn check_mode(
    executable: &Path,
    packet: Vec<u8>,
    requested: bool,
    mode: &str,
    scope: Scope,
) -> Result<usize> {
    invoke_mode(
        executable,
        packet,
        requested,
        TransportLimits::FINITE,
        mode,
        scope,
    )
}
#[cfg(test)]
fn invoke(executable: &Path, packet: Vec<u8>, requested: bool, timeout: Duration) -> Result<usize> {
    invoke_mode(
        executable,
        packet,
        requested,
        TransportLimits::FINITE.with_timeout(timeout),
        "--qirf-native",
        Scope::Inspection,
    )
}
fn invoke_mode(
    executable: &Path,
    packet: Vec<u8>,
    requested: bool,
    limits: TransportLimits,
    mode: &str,
    scope: Scope,
) -> Result<usize> {
    limits.invoke(executable, packet, mode, |bytes| {
        response_bound(bytes, requested, scope)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replies_bind_request_presence_and_reject_ambiguous_success() {
        let good = "qleisli.qirf-native 2\naccepted\ninspection\n42\n0\n";
        assert_eq!(response(good.as_bytes(), false).unwrap(), 42);
        assert!(response(good.as_bytes(), true).is_err());
        for bad in [
            good.replace("native 2", "native 1"),
            good.replace("42", "042"),
            good.replace("42", "10000001"),
            good.replace("\n0\n", "\ntrue\n"),
            good.trim_end().to_owned(),
            format!("{good}extra"),
            format!("{good}\n"),
            "qleisli.qirf-native 2\nerror\ncontract\nextra".into(),
        ] {
            assert!(response(bad.as_bytes(), false).is_err(), "{bad}");
        }
        assert_eq!(
            response(b"qleisli.qirf-native 2\nerror\ncontract\n", false)
                .unwrap_err()
                .code,
            "contract"
        );
    }

    #[test]
    #[cfg(unix)]
    fn process_failures_never_fall_back_or_wait_beyond_the_deadline() {
        use std::os::unix::fs::symlink;
        use std::time::{SystemTime, UNIX_EPOCH};
        let directory = std::env::temp_dir().join(format!(
            "qleisli-native-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v030/execution-view-binding/process-failure.sh");
        // Immutable code avoids ETXTBSY from concurrent forked children that
        // temporarily inherit a fixture writer. Each link selects one case.
        for (case, code) in [
            ("failed-acceptance", "io"),
            ("contract", "contract"),
            ("large-output", "limit"),
            ("sleep", "limit"),
            ("inherited-pipe", "limit"),
            ("empty", "format"),
        ] {
            let executable = directory.join(case);
            symlink(&fixture, &executable).unwrap();
            let start = Instant::now();
            let error =
                invoke(&executable, vec![0; 4096], false, Duration::from_secs(1)).unwrap_err();
            assert_eq!(error.code, code, "{case}: {error}");
            assert!(start.elapsed() < Duration::from_secs(2));
        }
        assert_eq!(
            invoke(
                &directory.join("absent"),
                vec![],
                false,
                Duration::from_millis(100)
            )
            .unwrap_err()
            .code,
            "io"
        );
    }
}
