//! Bounded process IO. A process status and a strictly framed reply must agree.
use std::path::Path;
use std::time::Duration;
#[cfg(test)]
use std::time::Instant;

use super::{Error, Result};

pub(super) const REJECTION_MESSAGE: &str =
    "Lean native checker rejected the artifact/request; no fallback";

fn response(bytes: &[u8], requested: bool) -> Result<usize> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid native response UTF-8"))?;
    let lines: Vec<_> = text.split('\n').collect();
    if lines.first() != Some(&"qleisli.qirf-native 1") {
        return Err(Error::format("unknown native response protocol"));
    }
    match lines.as_slice() {
        [_, "error", code, ""] => {
            let code = match *code {
                "limit" => "limit",
                "contract" => "contract",
                "invalid_ir" => "invalid_ir",
                "format" => "format",
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
        [_, "accepted", work, flag, ""] => {
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
) -> Result<usize> {
    invoke_mode(executable, packet, requested, Duration::from_secs(60), mode)
}
#[cfg(test)]
fn invoke(executable: &Path, packet: Vec<u8>, requested: bool, timeout: Duration) -> Result<usize> {
    invoke_mode(executable, packet, requested, timeout, "--qirf-native")
}
fn invoke_mode(
    executable: &Path,
    packet: Vec<u8>,
    requested: bool,
    timeout: Duration,
    mode: &str,
) -> Result<usize> {
    crate::interchange::process::invoke(executable, packet, mode, timeout, 256, |bytes| {
        response(bytes, requested)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replies_bind_request_presence_and_reject_ambiguous_success() {
        let good = "qleisli.qirf-native 1\naccepted\n42\n0\n";
        assert_eq!(response(good.as_bytes(), false).unwrap(), 42);
        assert!(response(good.as_bytes(), true).is_err());
        for bad in [
            good.replace("native 1", "native 0"),
            good.replace("42", "042"),
            good.replace("42", "10000001"),
            good.replace("\n0\n", "\ntrue\n"),
            good.trim_end().to_owned(),
            format!("{good}extra"),
            format!("{good}\n"),
            "qleisli.qirf-native 1\nerror\ncontract\nextra".into(),
        ] {
            assert!(response(bad.as_bytes(), false).is_err(), "{bad}");
        }
        assert_eq!(
            response(b"qleisli.qirf-native 1\nerror\ncontract\n", false)
                .unwrap_err()
                .code,
            "contract"
        );
    }

    #[test]
    #[cfg(unix)]
    fn process_failures_never_fall_back_or_wait_beyond_the_deadline() {
        use std::os::unix::fs::PermissionsExt;
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
        let executable = directory.join("kernel");
        for (script, code) in [
            (
                "cat >/dev/null\nprintf 'qleisli.qirf-native 1\\naccepted\\n0\\n0\\n'\nexit 1",
                "io",
            ),
            (
                "cat >/dev/null\nprintf 'qleisli.qirf-native 1\\nerror\\ncontract\\n'",
                "contract",
            ),
            (
                "while :; do printf 'xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx'; done",
                "limit",
            ),
            ("exec sleep 4", "limit"),
            ("sleep 4 &\nexit 0", "limit"),
            ("exit 0", "format"),
        ] {
            std::fs::write(&executable, format!("#!/bin/sh\n{script}\n")).unwrap();
            std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700)).unwrap();
            let start = Instant::now();
            let error =
                invoke(&executable, vec![0; 4096], false, Duration::from_secs(1)).unwrap_err();
            assert_eq!(error.code, code, "{script}: {error}");
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
