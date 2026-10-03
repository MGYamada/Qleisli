//! Bounded process IO. A process status and a strictly framed reply must agree.
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use super::{Error, Result};

fn response(bytes: &[u8], requested: bool) -> Result<usize> {
    let text =
        std::str::from_utf8(bytes).map_err(|_| Error::format("invalid dual response UTF-8"))?;
    let lines: Vec<_> = text.split('\n').collect();
    if lines.first() != Some(&"qleisli.qirf-dual 1") {
        return Err(Error::format("unknown dual response protocol"));
    }
    match lines.as_slice() {
        [_, "error", code, ""] => {
            let code = match *code {
                "limit" => "limit",
                "contract" => "contract",
                "invalid_ir" => "invalid_ir",
                "format" => "format",
                _ => return Err(Error::format("unknown dual rejection")),
            };
            Err(Error::new(
                code,
                "Lean dual checker rejected the artifact/request; no fallback",
            ))
        }
        [_, "accepted", work, flag, ""] => {
            if work.is_empty()
                || work.len() > 8
                || !work.bytes().all(|b| b.is_ascii_digit())
                || work.len() > 1 && work.starts_with('0')
            {
                return Err(Error::format("noncanonical dual work count"));
            }
            let work: usize = work
                .parse()
                .map_err(|_| Error::format("invalid dual work count"))?;
            if work > 10_000_000 || *flag != if requested { "1" } else { "0" } {
                return Err(Error::format(
                    "dual work bound or request coverage disagrees",
                ));
            }
            Ok(work)
        }
        _ => Err(Error::format("malformed/trailing dual response")),
    }
}

pub(super) fn check(executable: &Path, packet: Vec<u8>, requested: bool) -> Result<usize> {
    invoke(executable, packet, requested, Duration::from_secs(60))
}

fn invoke(executable: &Path, packet: Vec<u8>, requested: bool, timeout: Duration) -> Result<usize> {
    let mut child = Command::new(executable)
        .arg("--qirf-dual")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| Error::new("io", format!("cannot start Lean dual checker: {e}")))?;
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let (write_tx, write_rx) = mpsc::channel();
    let (read_tx, read_rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = write_tx.send(stdin.write_all(&packet));
    });
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let result = stdout.take(257).read_to_end(&mut bytes).map(|_| bytes);
        let _ = read_tx.send(result);
    });
    let deadline = Instant::now() + timeout;
    let mut output = None;
    let mut written = None;
    // Do not join potentially blocked pipes after exit/timeout: a descendant
    // might have inherited a handle. Every wait here has the same deadline.
    let result = (|| {
        loop {
            if output.is_none() {
                match read_rx.try_recv() {
                    Ok(Ok(bytes)) if bytes.len() <= 256 => output = Some(bytes),
                    Ok(Ok(_)) => return Err(Error::limit("dual response exceeds 256 bytes")),
                    Ok(Err(e)) => return Err(Error::new("io", format!("dual output failed: {e}"))),
                    Err(mpsc::TryRecvError::Disconnected) => {
                        return Err(Error::new("io", "dual output thread failed"));
                    }
                    Err(mpsc::TryRecvError::Empty) => {}
                }
            }
            if written.is_none() {
                match write_rx.try_recv() {
                    Ok(value) => written = Some(value),
                    Err(mpsc::TryRecvError::Disconnected) => {
                        return Err(Error::new("io", "dual input thread failed"));
                    }
                    Err(mpsc::TryRecvError::Empty) => {}
                }
            }
            let status = child
                .try_wait()
                .map_err(|e| Error::new("io", format!("dual wait failed: {e}")))?;
            if let (Some(status), Some(bytes), Some(write)) = (status, &output, &written) {
                let work = response(bytes, requested)?;
                if !status.success() {
                    return Err(Error::new(
                        "io",
                        "failed Lean dual checker returned acceptance",
                    ));
                }
                write
                    .as_ref()
                    .map_err(|e| Error::new("io", format!("dual input failed: {e}")))?;
                return Ok(work);
            }
            if Instant::now() >= deadline {
                return Err(Error::limit("Lean dual checker timed out; no fallback"));
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    })();
    if result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replies_bind_request_presence_and_reject_ambiguous_success() {
        let good = "qleisli.qirf-dual 1\naccepted\n42\n0\n";
        assert_eq!(response(good.as_bytes(), false).unwrap(), 42);
        assert!(response(good.as_bytes(), true).is_err());
        for bad in [
            good.replace("dual 1", "dual 0"),
            good.replace("42", "042"),
            good.replace("42", "10000001"),
            good.replace("\n0\n", "\ntrue\n"),
            good.trim_end().to_owned(),
            format!("{good}extra"),
            format!("{good}\n"),
            "qleisli.qirf-dual 1\nerror\ncontract\nextra".into(),
        ] {
            assert!(response(bad.as_bytes(), false).is_err(), "{bad}");
        }
        assert_eq!(
            response(b"qleisli.qirf-dual 1\nerror\ncontract\n", false)
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
            "qleisli-dual-{}-{}",
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
                "cat >/dev/null\nprintf 'qleisli.qirf-dual 1\\naccepted\\n0\\n0\\n'\nexit 1",
                "io",
            ),
            (
                "cat >/dev/null\nprintf 'qleisli.qirf-dual 1\\nerror\\ncontract\\n'",
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
