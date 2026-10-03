//! Host process transport, shared by finite and hierarchical native requests.
//! Unix invocations own a process group; nonblocking pipes need no IO threads.
//! This cleans up ordinary descendants, not executables that escape their group.
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use super::{Error, Result};

struct Invocation(Child);
impl Drop for Invocation {
    fn drop(&mut self) {
        #[cfg(unix)]
        if let Some(group) = rustix::process::Pid::from_raw(self.0.id() as i32) {
            let _ = rustix::process::kill_process_group(group, rustix::process::Signal::KILL);
        }
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

pub(super) fn invoke<T>(
    executable: &Path,
    packet: Vec<u8>,
    mode: &str,
    timeout: Duration,
    maximum: usize,
    decode: impl FnOnce(&[u8]) -> Result<T>,
) -> Result<T> {
    let mut command = Command::new(executable);
    command
        .arg(mode)
        .arg(env!("CARGO_PKG_VERSION"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    let mut child = Invocation(
        command
            .spawn()
            .map_err(|e| Error::new("io", format!("cannot start Lean native checker: {e}")))?,
    );
    let stdin = child.0.stdin.take().expect("piped stdin");
    let stdout = child.0.stdout.take().expect("piped stdout");
    let deadline = Instant::now() + timeout;
    #[cfg(unix)]
    let (bytes, written) = {
        for fd in [
            &stdin as &dyn std::os::fd::AsFd,
            &stdout as &dyn std::os::fd::AsFd,
        ] {
            let flags = rustix::fs::fcntl_getfl(fd)
                .map_err(|e| Error::new("io", format!("native pipe flags: {e}")))?;
            rustix::fs::fcntl_setfl(fd, flags | rustix::fs::OFlags::NONBLOCK)
                .map_err(|e| Error::new("io", format!("native nonblocking pipe: {e}")))?;
        }
        let mut stdin = Some(stdin);
        let mut stdout = stdout;
        let mut offset = 0;
        let mut written = Ok(());
        let mut bytes = Vec::new();
        let mut eof = false;
        loop {
            if let Some(pipe) = &mut stdin {
                if offset < packet.len() {
                    match pipe.write(&packet[offset..]) {
                        Ok(0) => {
                            written = Err(std::io::ErrorKind::WriteZero.into());
                            stdin = None;
                        }
                        Ok(count) => offset += count,
                        Err(e)
                            if matches!(
                                e.kind(),
                                std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
                            ) => {}
                        Err(e) => {
                            written = Err(e);
                            stdin = None;
                        }
                    }
                }
                if offset == packet.len() {
                    stdin = None;
                }
            }
            if !eof {
                let mut buffer = [0; 8192];
                let count = buffer.len().min(maximum + 1 - bytes.len());
                match stdout.read(&mut buffer[..count]) {
                    Ok(0) => eof = true,
                    Ok(count) => bytes.extend_from_slice(&buffer[..count]),
                    Err(e)
                        if matches!(
                            e.kind(),
                            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
                        ) => {}
                    Err(e) => return Err(Error::new("io", format!("native output failed: {e}"))),
                }
                if bytes.len() > maximum {
                    return Err(Error::limit("native response exceeds limit"));
                }
            }
            if eof && stdin.is_none() {
                break (bytes, written);
            }
            if Instant::now() >= deadline {
                return Err(Error::limit("Lean native checker timed out; no fallback"));
            }
            std::thread::sleep(Duration::from_millis(1));
        }
    };
    // Other platforms retain the existing process/pipe trust assumption. Their
    // wait is bounded, but process-tree containment requires a platform job API.
    #[cfg(not(unix))]
    let (bytes, written) = {
        use std::sync::mpsc;
        let (tx, rx) = mpsc::channel();
        let (write_tx, write_rx) = mpsc::channel();
        std::thread::spawn(move || {
            let _ = write_tx.send({
                let mut stdin = stdin;
                stdin.write_all(&packet)
            });
        });
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let result = stdout
                .take((maximum + 1) as u64)
                .read_to_end(&mut bytes)
                .map(|_| bytes);
            let _ = tx.send(result);
        });
        let bytes = rx
            .recv_timeout(deadline.saturating_duration_since(Instant::now()))
            .map_err(|_| Error::limit("Lean native checker timed out; no fallback"))?
            .map_err(|e| Error::new("io", format!("native output failed: {e}")))?;
        if bytes.len() > maximum {
            return Err(Error::limit("native response exceeds limit"));
        }
        let written = write_rx
            .recv_timeout(deadline.saturating_duration_since(Instant::now()))
            .map_err(|_| Error::limit("Lean native checker timed out; no fallback"))?;
        (bytes, written)
    };
    let status = loop {
        if let Some(status) = child
            .0
            .try_wait()
            .map_err(|e| Error::new("io", format!("native wait failed: {e}")))?
        {
            break status;
        }
        if Instant::now() >= deadline {
            return Err(Error::limit("Lean native checker timed out; no fallback"));
        }
        std::thread::sleep(Duration::from_millis(1));
    };
    // Preserve a framed rejection even if the checker closed its input early.
    let result = decode(&bytes)?;
    if !status.success() {
        return Err(Error::new(
            "io",
            "failed Lean native checker returned acceptance",
        ));
    }
    written.map_err(|e| Error::new("io", format!("native input failed: {e}")))?;
    Ok(result)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn inherited_pipes_do_not_leave_descendants_or_transport_threads() {
        let root = std::env::temp_dir().join(format!(
            "qleisli-process-tree-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(root.clone());
        let executable = root.join("checker");
        let pidfile = root.join("pid");
        for tail in ["exit 0", "wait"] {
            std::fs::write(
                &executable,
                format!(
                    "#!/bin/sh\nsleep 30 &\necho $! > '{}'\n{tail}\n",
                    pidfile.display()
                ),
            )
            .unwrap();
            std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o700)).unwrap();
            let start = Instant::now();
            let error = invoke(
                &executable,
                vec![0; 131072],
                "--test",
                Duration::from_secs(2),
                256,
                |_| Ok(()),
            )
            .unwrap_err();
            assert_eq!(error.code, "limit");
            assert!(start.elapsed() < Duration::from_secs(4));
            let pid = std::fs::read_to_string(&pidfile).unwrap();
            let deadline = Instant::now() + Duration::from_secs(2);
            loop {
                let status = Command::new("ps")
                    .args(["-p", pid.trim(), "-o", "stat="])
                    .output()
                    .unwrap();
                assert!(status.stderr.is_empty(), "ps failed: {status:?}");
                let state = String::from_utf8(status.stdout).unwrap();
                if state.trim().is_empty() || state.trim().starts_with('Z') {
                    break;
                }
                assert!(
                    Instant::now() < deadline,
                    "descendant {} still running: {state}",
                    pid.trim()
                );
                std::thread::sleep(Duration::from_millis(10));
            }
            // Unix transport uses no reader/writer threads; inherited handles
            // therefore cannot retain detached transport threads after return.
        }
        std::fs::write(&executable, "#!/bin/sh\ncat >/dev/null\nprintf 'ok\\n'\n").unwrap();
        assert_eq!(
            invoke(
                &executable,
                vec![1; 16384],
                "--test",
                Duration::from_secs(2),
                256,
                |bytes| Ok(bytes.to_vec())
            )
            .unwrap(),
            b"ok\n"
        );
    }
}
