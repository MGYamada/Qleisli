//! Host process transport, shared by finite and hierarchical native requests.
//! Unix invocations own a process group; nonblocking pipes need no IO threads.
//! This cleans up ordinary descendants, not executables that escape their group.
use std::io::{Read, Write};
use std::path::Path;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use super::{Error, Result};

mod limits;
pub(crate) use limits::TransportLimits;

// A child stays owned until group cleanup has completed. Taking it before
// reaping also disarms Drop, so cleanup never signals a number after reaping it.
struct Invocation(Option<Child>);

fn stop_descendants(child: &mut Child) {
    #[cfg(all(test, unix, not(any(target_os = "openbsd", target_os = "redox"))))]
    {
        use rustix::process::{Pid, WaitId, WaitIdOptions, waitid};
        let pid = Pid::from_raw(child.id() as i32).unwrap();
        // Assert at the actual cleanup site, including the success path: a
        // future wait-before-signal regression must fail before sending KILL.
        let status = waitid(
            WaitId::Pid(pid),
            WaitIdOptions::EXITED | WaitIdOptions::NOHANG | WaitIdOptions::NOWAIT,
        );
        assert_ne!(status.err(), Some(rustix::io::Errno::CHILD));
    }
    #[cfg(unix)]
    if let Some(group) = rustix::process::Pid::from_raw(child.id() as i32) {
        let _ = rustix::process::kill_process_group(group, rustix::process::Signal::KILL);
    }
    let _ = child.kill();
}

impl Invocation {
    fn child(&mut self) -> &mut Child {
        self.0.as_mut().expect("unreaped native child")
    }

    fn finish(&mut self) -> std::io::Result<ExitStatus> {
        let mut child = self.0.take().expect("unreaped native child");
        stop_descendants(&mut child);
        child.wait()
    }

    fn try_wait(&mut self) -> std::io::Result<Option<ExitStatus>> {
        #[cfg(all(unix, not(any(target_os = "openbsd", target_os = "redox"))))]
        {
            use rustix::process::{Pid, WaitId, WaitIdOptions, waitid};
            let pid = Pid::from_raw(self.child().id() as i32).expect("native child PID");
            // WNOWAIT keeps an exited leader waitable and reserves its PID/PGID
            // until finish has stopped descendants and reaped the leader.
            match waitid(
                WaitId::Pid(pid),
                WaitIdOptions::EXITED | WaitIdOptions::NOHANG | WaitIdOptions::NOWAIT,
            ) {
                Ok(Some(_)) => self.finish().map(Some),
                Ok(None) => Ok(None),
                Err(error) if error == rustix::io::Errno::INTR => Ok(None),
                Err(error) if error == rustix::io::Errno::CHILD => {
                    // An external reaper violates our child-ownership premise.
                    // Do not signal a number whose reservation is now unknown.
                    self.0.take();
                    Err(error.into())
                }
                Err(error) => Err(error.into()),
            }
        }
        #[cfg(any(not(unix), target_os = "openbsd", target_os = "redox"))]
        {
            let status = self.child().try_wait()?;
            if status.is_some() {
                self.0.take();
            }
            Ok(status)
        }
    }
}

impl Drop for Invocation {
    fn drop(&mut self) {
        if self.0.is_some() {
            let _ = self.finish();
        }
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
    // rustix cannot provide a non-reaping wait on these Unix targets. Reject
    // before spawning rather than signal an unreserved process-group number.
    if cfg!(all(unix, any(target_os = "openbsd", target_os = "redox"))) {
        return Err(Error::new(
            "unsupported",
            "native process-group cleanup requires a non-reaping wait on this platform",
        ));
    }

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
    let mut child =
        Invocation(Some(command.spawn().map_err(|e| {
            Error::new("io", format!("cannot start Lean native checker: {e}"))
        })?));
    let stdin = child.child().stdin.take().expect("piped stdin");
    let stdout = child.child().stdout.take().expect("piped stdout");
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

#[cfg(all(test, unix, not(any(target_os = "openbsd", target_os = "redox"))))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;
    use std::os::unix::process::CommandExt;

    #[test]
    fn each_transport_profile_accepts_its_exact_byte_limit_and_rejects_one_more() {
        let executable = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v030/transport-limit.sh");
        for (limits, maximum) in [
            (TransportLimits::FINITE, 256),
            (TransportLimits::HIERARCHY_INSPECTION, 1_100_000),
            (TransportLimits::HIERARCHY_REQUEST, 2_200_000),
        ] {
            let limits = limits.with_timeout(Duration::from_secs(5));
            let accepted = limits
                .invoke(
                    &executable,
                    format!("{maximum}\n").into_bytes(),
                    "--test",
                    |bytes| Ok(bytes.len()),
                )
                .unwrap();
            assert_eq!(accepted, maximum);
            let refused = limits
                .invoke(
                    &executable,
                    format!("{}\n", maximum + 1).into_bytes(),
                    "--test",
                    |_| -> Result<()> { panic!("oversized reply reached decoder") },
                )
                .unwrap_err();
            assert_eq!(refused.code, "limit");
            assert_eq!(refused.message, "native response exceeds limit");
        }
    }

    #[test]
    fn exited_leader_remains_waitable_until_cleanup_and_disarms_after_reaping() {
        use rustix::process::{Pid, WaitId, WaitIdOptions, waitid};
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "exit 0"]).process_group(0);
        let mut invocation = Invocation(Some(command.spawn().unwrap()));
        let pid = Pid::from_raw(invocation.child().id() as i32).unwrap();
        let options = WaitIdOptions::EXITED | WaitIdOptions::NOHANG | WaitIdOptions::NOWAIT;
        let deadline = Instant::now() + Duration::from_secs(2);
        while waitid(WaitId::Pid(pid), options).unwrap().is_none() {
            assert!(Instant::now() < deadline, "leader did not exit");
            std::thread::sleep(Duration::from_millis(1));
        }

        // Cleanup must leave the leader's PID reserved until the final wait.
        stop_descendants(invocation.child());
        assert!(waitid(WaitId::Pid(pid), options).unwrap().is_some());
        assert!(invocation.try_wait().unwrap().unwrap().success());
        assert!(invocation.0.is_none());
        assert!(matches!(
            waitid(WaitId::Pid(pid), options),
            Err(rustix::io::Errno::CHILD)
        ));
        // No PID remains owned: dropping the guard must perform no cleanup.
        drop(invocation);
    }

    #[test]
    fn failed_leader_cannot_authorize_a_successful_response() {
        let result = invoke(
            Path::new("/usr/bin/false"),
            vec![],
            "--test",
            Duration::from_secs(2),
            256,
            |_| Ok(()),
        );
        assert_eq!(result.unwrap_err().code, "io");
    }

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
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/verification_v029/process-tree.sh");
        let pidfile = root.join("pid");
        // Test code is immutable even while other library tests fork. A link
        // supplies the private directory and case without executable writes.
        for case in ["exit", "wait"] {
            let executable = root.join(case);
            symlink(&fixture, &executable).unwrap();
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
        let executable = root.join("ok");
        symlink(&fixture, &executable).unwrap();
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
