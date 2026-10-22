//! Bounded process IO. A process status and a strictly framed reply must agree.
use std::path::Path;
#[cfg(test)]
use std::time::{Duration, Instant};

use super::{Error, Result};
use crate::interchange::native_packet::Scope;
use crate::interchange::process::TransportLimits;

pub(super) const REJECTION_MESSAGE: &str =
    "Lean native checker rejected the artifact/request; no fallback";

pub(super) struct Decision {
    pub(super) context: crate::interchange::native_context::CheckedContext,
    pub(super) exact_work: usize,
}

#[cfg(test)]
fn response(bytes: &[u8], requested: bool) -> Result<usize> {
    response_bound(
        bytes,
        requested,
        Scope::Inspection,
        crate::edition::Edition::E2026,
        crate::interchange::native_context::Mode::Ordinary,
    )
    .map(|value| value.exact_work)
}

fn response_bound(
    bytes: &[u8],
    requested: bool,
    scope: Scope,
    edition: crate::edition::Edition,
    mode: crate::interchange::native_context::Mode,
) -> Result<Decision> {
    use crate::interchange::native_context::{self, Reply};
    let (context, payload) = match native_context::parse(bytes, edition, mode, scope)? {
        Reply::Rejected(code) => {
            let code = if code == "version" { "kernel" } else { code };
            return Err(Error::new(
                code,
                if code == "kernel" {
                    "native checker product version differs from the Rust package"
                } else {
                    REJECTION_MESSAGE
                },
            ));
        }
        Reply::Checked { context, payload } => (context, payload),
    };
    let [work, flag] = payload.as_slice() else {
        return Err(Error::format("malformed/trailing native response"));
    };
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
    Ok(Decision {
        context,
        exact_work: work,
    })
}

pub(super) fn check_mode(
    executable: &Path,
    packet: Vec<u8>,
    requested: bool,
    mode: &str,
    scope: Scope,
    edition: crate::edition::Edition,
) -> Result<Decision> {
    invoke_mode(
        executable,
        packet,
        requested,
        TransportLimits::FINITE,
        mode,
        scope,
        edition,
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
        crate::edition::Edition::E2026,
    )
    .map(|value| value.exact_work)
}
fn invoke_mode(
    executable: &Path,
    packet: Vec<u8>,
    requested: bool,
    limits: TransportLimits,
    mode: &str,
    scope: Scope,
    edition: crate::edition::Edition,
) -> Result<Decision> {
    let mode = crate::interchange::native_context::Mode::parse(mode)?;
    if !matches!(
        mode,
        crate::interchange::native_context::Mode::Ordinary
            | crate::interchange::native_context::Mode::Contract
            | crate::interchange::native_context::Mode::CarrierPure
    ) {
        return Err(Error::format(
            "finite checking requires an ordinary, contract or carrier native mode",
        ));
    }
    limits.invoke(executable, packet, mode.argument(), |bytes| {
        response_bound(bytes, requested, scope, edition, mode)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replies_bind_request_presence_and_reject_ambiguous_success() {
        let good = format!(
            "qleisli.native-result 3\naccepted\n2026\n{}\n--qirf-native\ninspection\n42\n0\n",
            env!("CARGO_PKG_VERSION")
        );
        assert_eq!(response(good.as_bytes(), false).unwrap(), 42);
        assert!(response(good.as_bytes(), true).is_err());
        for bad in [
            "qleisli.engineering-pure-native 1\nengineering-checked\nexecution\n42\n".into(),
            good.replace("result 3", "result 2"),
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
            response(b"qleisli.native-result 3\nerror\ncontract\n", false)
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
            .join("tests/fixtures/verification_v030/native-edition-context/process-failure.sh");
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
