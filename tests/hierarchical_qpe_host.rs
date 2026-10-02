//! Named-QPE private host framing and exact obligation completeness.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::path::{Path, PathBuf};

fn directory() -> PathBuf {
    std::env::var_os("QLEISLI_QPE_HOST_FIXTURES")
        .map(PathBuf::from)
        .expect("fixture harness required")
}
fn files(path: &Path, name: &str) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let read = |suffix: &str| std::fs::read(path.join(format!("{name}.{suffix}.json"))).unwrap();
    (read("payload"), read("request"), read("candidate"))
}

#[test]
#[ignore = "requires generated small fixtures and an audited native Lean kernel"]
fn native_qpe_instrument_binds_provider_phase_hadamards_and_all_boundaries() {
    let root = directory();
    let kernel =
        Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").expect("native kernel required"));
    for line in std::fs::read_to_string(root.join("cases.txt"))
        .unwrap()
        .lines()
    {
        let (name, expected) = line.split_once('|').unwrap();
        let (payload, request, candidate) = files(&root, name);
        match kernel.check_qpe_instrument_native(&payload, &request, &candidate) {
            Ok(native) => {
                assert_eq!(expected, "ok", "{name}");
                assert_eq!(native.payload(), payload);
                assert_eq!(native.request(), Some(request.as_slice()));
                assert_eq!(native.candidate(), Some(candidate.as_slice()));
                assert!(native.exact_work() > 0 && native.exact_work() <= 10_000_000);
            }
            Err(error) => assert_eq!(error.code, expected, "native-only {name}: {error}"),
        }
        match kernel.check_qpe_instrument(&payload, &request, &candidate) {
            Ok(checked) => {
                assert_eq!(expected, "ok", "{name}");
                assert_eq!(checked.candidate(), candidate);
                assert_eq!(checked.instrument().request(), request);
                assert_eq!(checked.instrument().reconstruction().payload(), payload);
                assert!(checked.instrument().reconstruction().structural_work() <= 2_000_000);
                assert!(checked.instrument().reconstruction().exact_work() > 0);
                // The wrapper retains the exact existing executable instrument.
                if name == "small" {
                    let state = checked
                        .instrument()
                        .execute(
                            &[[0.0, 0.0], [1.0, 0.0]],
                            1,
                            ExecutionLimits {
                                max_amplitudes: 4096,
                                max_steps: 100000,
                            },
                        )
                        .unwrap();
                    assert_eq!(state.branches.len(), 4);
                    let mass: f64 = state
                        .branches
                        .iter()
                        .flatten()
                        .map(|z| z[0] * z[0] + z[1] * z[1])
                        .sum();
                    assert!((mass - 1.0).abs() < 1e-12);
                }
                println!(
                    "QPE_HOST|{name}|ok|{}|{}",
                    checked.instrument().reconstruction().structural_work(),
                    checked.instrument().reconstruction().exact_work()
                );
            }
            Err(error) => assert_eq!(error.code, expected, "{name}: {error}"),
        }
    }
}

#[test]
#[cfg(unix)]
#[ignore = "requires generated small fixtures"]
fn qpe_host_rejects_missing_duplicate_and_substituted_runtime_obligations() {
    use std::os::unix::fs::PermissionsExt;
    let root = directory();
    let (payload, request, candidate) = files(&root, "finite-provider");
    let runtime = root.join("fake-runtime");
    for entry in std::fs::read_dir(root.join("bad-responses")).unwrap() {
        let entry = entry.unwrap();
        let response = std::fs::read_to_string(entry.path()).unwrap();
        assert!(!response.contains('\''));
        let frame = root.join("captured-frame");
        assert!(!frame.to_string_lossy().contains('\''));
        std::fs::write(
            &runtime,
            format!(
                "#!/bin/sh\ncat > '{}'\nprintf '%s' '{response}'\n",
                frame.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&runtime, std::fs::Permissions::from_mode(0o700)).unwrap();
        let error = Kernel::new(&runtime)
            .check_qpe_instrument(&payload, &request, &candidate)
            .unwrap_err();
        assert_eq!(error.code, "format", "{}: {error}", entry.path().display());
    }
}
