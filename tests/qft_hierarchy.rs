//! Native QFT hierarchy authoring probe. Numerical oracles live in Python and
//! are never passed to the acceptance API as evidence.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::hierarchical::Kernel;

#[test]
#[ignore = "run through scripts/test_hierarchical_fourier_base.py with native bound H requests"]
fn reconstruct_bound_hadamard_requests() {
    use qleisli::contract::exact::{Budget, Exact, Matrix};
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK};
    use qleisli::interchange::finite_leaf::{UnitaryBoundary, check_unitary};
    use qleisli::ir::{BasisShape, QuantumPort, TokenId, WireId};
    use std::collections::BTreeMap;

    let directory = std::env::var_os("QLEISLI_HADAMARD_FIXTURES").unwrap();
    let directory = std::path::Path::new(&directory);
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let mut budgets = BTreeMap::new();
    for width in 1..=8 {
        let payload = std::fs::read(directory.join(format!("qft-{width}.json"))).unwrap();
        let checked = kernel.inspect(&payload).unwrap();
        budgets.insert(
            width,
            Budget::new(DEFAULT_EXACT_WORK - checked.exact_work()),
        );
    }
    // The requested matrix is independent of every artifact's meaning table.
    let r = Exact::inv_sqrt2();
    let expected = Matrix::new(2, 2, vec![r, r, r, r.neg().unwrap()]).unwrap();
    let requests = std::fs::read_to_string(directory.join("requests.txt")).unwrap();
    let mut count = 0;
    for line in requests.lines() {
        let fields: Vec<_> = line.split('|').collect();
        assert_eq!(fields.len(), 8);
        let [
            name,
            width,
            input,
            output,
            input_axis,
            output_axis,
            outcome,
            file,
        ] = fields.as_slice()
        else {
            unreachable!()
        };
        let width: usize = width.parse().unwrap();
        let port = |owner: &str, axis: &str| QuantumPort {
            token: TokenId(owner.parse().unwrap()),
            wires: vec![WireId(axis.parse().unwrap())],
            shape: BasisShape { bits: 1 },
        };
        let boundary = UnitaryBoundary::new(
            BasisType::Bit,
            port(input, input_axis),
            port(output, output_axis),
        )
        .unwrap();
        let bytes = std::fs::read(directory.join(file)).unwrap();
        let budget = budgets.get_mut(&width).unwrap();
        match check_unitary(&bytes, &boundary, &expected, budget) {
            Ok(checked) => {
                assert_eq!(*outcome, "ok", "{name}");
                assert!(checked.matches(&bytes, &boundary, &expected));
                println!("H|{name}|ok|{}", checked.exact_work());
            }
            Err(error) => {
                assert_eq!(error.code, *outcome, "{name}: {error}");
                println!("H|{name}|{}", error.code);
            }
        }
        count += 1;
    }
    assert_eq!(count, 40); // 36 actual positive requests and four altered requests.
    for (width, budget) in budgets {
        println!("H-WORK|{width}|{}", DEFAULT_EXACT_WORK - budget.remaining());
    }
}

#[test]
#[ignore = "run through scripts/test_hierarchical_qft.py with an audited kernel"]
fn inspect_authored_qft_hierarchies() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let directory = std::env::var_os("QLEISLI_QFT_FIXTURES").unwrap();
    let shared = std::env::var("QLEISLI_QFT_CONSTRUCTION").unwrap() == "shared-gradient";
    let widths: &[usize] = if shared {
        &[1, 2, 3, 4, 5, 6, 7, 8]
    } else {
        &[1, 2, 3, 4, 8]
    };
    for &width in widths {
        let path = std::path::Path::new(&directory).join(format!("qft-{width}.json"));
        let payload = std::fs::read(path).unwrap();
        match kernel.inspect(&payload) {
            Ok(checked) => {
                println!(
                    "QFT|{width}|accepted|{}|{}|{}",
                    checked.structural_work(),
                    checked.exact_work(),
                    checked.leaves().len()
                );
                let request = std::fs::read(
                    std::path::Path::new(&directory).join(format!("qft-request-{width}.json")),
                )
                .unwrap();
                if shared {
                    let bound = kernel.check_against(&payload, &request).unwrap();
                    assert_eq!(bound.request(), request);
                    assert_eq!(bound.reconstruction().payload(), payload);
                    assert!(bound.reconstruction().structural_work() <= 2_000_000);
                    assert_eq!(bound.reconstruction().exact_work(), 67 * width);
                    assert!(bound.reconstruction().native_exact_work() > 67 * width);
                    println!(
                        "FOURIER|{width}|accepted|{}|{}",
                        bound.reconstruction().structural_work(),
                        bound.reconstruction().exact_work()
                    );
                } else {
                    // The lifted construction is a distinct unsupported shape.
                    assert!(kernel.check_against(&payload, &request).is_err());
                }
            }
            Err(error) => {
                // The remaining capacity failure is recorded, not accepted as
                // completion of the full width-eight profile.
                assert!(!shared && width == 8, "{width}: {error}");
                assert_eq!(error.code, "limit", "{width}: {error}");
                println!("QFT|{width}|{}|{}", error.code, error.message);
            }
        }
    }
    let mut faults = vec![
        ("layout", "invalid_ir"),
        ("empty-owner", "invalid_ir"),
        ("h", "contract"),
        ("phase", "contract"),
    ];
    if shared {
        faults.push(("repeat", "contract"));
    }
    for (name, code) in faults {
        let payload =
            std::fs::read(std::path::Path::new(&directory).join(format!("invalid-{name}.json")))
                .unwrap();
        assert_eq!(kernel.inspect(&payload).unwrap_err().code, code, "{name}");
        println!("FAULT|{name}|{code}");
    }
}

#[test]
#[ignore = "run through scripts/test_hierarchical_fourier_host.py with an audited kernel"]
fn native_fourier_request_faults() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let directory = std::path::PathBuf::from(std::env::var_os("QLEISLI_FOURIER_FIXTURES").unwrap());
    let manifest = std::fs::read_to_string(directory.join("cases.txt")).unwrap();
    for line in manifest.lines() {
        let fields: Vec<_> = line.split('|').collect();
        let [name, artifact, request, inspect, expected, executable] = fields.as_slice() else {
            panic!("invalid case")
        };
        let payload = std::fs::read(directory.join(artifact)).unwrap();
        let request = std::fs::read(directory.join(request)).unwrap();
        if *inspect == "ok" {
            kernel.inspect(&payload).unwrap();
        } else {
            assert_eq!(
                kernel.inspect(&payload).unwrap_err().code,
                *inspect,
                "{name}: full artifact"
            );
        }
        let selected = if executable.is_empty() {
            kernel.clone()
        } else {
            Kernel::new(directory.join(executable))
        };
        match selected.check_against_native(&payload, &request) {
            Ok(native) => {
                assert_eq!(*expected, "ok", "native-only {name}");
                assert_eq!(native.payload(), payload);
                assert_eq!(native.request(), Some(request.as_slice()));
                assert!(native.exact_work() > 0 && native.exact_work() <= 10_000_000);
            }
            Err(error) => assert_eq!(error.code, *expected, "native-only {name}: {error}"),
        }
        match selected.check_against(&payload, &request) {
            Ok(checked) => {
                assert_eq!(*expected, "ok", "{name}");
                assert_eq!(checked.request(), request);
                assert_eq!(checked.reconstruction().payload(), payload);
                println!(
                    "HOST|{name}|ok|{}|{}",
                    checked.reconstruction().structural_work(),
                    checked.reconstruction().exact_work()
                );
            }
            Err(error) => {
                assert_eq!(error.code, *expected, "{name}: {error}");
                println!("HOST|{name}|{}", error.code);
            }
        }
    }
}
