//! Fresh native inspection of source-produced corpus artifacts.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use qleisli::interchange::hierarchical::Kernel;

#[test]
#[ignore = "run through scripts/test_sized_corpus.py with an audited native kernel"]
fn inspect_source_produced_corpus() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let directory = std::path::PathBuf::from(std::env::var_os("QLEISLI_SIZED_CORPUS").unwrap());
    let manifest = std::fs::read_to_string(directory.join("cases.txt")).unwrap();
    for line in manifest.lines() {
        let fields: Vec<_> = line.split('|').collect();
        let [name, expected] = fields.as_slice() else {
            panic!("invalid corpus case")
        };
        let payload = std::fs::read(directory.join(format!("{name}.json"))).unwrap();
        match kernel.inspect(&payload) {
            Ok(checked) => {
                assert_eq!(*expected, "ok", "{name}");
                assert_eq!(checked.payload(), payload);
                println!(
                    "CORPUS|{name}|ok|{}|{}|{}",
                    checked.structural_work(),
                    checked.exact_work(),
                    checked.leaves().len()
                );
            }
            Err(error) => {
                println!("CORPUS|{name}|{}|{}", error.code, error.message);
                assert_eq!(error.code, *expected, "{name}: {error}");
            }
        }
    }
}

#[test]
#[ignore = "run through scripts/test_sized_qft.py with an audited native kernel"]
fn check_source_fourier_contracts() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let directory = std::path::PathBuf::from(std::env::var_os("QLEISLI_SIZED_QFT").unwrap());
    let manifest = std::fs::read_to_string(directory.join("cases.txt")).unwrap();
    for line in manifest.lines() {
        let fields: Vec<_> = line.split('|').collect();
        let [name, request, expected] = fields.as_slice() else {
            panic!("invalid Fourier source case")
        };
        let payload = std::fs::read(directory.join(format!("{name}.json"))).unwrap();
        let inspected = kernel.inspect(&payload).unwrap();
        println!(
            "SIZED-FOURIER|{name}|inspect|{}|{}",
            inspected.structural_work(),
            inspected.exact_work()
        );
        if request.is_empty() {
            continue;
        }
        let request = std::fs::read(directory.join(request)).unwrap();
        match kernel.check_against(&payload, &request) {
            Ok(checked) => {
                assert_eq!(*expected, "ok", "{name}");
                assert_eq!(checked.reconstruction().payload(), payload);
                assert_eq!(checked.request(), request);
                println!(
                    "SIZED-FOURIER|{name}|ok|{}|{}",
                    checked.reconstruction().structural_work(),
                    checked.reconstruction().exact_work()
                );
            }
            Err(error) => {
                assert_eq!(error.code, *expected, "{name}: {error}");
                println!("SIZED-FOURIER|{name}|{}", error.code);
            }
        }
    }
}

#[test]
#[ignore = "run through scripts/test_instrument_host.py with an audited native kernel"]
fn check_source_instrument_contracts() {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_HIERARCHY_KERNEL").unwrap());
    let directory = std::path::PathBuf::from(std::env::var_os("QLEISLI_SIZED_INSTRUMENT").unwrap());
    let manifest = std::fs::read_to_string(directory.join("cases.txt")).unwrap();
    for line in manifest.lines() {
        let fields: Vec<_> = line.split('|').collect();
        let [name, expected] = fields.as_slice() else {
            panic!("invalid instrument source case")
        };
        let payload = std::fs::read(directory.join(format!("{name}.json"))).unwrap();
        let request = std::fs::read(directory.join(format!("{name}.request.json"))).unwrap();
        match kernel.check_instrument(&payload, &request) {
            Ok(checked) => {
                assert_eq!(*expected, "ok", "{name}");
                assert_eq!(checked.reconstruction().payload(), payload);
                assert_eq!(checked.request(), request);
                println!(
                    "INSTRUMENT|{name}|ok|{}|{}",
                    checked.reconstruction().structural_work(),
                    checked.reconstruction().exact_work(),
                );
            }
            Err(error) => {
                assert_eq!(error.code, *expected, "{name}: {error}");
                println!("INSTRUMENT|{name}|{}", error.code);
            }
        }
    }
}
