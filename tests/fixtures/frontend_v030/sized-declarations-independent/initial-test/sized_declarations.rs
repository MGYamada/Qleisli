//! Independent bounded source and native regressions for sized declarations.
//! These are executable counterexamples/oracles, not source-preservation proofs.
use qleisli::frontend::sized::{HierarchyProposal, OperationBinding, ParsedProgram};
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;
use std::path::Path;

fn sources(case: &str) -> BTreeMap<String, String> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/sized-declarations-independent/sources")
        .join(case);
    std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "qli"))
        .map(|path| {
            (
                path.file_stem().unwrap().to_str().unwrap().to_owned(),
                std::fs::read_to_string(path).unwrap(),
            )
        })
        .collect()
}

fn prepare(case: &str) -> ParsedProgram {
    // Retained declaration identities must survive moving and cloning the owner.
    let parsed = ParsedProgram::parse(sources(case)).unwrap();
    let cloned = parsed.clone();
    drop(parsed);
    cloned
}

fn execute(proposal: &HierarchyProposal, input: &[[f64; 2]]) -> Vec<[f64; 2]> {
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"));
    let checked = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    assert_eq!(checked.payload(), proposal.payload());
    let output = checked
        .execute_pure(
            input,
            2,
            ExecutionLimits {
                max_amplitudes: 128,
                max_steps: 10_000,
            },
        )
        .unwrap();
    assert_eq!(output.reference_dimension, 2);
    output.amplitudes
}

fn assert_amplitudes(actual: &[[f64; 2]], expected: &[[f64; 2]]) {
    assert_eq!(actual.len(), expected.len());
    for (index, (actual, expected)) in actual.iter().zip(expected).enumerate() {
        for component in 0..2 {
            assert!(
                (actual[component] - expected[component]).abs() < 1e-11,
                "coefficient {index}, component {component}: {actual:?} != {expected:?}"
            );
        }
    }
}

#[test]
fn sibling_order_and_module_partition_preserve_phase_and_labelled_axes() {
    // Independent analytic meaning: |a>q|b>r -> i^a |b>first|a>second.
    // Unequal complex coefficients and two reference slices expose phase,
    // port-order and reference-axis errors without assuming separable inputs.
    let input = [
        [0.1, -0.2],
        [0.3, 0.4],
        [-0.5, 0.6],
        [0.7, -0.8],
        [-0.9, 0.2],
        [0.4, -0.3],
        [0.6, 0.1],
        [-0.2, -0.7],
    ];
    let mut expected = [[0.0; 2]; 8];
    for reference in 0..2 {
        for a in 0..2 {
            for b in 0..2 {
                let [real, imaginary] = input[reference * 4 + a + 2 * b];
                expected[reference * 4 + b + 2 * a] = if a == 0 {
                    [real, imaginary]
                } else {
                    [-imaginary, real]
                };
            }
        }
    }
    for case in ["phase-same", "phase-backward", "phase-split"] {
        let program = prepare(case);
        let elaborated = program
            .instantiate("main::z_entry", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        assert_eq!(
            elaborated.definitions()[elaborated.root()].path(),
            "main::z_entry"
        );
        let proposal = elaborated.lower().unwrap();
        for (module, source) in sources(case) {
            assert_eq!(
                proposal.source().instantiation().program().source(&module),
                Some(source.as_str())
            );
        }
        assert_amplitudes(&execute(&proposal, &input), &expected);
    }
}

#[test]
fn same_named_providers_keep_distinct_meanings_and_specialization_identity() {
    let program = prepare("providers");
    let input = [[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]];
    let mut previous_x = None;
    for provider in ["a::gate", "b::gate", "a::gate", "main::private_identity"] {
        let elaborated = program
            .instantiate(
                "main::z_client",
                BTreeMap::new(),
                BTreeMap::from([("U".into(), OperationBinding::new(provider, BTreeMap::new()))]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        assert!(
            elaborated
                .definitions()
                .iter()
                .any(|definition| definition.path() == provider)
        );
        let proposal = elaborated.lower().unwrap();
        let mut expected = input;
        for reference in 0..2 {
            match provider {
                "a::gate" => expected.swap(reference * 2, reference * 2 + 1),
                "b::gate" => {
                    let [real, imaginary] = input[reference * 2 + 1];
                    expected[reference * 2 + 1] = [-imaginary, real];
                }
                _ => {}
            }
        }
        assert_amplitudes(&execute(&proposal, &input), &expected);
        if provider == "a::gate" {
            if let Some(previous) = &previous_x {
                assert_eq!(proposal.payload(), previous);
            } else {
                previous_x = Some(proposal.payload().to_vec());
            }
        }
    }
}

#[test]
fn private_siblings_are_providers_but_not_host_entries_or_external_imports() {
    let program = prepare("providers");
    for private in ["main::private_identity", "a::z_helper", "b::a_helper"] {
        let error = program
            .instantiate(private, BTreeMap::new(), BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.code(), "visibility", "{error}");
        assert!(error.message().contains(private), "{error}");
    }
    program
        .instantiate("a::gate", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let error = program
        .instantiate(
            "main::z_client",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("a::z_helper", BTreeMap::new()),
            )]),
        )
        .unwrap_err();
    assert_eq!(error.code(), "visibility", "{error}");
    let inputs = sources("private-import");
    let error = ParsedProgram::parse(inputs.clone()).unwrap_err();
    assert_eq!(error.code(), "visibility", "{error}");
    assert_eq!(error.module(), Some("main"));
    assert!(inputs["main"][error.span().start..error.span().end].contains("dep::hidden"));
}

#[test]
fn every_unused_sibling_is_checked_including_dead_static_arms_and_empty_folds() {
    for (case, code) in [
        ("unused-type", "type"),
        ("unused-owner", "ownership"),
        ("unused-static-arm", "ownership"),
        ("zero-fold-capture", "name"),
    ] {
        let inputs = sources(case);
        let error = ParsedProgram::parse(inputs.clone()).unwrap_err();
        assert_eq!(error.code(), code, "{case}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(
            error.span().start >= inputs["main"].find("fn unused").unwrap(),
            "{case}: {error}"
        );
        assert!(error.span().end <= inputs["main"].len(), "{error}");
    }
}

#[test]
fn sibling_and_unused_provider_cycles_do_not_become_self_recursion() {
    for case in [
        "sibling-cycle",
        "unused-provider-cycle",
        "nondecreasing-recursion",
    ] {
        let error = ParsedProgram::parse(sources(case)).unwrap_err();
        assert_eq!(error.code(), "cycle", "{case}: {error}");
        assert_eq!(error.module(), Some("main"));
    }
    let elaborated = prepare("self-recursion")
        .instantiate(
            "main::f",
            BTreeMap::from([("n".into(), 2)]),
            BTreeMap::new(),
        )
        .unwrap()
        .elaborate()
        .unwrap();
    let mut naturals = elaborated
        .definitions()
        .iter()
        .filter(|definition| definition.path() == "main::f")
        .map(|definition| definition.naturals()["n"])
        .collect::<Vec<_>>();
    naturals.sort_unstable();
    assert_eq!(naturals, [0, 1, 2]);
    let input = [[0.1, -0.2], [0.3, 0.4], [-0.5, 0.6], [0.7, -0.8]];
    assert_amplitudes(&execute(&elaborated.lower().unwrap(), &input), &input);
}

#[test]
fn duplicate_and_import_alias_collisions_remain_located_rejections() {
    for (case, code, message) in [
        ("collision", "name", "import shadows"),
        ("duplicate", "name", "duplicate declaration"),
        ("rename", "parse", "expected ;"),
    ] {
        let inputs = sources(case);
        let error = ParsedProgram::parse(inputs.clone()).unwrap_err();
        assert_eq!(error.code(), code, "{case}: {error}");
        assert!(error.message().contains(message), "{case}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().start < error.span().end, "{error}");
        assert!(error.span().end <= inputs["main"].len(), "{error}");
        if case == "duplicate" {
            assert_eq!(error.span().start, inputs["main"].rfind("entry(").unwrap());
        }
    }
}
