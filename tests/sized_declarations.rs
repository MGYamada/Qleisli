//! Independent bounded source and native regressions for sized declarations.
//! These are executable counterexamples/oracles, not source-preservation proofs.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, check_project};
use qleisli::frontend::compile::{HierarchyProposal, OperationBinding, ParsedProgram};
use qleisli::interchange::hierarchical::{Kernel, execution::ExecutionLimits};
use std::collections::BTreeMap;
use std::path::Path;

fn sources(case: &str) -> BTreeMap<String, String> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/frontend_v030/ordinary-type-cutover/current/frontend_v030/sized-declarations-independent/sources")
        .join(case);
    std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "qli"))
        .map(|path| {
            (
                path.file_stem().unwrap().to_str().unwrap().to_owned(),
                std::fs::read_to_string(common::current_namespace_fixture(&path)).unwrap(),
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
    assert_eq!(
        &inputs["main"][error.span().start..error.span().end],
        "hidden"
    );
}

#[test]
fn every_unused_sibling_is_checked_including_dead_static_arms_and_empty_folds() {
    for (case, code) in [
        ("unused-type", "type"),
        ("unused-owner", "ownership"),
        ("unused-static-arm", "ownership"),
        ("zero-fold-capture", "ownership"),
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
fn first_invalid_sibling_follows_source_order_not_sorted_definition_identity() {
    let inputs = sources("source-order-errors");
    let error = ParsedProgram::parse(inputs.clone()).unwrap_err();
    assert_eq!(error.code(), "type", "{error}");
    assert_eq!(error.module(), Some("main"));
    assert!(error.span().start > inputs["main"].find("fn z_bad").unwrap());
    assert!(error.span().end < inputs["main"].find("fn a_bad").unwrap());
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
        (
            "collision",
            "name",
            "name `gate` collides with another declaration or import",
        ),
        (
            "ambiguous-import",
            "name",
            "name `gate` collides with another declaration or import",
        ),
        ("duplicate", "name", "duplicate declaration"),
        ("rename", "parse", "expected `;`"),
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
        } else if matches!(case, "collision" | "ambiguous-import") {
            assert_eq!(
                &inputs["main"][error.span().start..error.span().end],
                "gate"
            );
        }
    }
}

#[test]
fn direct_formal_adjoint_and_controlled_slots_are_usable() {
    let inverse = "pub fn inverse[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Adjoint(U){inverse(U)(q)} pub fn main()->Unit{()}";
    check_project(&SourceRoot::new(inverse).0).unwrap();
    ParsedProgram::parse(BTreeMap::from([("main".into(), inverse.into())])).unwrap();

    // Both finite spellings reach the same declared Controlled slot. The
    // canonical application below also drives the independent native oracle.
    let finite_control = "fn identity(q:Q<Bit>)->Q<Bit>{q} pub fn control[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controlled(U){qif(c,q){0=>identity,1=>U}} pub fn main()->Unit{()}";
    check_project(&SourceRoot::new(finite_control).0).unwrap();
    let control = "pub fn control[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controlled(U){controlled(U)(c,q)} pub fn main()->Unit{()}";
    check_project(&SourceRoot::new(control).0).unwrap();

    // This selected-only ordinary provider is T = diag(1, exp(i*pi/4)).
    // Expected coefficients below come from that equation, independently of
    // producer meanings. Neither formal receives the other access slots.
    let provider = "use std::quantum::phase; fn rotate(q:Q<Bit>)->Q<Bit>{phase[1,3](q)} ";
    let (sine, cosine) = std::f64::consts::FRAC_PI_4.sin_cos();
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
    for (declaration, entry, system_dimension) in
        [(inverse, "main::inverse", 2), (control, "main::control", 4)]
    {
        let source = format!("{provider}{declaration}");
        let program =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap();
        let elaborated = program
            .instantiate(
                entry,
                BTreeMap::new(),
                BTreeMap::from([(
                    "U".into(),
                    OperationBinding::new("main::rotate", BTreeMap::new()),
                )]),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        assert!(
            elaborated
                .definitions()
                .iter()
                .any(|definition| definition.path() == "main::rotate")
        );
        let proposal = elaborated.lower().unwrap();
        assert_eq!(
            proposal.source().instantiation().program().source("main"),
            Some(source.as_str())
        );
        let input = &input[..system_dimension * 2];
        let mut expected = input.to_vec();
        for reference in 0..2 {
            for basis in 0..system_dimension {
                let index = reference * system_dimension + basis;
                let [real, imaginary] = input[index];
                // Control is the first owner/low axis, target the second.
                expected[index] = match (system_dimension, basis) {
                    (2, 1) => [
                        cosine * real + sine * imaginary,
                        cosine * imaginary - sine * real,
                    ],
                    (4, 3) => [
                        cosine * real - sine * imaginary,
                        sine * real + cosine * imaginary,
                    ],
                    _ => [real, imaginary],
                };
            }
        }
        assert_amplitudes(&execute(&proposal, input), &expected);
    }
}

#[test]
fn private_unused_formals_cannot_borrow_adjoint_or_controlled_access() {
    let inverse = "fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){inverse(U)(q)} pub fn main()->Unit{()}";
    let finite_error = check_project(&SourceRoot::new(inverse).0).unwrap_err();
    assert_eq!(finite_error.code, ErrorCode::Capability, "{finite_error}");
    assert_eq!(finite_error.message, "missing Adjoint operation access");
    let target = inverse.rfind("inverse(U)(q)").unwrap();
    assert_eq!(
        (finite_error.span.start, finite_error.span.end),
        (target, target + "inverse(U)(q)".len())
    );
    for (source, access, use_text) in [
        (inverse, "Adjoint", "inverse(U)(q)"),
        (
            "fn unused[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Apply(U){controlled(U)(c,q)} pub fn main()->Unit{()}",
            "Controlled",
            "controlled(U)(c,q)",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "access", "{error}");
        assert_eq!(
            error.message(),
            format!("missing {access} operation access")
        );
        assert_eq!(error.module(), Some("main"));
        let start = source.rfind(use_text).unwrap();
        assert_eq!(
            (error.span().start, error.span().end),
            (start, start + use_text.len())
        );
    }
    let finite_control = "fn identity(q:Q<Bit>)->Q<Bit>{q} fn unused[const U:Op<Bit>](c:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Apply(U){qif(c,q){0=>identity,1=>U}} pub fn main()->Unit{()}";
    let error = check_project(&SourceRoot::new(finite_control).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Capability, "{error}");
    assert_eq!(error.message, "missing Controlled operation access");
    let start = finite_control.find("1=>U").unwrap() + "1=>".len();
    assert_eq!((error.span.start, error.span.end), (start, start + 1));
}

#[test]
fn both_source_consumers_check_dead_arms_and_zero_folds_for_missing_access() {
    // Complete source checking precedes either consumer's concrete eligibility.
    for (parameters, result, body, access, use_text) in [
        (
            "q:Q<Bit>",
            "Q<Bit>",
            "if static 0 == 0 {q} else {inverse(U)(q)}",
            "Adjoint",
            "inverse(U)(q)",
        ),
        (
            "q:Q<Bit>",
            "Q<Bit>",
            "qfor static i in 0..0 carry a=q {yield inverse(U)(a)}",
            "Adjoint",
            "inverse(U)(a)",
        ),
        (
            "c:Q<Bit>,q:Q<Bit>",
            "(Q<Bit>,Q<Bit>)",
            "if static 0 == 0 {(c,q)} else {controlled(U)(c,q)}",
            "Controlled",
            "controlled(U)(c,q)",
        ),
        (
            "c:Q<Bit>,q:Q<Bit>",
            "(Q<Bit>,Q<Bit>)",
            "qfor static i in 0..0 carry pair=(c,q) {let (c,q)=pair; yield controlled(U)(c,q)}",
            "Controlled",
            "controlled(U)(c,q)",
        ),
    ] {
        let source = format!(
            "fn unused[const U:Op<Bit>]({parameters})->{result} requires Apply(U){{{body}}} pub fn main()->Unit{{()}}"
        );
        let finite_error = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(finite_error.code, ErrorCode::Capability, "{finite_error}");
        assert_eq!(
            finite_error.message,
            format!("missing {access} operation access")
        );
        let start = source.rfind(use_text).unwrap();
        assert_eq!(
            (finite_error.span.start, finite_error.span.end),
            (start, start + use_text.len())
        );
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(error.code(), "access", "{error}");
        assert_eq!(
            error.message(),
            format!("missing {access} operation access")
        );
        assert_eq!(error.module(), Some("main"));
        let start = source.rfind(use_text).unwrap();
        assert_eq!(
            (error.span().start, error.span().end),
            (start, start + use_text.len())
        );
    }
}

#[test]
fn duplicate_adjoint_and_controlled_slots_share_the_requirement_location() {
    for access in ["Adjoint", "Controlled"] {
        let source = format!(
            "fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires {access}(U),{access}(U){{q}} pub fn main()->Unit{{()}}"
        );
        let second = source.rfind(&format!("{access}(U)")).unwrap();
        let finite_error = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(finite_error.code, ErrorCode::Capability, "{finite_error}");
        assert_eq!(
            finite_error.message,
            "duplicate operation access requirement"
        );
        assert_eq!(
            (finite_error.span.start, finite_error.span.end),
            (second, second + access.len())
        );
        let selected_error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source)])).unwrap_err();
        assert_eq!(selected_error.code(), "access", "{selected_error}");
        assert_eq!(
            selected_error.message(),
            "duplicate operation access requirement"
        );
        assert_eq!(selected_error.module(), Some("main"));
        assert_eq!(
            (selected_error.span().start, selected_error.span().end),
            (second, second + access.len())
        );
    }
}
