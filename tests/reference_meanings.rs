//! Artifact-bound reference Meaning formation and concrete adapter regressions.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::contract::{
    DEFAULT_EXACT_WORK,
    exact::{Budget, Exact, Matrix},
};
use qleisli::frontend::compile::{ParsedProgram, compile_project};
use qleisli::interchange::{hierarchical, native::Kernel};
use qleisli::ir::{CircuitAction, RawOp};
use std::collections::BTreeMap;

const IMPORTS: &str = "use std::quantum::h; use std::quantum::z; use std::quantum::x;
    use std::quantum::init0; use std::quantum::join; use std::quantum::split;
    use std::observe::measure_z;";

fn parse(source: &str) -> Result<ParsedProgram, qleisli::frontend::compile::Error> {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())]))
}

fn matrix(source: &str) -> Matrix {
    let root = SourceRoot::new(source);
    let accepted = compile_project(&root.0).unwrap_or_else(|e| panic!("{e}\n{source}"));
    let receipt = accepted
        .program()
        .operations
        .iter()
        .find_map(|op| {
            if let RawOp::ApplyUnitary { steps, .. } = op {
                steps.iter().find_map(|step| {
                    if let CircuitAction::Contract { evidence, .. } = &step.action {
                        Some(evidence)
                    } else {
                        None
                    }
                })
            } else {
                None
            }
        })
        .expect("actual emitted contract receipt");
    assert!(
        receipt
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "main" && text == source)
    );
    assert_eq!(receipt.specification().quantum_inputs.len(), 1);
    let ordinary = receipt.meaning().clone();
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let selected = parse(source)
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let raw = if selected.has_operation_meanings() {
        selected
            .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap()
            .lower_raw(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap()
    } else {
        selected
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap()
    };
    let accepted = kernel.accept(raw.proposal()).unwrap();
    raw.validate_source_steps(&accepted).unwrap();
    let selected = accepted
        .raw()
        .operations
        .iter()
        .find_map(|op| match op {
            RawOp::ApplyUnitary { steps, .. } => steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. } => Some(evidence),
                _ => None,
            }),
            _ => None,
        })
        .expect("selected emitted original reference receipt");
    assert!(
        selected
            .identity()
            .sources
            .iter()
            .any(|(name, text)| name == "main" && text == source)
    );
    assert_eq!(selected.meaning(), &ordinary);
    ordinary
}

#[test]
fn reference_operation_bindings_retain_requests_in_raw_and_hierarchy() {
    let source = format!(
        "{IMPORTS}
        fn reference_h(q:Q<Bit>)->Q<Bit>{{h(q)}}
        meaning H:Bit=reference(reference_h);
        fn implementation(q:Q<Bit>)->Q<Bit>{{h(h(h(q)))}}
        fn client[const U:Op<Bit,H>](q:Q<Bit>)->Q<Bit> requires Applicable(U){{U(q)}}
        pub fn quantum_client(q:Q<Bit>)->Q<Bit>{{client[implementation](q)}}
        pub observe fn main()->Bit{{measure_z(quantum_client(init0()))}}"
    );
    let s = Exact::inv_sqrt2();
    assert_eq!(
        matrix(&source),
        Matrix::new(2, 2, vec![s, s, s, s.neg().unwrap()]).unwrap()
    );
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let selected = parse(&source)
        .unwrap()
        .instantiate("main::quantum_client", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let checked = selected
        .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let hierarchy = checked.lower_hierarchy().unwrap();
    hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap())
        .check_against_native(hierarchy.payload(), hierarchy.comparison_request())
        .unwrap();
    let wrong = source.replace("{h(h(h(q)))}", "{q}");
    assert_ne!(source, wrong);
    assert!(compile_project(&SourceRoot::new(&wrong).0).is_err());
    let selected = parse(&wrong)
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    assert_eq!(
        selected
            .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "contract"
    );
}

#[test]
fn reference_identity_is_retained_even_when_the_operator_is_monomial() {
    let source = format!(
        "{IMPORTS}
        fn reference(q:Q<Bit>)->Q<Bit>{{q}}
        meaning I:Bit=reference(reference);
        meaning II:Bit=compose(I,I);
        meaning Pair:(Bit,Bit)=tensor(I,I);
        pub fn main()->Bit{{0}}"
    );
    let parsed = parse(&source).unwrap();
    for name in ["main::I", "main::II", "main::Pair"] {
        let error = parsed.finite_meaning_target(name).unwrap_err();
        assert!(error.message().contains("monomial-only"), "{error}");
    }
    // `reference` remains an ordinary contextual identifier elsewhere.
    assert_eq!(
        matrix(&format!(
            "{IMPORTS}
        fn reference(q:Q<Bit>)->Q<Bit>{{q}}
        meaning I:Bit=reference(reference);
        pub observe fn main()->Bit{{measure_z(apply_contract(reference,I,init0()))}}"
        )),
        Matrix::identity(2).unwrap()
    );
}

#[test]
fn ordinary_reference_checks_exact_hadamard_and_rejects_probability_equivalence() {
    let prefix = format!(
        "{IMPORTS}
        meaning H:Bit=reference(reference_h);
        fn reference_h(q:Q<Bit>)->Q<Bit>{{h(q)}}"
    );
    let positive = format!(
        "{prefix}
        fn implementation(q:Q<Bit>)->Q<Bit>{{h(h(h(q)))}}
        pub observe fn main()->Bit{{measure_z(apply_contract(implementation,H,init0()))}}"
    );
    let s = Exact::inv_sqrt2();
    let m = s.neg().unwrap();
    assert_eq!(
        matrix(&positive),
        Matrix::new(2, 2, vec![s, s, s, m]).unwrap()
    );
    for body in ["q", "z(x(z(x(h(q)))))"] {
        let negative = format!(
            "{prefix}
            fn implementation(q:Q<Bit>)->Q<Bit>{{{body}}}
            observe fn main()->Bit{{measure_z(apply_contract(implementation,H,init0()))}}"
        );
        let root = SourceRoot::new(&negative);
        let error = compile_project(&root.0).unwrap_err();
        assert!(error.message.contains("contract"), "{error}");
    }
}

#[test]
fn mixed_composition_and_tensor_keep_order_and_low_axes() {
    let prefix = format!(
        "{IMPORTS}
        meaning H:Bit=reference(reference_h);
        fn reference_h(q:Q<Bit>)->Q<Bit>{{h(q)}}
        classical fn phase(b:Bit)->(Bit,(Bit,Bit)){{(0,(0,b))}}
        meaning Z:Bit=phase_by(phase);"
    );
    let s = Exact::inv_sqrt2();
    let m = s.neg().unwrap();
    for (target, body, expected) in [
        ("compose(Z,H)", "h(z(q))", vec![s, m, s, s]),
        ("compose(H,Z)", "z(h(q))", vec![s, s, m, s]),
    ] {
        let source = format!(
            "{prefix} meaning M:Bit={target};
            fn implementation(q:Q<Bit>)->Q<Bit>{{{body}}}
            pub observe fn main()->Bit{{measure_z(apply_contract(implementation,M,init0()))}}"
        );
        assert_eq!(matrix(&source), Matrix::new(2, 2, expected).unwrap());
    }
    for (target, body, expected) in [
        (
            "tensor(H,Z)",
            "join(h(a),z(b))",
            vec![
                s,
                s,
                Exact::zero(),
                Exact::zero(),
                s,
                m,
                Exact::zero(),
                Exact::zero(),
                Exact::zero(),
                Exact::zero(),
                m,
                m,
                Exact::zero(),
                Exact::zero(),
                m,
                s,
            ],
        ),
        (
            "tensor(Z,H)",
            "join(z(a),h(b))",
            vec![
                s,
                Exact::zero(),
                s,
                Exact::zero(),
                Exact::zero(),
                m,
                Exact::zero(),
                m,
                s,
                Exact::zero(),
                m,
                Exact::zero(),
                Exact::zero(),
                m,
                Exact::zero(),
                s,
            ],
        ),
    ] {
        let source = format!(
            "{prefix} meaning M:(Bit,Bit)={target};
            fn implementation(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{let(a,b)=split(q);{body}}}
            pub observe fn main()->(Bit,Bit){{
                let q=apply_contract(implementation,M,join(init0(),init0()));
                let(a,b)=split(q);(measure_z(a),measure_z(b))}}"
        );
        assert_eq!(matrix(&source), Matrix::new(4, 4, expected).unwrap());
    }
}

#[test]
fn unused_reference_rejects_wrong_category_unbound_statics_shape_and_effect() {
    for (source, code) in [
        (
            "static fn f()->Nat{0} meaning M:Bit=reference(f);",
            "static",
        ),
        (
            "classical fn f(b:Bit)->Bit{b} meaning M:Bit=reference(f);",
            "type",
        ),
        (
            "fn f[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)} meaning M:Bit=reference(f);",
            "type",
        ),
        (
            "fn f(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{q} meaning M:(Unit,Bit)=reference(f);",
            "type",
        ),
        (
            "use std::observe::reset; fn f(q:Q<Bit>)->Q<Bit>{reset(q)} meaning M:Bit=reference(f);",
            "effect",
        ),
        (
            "use std::quantum::{init0,finish}; fn f(q:Q<Unit>)->Q<Bit>{let ()=finish(q);init0()} meaning M:Unit=reference(f);",
            "type",
        ),
    ] {
        let error = parse(source).unwrap_err();
        assert_eq!(error.code(), code, "{error}\n{source}");
    }
}

#[test]
fn indirect_function_meaning_cycles_reject_before_concrete_emission() {
    for body in [
        "apply_contract(f,M,q)",
        "adjoint(checked_op(f,M))(q)",
        "qfor static i in 0..0 carry a=q {yield apply_contract(f,M,a);}",
    ] {
        let source = format!("fn f(q:Q<Bit>)->Q<Bit>{{{body}}} meaning M:Bit=reference(f);");
        let error = parse(&source).unwrap_err();
        assert_eq!(error.code(), "cycle", "{error}");
    }
}

#[test]
fn reference_arguments_and_visibility_are_exact() {
    for body in ["reference(f[1])", "reference(power(f,1))", "reference(f,f)"] {
        let source = format!("fn f(q:Q<Bit>)->Q<Bit>{{q}} meaning M:Bit={body};");
        assert_eq!(parse(&source).unwrap_err().code(), "parse");
    }
    let modules = |public: &str| {
        BTreeMap::from([
            (
                "dependency".into(),
                format!("{public} fn f(q:Q<Bit>)->Q<Bit>{{q}}"),
            ),
            (
                "main".into(),
                "use dependency::f; meaning M:Bit=reference(f);pub fn main()->Bit{0}".into(),
            ),
        ])
    };
    assert_eq!(
        ParsedProgram::parse(modules("")).unwrap_err().code(),
        "visibility"
    );
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let source = ParsedProgram::parse(modules("pub"))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    assert!(source.has_function_contracts());
    assert_eq!(source.lower_raw().unwrap_err().code(), "meaning");
    assert!(
        source
            .check_function_contracts(
                &Kernel::new("/absent-qleisli-reference-kernel"),
                &mut Budget::new(DEFAULT_EXACT_WORK)
            )
            .is_err()
    );
    assert_eq!(
        source
            .check_function_contracts(&kernel, &mut Budget::new(1))
            .unwrap_err()
            .code(),
        "limit"
    );
    let checked = source
        .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let raw = checked.lower_raw().unwrap();
    raw.validate_source_steps(&kernel.accept(raw.proposal()).unwrap())
        .unwrap();
}

#[test]
fn reference_does_not_erase_unused_generic_or_zero_repeat_lying_contracts() {
    let prefix = format!(
        "{IMPORTS}
        fn reference_h(q:Q<Bit>)->Q<Bit>{{h(q)}} meaning H:Bit=reference(reference_h);
        fn liar(q:Q<Bit>)->Q<Bit>{{q}}"
    );
    for declarations in [
        "fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{apply_contract(liar,H,q)}
         pub observe fn main()->Bit{measure_z(init0())}",
        "pub observe fn main()->Bit{measure_z(adjoint(power(checked_op(liar,H),0))(init0()))}",
    ] {
        let text = format!("{prefix}{declarations}");
        assert_eq!(
            compile_project(&SourceRoot::new(&text).0).unwrap_err().code,
            qleisli::frontend::compile::ErrorCode::Contract
        );
        let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
        let source = parse(&text)
            .unwrap()
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let error =
            match source.check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK)) {
                Err(error) => error,
                Ok(checked) => checked
                    .check_operation_meanings(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap_err(),
            };
        assert_eq!(error.code(), "contract", "{error}");
    }
}

#[test]
fn reference_receipts_survive_existing_inverse_and_control_access() {
    let prefix = format!(
        "{IMPORTS}
        fn reference_h(q:Q<Bit>)->Q<Bit>{{h(q)}}
        meaning H:Bit=reference(reference_h);
        fn implementation(q:Q<Bit>)->Q<Bit>{{h(h(h(q)))}}"
    );
    let s = Exact::inv_sqrt2();
    let expected = Matrix::new(2, 2, vec![s, s, s, s.neg().unwrap()]).unwrap();
    for main in [
        "pub observe fn main()->Bit{measure_z(adjoint(checked_op(implementation,H))(init0()))}",
        "pub observe fn main()->(Bit,Bit){let(c,q)=controlled(checked_op(implementation,H))(init0(),init0());(measure_z(c),measure_z(q))}",
    ] {
        assert_eq!(matrix(&format!("{prefix}{main}")), expected);
    }
}

#[test]
fn scalar_unit_reference_keeps_exact_phase_and_zero_axis_owner() {
    let source = "use std::quantum::{unit,finish,phase_eighth};
        fn scalar(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}
        meaning S:Unit=reference(scalar);
        fn implementation(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}
        pub fn main()->Bit{let q=apply_contract(implementation,S,unit(()));finish(q);0}";
    assert_eq!(
        matrix(source),
        Matrix::new(1, 1, vec![Exact::new([0, 1, 0, 1], 1).unwrap()]).unwrap()
    );
    let wrong = source.replace(
        "fn implementation(q:Q<Unit>)->Q<Unit>{phase_eighth(q)}",
        "fn implementation(q:Q<Unit>)->Q<Unit>{q}",
    );
    assert!(compile_project(&SourceRoot::new(&wrong).0).is_err());
    let kernel = Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    let selected = parse(&wrong)
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    assert_eq!(
        selected
            .check_function_contracts(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "contract"
    );
}
