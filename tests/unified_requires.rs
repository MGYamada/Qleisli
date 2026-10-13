//! Mixed requires obligations, exact specialization identity and bounded checks.
//! These regressions do not establish generic or source-preservation theorems.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0
use qleisli::contract::{ContractError, DEFAULT_EXACT_WORK, FunctionEvidence, exact::Budget};
use qleisli::frontend::compile::{
    BasisBinding, ElaboratedProgram, OperationBinding, ParsedProgram,
};
use qleisli::interchange::{hierarchical, native::Kernel};
use qleisli::ir::{CircuitAction, RawOp, RawProgram};
use std::collections::BTreeMap;
use std::sync::Arc;

const MIXED: &str = "
pub unitary fn identity[const B:Basis,const p:Nat](q:Q<B>)->Q<B>
requires p >= 1, p <= 2 {q}
pub unitary fn generic[const A:Basis,const n:Nat,const U:Op<A>](q:Q<A>)->Q<A>
requires n >= 1, n <= 2, Applicable(U) {
    qfor static i in 0..n carry r=q {yield U(r);}
}
pub unitary fn forward[const A:Basis,const n:Nat,const U:Op<A>](q:Q<A>)->Q<A>
requires Applicable(U), n <= 2, n >= 1 {generic[A,n,U](q)}";

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

fn naturals(name: &str, value: u32) -> BTreeMap<String, u32> {
    BTreeMap::from([(name.into(), value)])
}

fn types(name: &str, source: &str) -> BTreeMap<String, BasisBinding> {
    BTreeMap::from([(name.into(), BasisBinding::parse(source).unwrap())])
}

fn mixed(program: &ParsedProgram, entry: &str, basis: &str, n: u32) -> ElaboratedProgram {
    program
        .instantiate_with_types(
            entry,
            types("A", basis),
            naturals("n", n),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::with_types("main::identity", types("B", basis), naturals("p", 1)),
            )]),
        )
        .unwrap()
        .elaborate()
        .unwrap()
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn mixed_symbolic_forwarding_preserves_exact_basis_and_reference_coefficients() {
    let program = parsed(MIXED);
    let kernel = hierarchical::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap());
    // Unequal complex reference slices expose phase and axis changes. All
    // selected Basis trees below have one wire, but retain distinct types.
    let input = [[0.25, -0.5], [0.75, 1.0], [-1.25, 1.5], [1.75, -2.0]];
    for basis in ["Bit", "Bits<1>", "(Unit,Bit)"] {
        for n in [1, 2] {
            let source = mixed(&program, "main::forward", basis, n);
            let root = &source.definitions()[source.root()];
            assert_eq!(root.types()["A"], BasisBinding::parse(basis).unwrap());
            assert_eq!(root.naturals()["n"], n);
            assert_eq!(root.inputs()[0].ty(), root.output().ty());
            let proposal = source.lower().unwrap();
            let repeated = mixed(&program.clone(), "main::forward", basis, n)
                .lower()
                .unwrap();
            assert_eq!(proposal.payload(), repeated.payload());
            assert_eq!(proposal.comparison_request(), repeated.comparison_request());
            let checked = kernel
                .check_against_native(proposal.payload(), proposal.comparison_request())
                .unwrap();
            let output = checked
                .execute_pure(
                    &input,
                    2,
                    hierarchical::execution::ExecutionLimits {
                        max_amplitudes: 16,
                        max_steps: 100,
                    },
                )
                .unwrap();
            assert_eq!(output.amplitudes, input);
        }
    }
}

#[test]
fn absent_numeric_or_access_obligations_reject_even_unused_or_empty_bodies() {
    let missing_numeric = MIXED.replace(
        "requires Applicable(U), n <= 2, n >= 1 {generic[A,n,U](q)}",
        "requires Applicable(U), n <= 2 {generic[A,n,U](q)}",
    );
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), missing_numeric.clone())]))
        .unwrap_err();
    assert_eq!(error.code(), "size");
    assert_eq!(error.module(), Some("main"));
    assert_eq!(
        error.span().start,
        missing_numeric.find("generic[A,n,U](q)").unwrap()
    );
    assert!(error.message().contains("callee natural premise"));
    for (grant, body) in [
        ("", "U(q)"),
        (", Controllable(U)", "U(q)"),
        ("", "qfor static i in 0..0 carry r=q {yield U(r);}"),
        ("", "if static 0 == 0 {q} else {U(q)}"),
    ] {
        let source = format!(
            "pub unitary fn unused[const A:Basis,const n:Nat,const U:Op<A>](q:Q<A>)->Q<A>
             requires n >= 1, n <= 2{grant} {{{body}}}"
        );
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(error.code(), "access", "{source}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(error.span().start >= source.find(body).unwrap());
    }
}

#[test]
fn simple_comparisons_commute_but_subtraction_requires_an_earlier_guard() {
    for requirements in [
        "n >= 1, n <= 2, Applicable(U)",
        "n <= 2, Applicable(U), n >= 1",
        "n >= 1, Applicable(U), n-1 <= 1",
    ] {
        let source = MIXED.replace("n >= 1, n <= 2, Applicable(U)", requirements);
        mixed(&parsed(&source), "main::generic", "Bit", 1);
    }
    let source = MIXED.replace(
        "n >= 1, n <= 2, Applicable(U)",
        "n-1 <= 1, n >= 1, Applicable(U)",
    );
    let error =
        ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
    assert_eq!(error.code(), "size");
    assert_eq!(&source[error.span().start..error.span().end], "n-1");
    assert!(error.message().contains("nonnegative guard"));
}

#[test]
fn each_closed_comparison_rejects_at_its_original_predicate() {
    for (comparison, right, good, bad) in [
        ("==", 1, 1, 0),
        ("!=", 1, 0, 1),
        ("<", 2, 1, 2),
        ("<=", 2, 2, 3),
        (">", 0, 1, 0),
        (">=", 1, 1, 0),
    ] {
        let predicate = format!("n {comparison} {right}");
        let source = format!(
            "pub unitary fn guarded[const n:Nat](q:Q<Bit>)->Q<Bit> requires {predicate} {{q}}"
        );
        let program = parsed(&source);
        program
            .instantiate("main::guarded", naturals("n", good), BTreeMap::new())
            .unwrap();
        let error = program
            .instantiate("main::guarded", naturals("n", bad), BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.code(), "size", "{predicate}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert_eq!(&source[error.span().start..error.span().end], predicate);
        assert!(error.message().contains("entry main::guarded"), "{error}");
        assert!(
            error
                .message()
                .contains(&format!("evaluated {bad} {comparison} {right}")),
            "{error}"
        );
    }
}

#[test]
fn false_entry_and_provider_premises_precede_concrete_materialization() {
    let source = "pub unitary fn bounded[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>
        requires n >= 1, n <= 2 {q}";
    let program = parsed(source);
    // Nine is an invalid closed interface description, never a generated or
    // simulated maximum-size quantum program. Its false premise must win.
    for (n, predicate) in [(0, "n >= 1"), (9, "n <= 2")] {
        let error = program
            .instantiate("main::bounded", naturals("n", n), BTreeMap::new())
            .unwrap_err();
        assert_eq!(error.code(), "size");
        assert_eq!(&source[error.span().start..error.span().end], predicate);
    }
    let provider = "pub unitary fn gate[const m:Nat](q:Q<Bit>)->Q<Bit> requires m == 1 {q}";
    let main =
        "pub unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}";
    let program = ParsedProgram::parse(BTreeMap::from([
        ("main".into(), main.into()),
        ("providers".into(), provider.into()),
    ]))
    .unwrap();
    let error = program
        .instantiate(
            "main::invoke",
            BTreeMap::new(),
            BTreeMap::from([(
                "U".into(),
                OperationBinding::new("providers::gate", naturals("m", 0)),
            )]),
        )
        .unwrap_err();
    assert_eq!(error.code(), "size");
    assert_eq!(error.module(), Some("providers"));
    assert_eq!(&provider[error.span().start..error.span().end], "m == 1");
    assert!(
        error
            .message()
            .contains("operation U provider providers::gate"),
        "{error}"
    );
    assert!(error.message().contains("evaluated 0 == 1"), "{error}");
}

#[test]
fn invalid_arithmetic_and_unbounded_requirement_forms_do_not_gain_acceptance() {
    for (predicate, code) in [
        ("n*n <= 2", "unsupported"),
        ("0-1 <= n", "size"),
        ("170141183460469231731687303715884105727+1 >= n", "limit"),
        ("n >= 1 && n <= 2", "parse"),
        ("n >= 1 || n <= 2", "parse"),
    ] {
        let source =
            format!("pub unitary fn f[const n:Nat](q:Q<Bit>)->Q<Bit> requires {predicate} {{q}}");
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(error.code(), code, "{source}: {error}");
    }
    let source = "pub unitary fn f[const n:Nat]()->Bit {static let next=n+1;0}";
    let error = parsed(source)
        .instantiate("main::f", naturals("n", u32::MAX), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "limit");
}

#[test]
fn specialization_keys_keep_nat_provider_and_exact_type_separate() {
    let source = format!(
        "{MIXED}
        use std::quantum::x;
        pub unitary fn flip(q:Q<Bit>)->Q<Bit>{{x(q)}}
        pub unitary fn host(a:Q<Bit>,b:Q<Bit>,c:Q<Bits<1>>,d:Q<Bit>,e:Q<Bit>)
          ->(Q<Bit>,Q<Bit>,Q<Bits<1>>,Q<Bit>,Q<Bit>) {{
            (generic[type(Bit),1,identity[type(Bit),1]](a),
             generic[type(Bit),2,identity[type(Bit),1]](b),
             generic[type(Bits<1>),1,identity[type(Bits<1>),1]](c),
             generic[type(Bit),1,flip](d),
             generic[type(Bit),1,identity[type(Bit),1]](e))
        }}"
    );
    let elaborated = parsed(&source)
        .instantiate("main::host", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let definitions = elaborated.definitions();
    let generic = definitions
        .iter()
        .filter(|d| d.path() == "main::generic")
        .collect::<Vec<_>>();
    assert_eq!(
        generic.len(),
        4,
        "identical reuse shares one instance; each changed binding remains distinct"
    );
    for (basis, n, provider) in [
        ("Bit", 1, "main::identity"),
        ("Bit", 2, "main::identity"),
        ("Bits<1>", 1, "main::identity"),
        ("Bit", 1, "main::flip"),
    ] {
        assert_eq!(
            generic
                .iter()
                .filter(|d| d.types()["A"] == BasisBinding::parse(basis).unwrap()
                    && d.naturals()["n"] == n
                    && definitions[d.operations()["U"].definition().unwrap()].path() == provider)
                .count(),
            1
        );
    }
}

fn receipt(raw: &RawProgram) -> &FunctionEvidence {
    raw.operations
        .iter()
        .find_map(|operation| match operation {
            RawOp::ApplyUnitary { steps, .. } => steps.iter().find_map(|step| match &step.action {
                CircuitAction::Contract { evidence, .. } => Some(evidence.as_ref()),
                _ => None,
            }),
            _ => None,
        })
        .expect("the actual emitted function-contract receipt")
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn requires_only_source_replacement_cannot_reuse_old_function_evidence() {
    let first = "use std::quantum::h;
        unitary fn implementation(q:Q<Bit>)->Q<Bit>{h(h(q))}
        unitary fn specified(q:Q<Bit>)->Q<Bit>{q}
        pub unitary fn guarded[const n:Nat](q:Q<Bit>)->Q<Bit>
        requires n >= 1 {apply_contract(implementation,specified,q)}";
    let second = first.replace("n >= 1", "n >= 2");
    let old = parsed(first);
    let new = parsed(&second);
    assert_eq!(old.source("main"), Some(first));
    assert_eq!(new.source("main"), Some(second.as_str()));
    old.instantiate("main::guarded", naturals("n", 1), BTreeMap::new())
        .unwrap();
    assert_eq!(
        new.instantiate("main::guarded", naturals("n", 1), BTreeMap::new())
            .unwrap_err()
            .code(),
        "size"
    );
    let kernel = Kernel::selected().unwrap();
    let prepare = |program: &ParsedProgram| {
        program
            .instantiate("main::guarded", naturals("n", 2), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap()
    };
    let old_proposal = prepare(&old);
    let new_proposal = prepare(&new);
    let old_checked = kernel.accept(old_proposal.proposal()).unwrap();
    let new_checked = kernel.accept(new_proposal.proposal()).unwrap();
    let old_receipt = receipt(old_checked.raw());
    let new_receipt = receipt(new_checked.raw());
    assert_eq!(old_receipt.meaning(), new_receipt.meaning());
    assert_eq!(old_receipt.implementation(), new_receipt.implementation());
    assert_eq!(old_receipt.specification(), new_receipt.specification());
    assert_ne!(old_receipt.identity(), new_receipt.identity());
    assert_eq!(
        old_receipt.check_binding(
            new_receipt.signature(),
            new_receipt.identity(),
            new_receipt.implementation(),
            new_receipt.specification()
        ),
        Err(ContractError::EvidenceMismatch)
    );
    let mut stale = new_checked.raw().clone();
    let mut replaced = 0;
    for operation in &mut stale.operations {
        if let RawOp::ApplyUnitary { steps, .. } = operation {
            for step in steps {
                if let CircuitAction::Contract { evidence, .. } = &mut step.action {
                    *evidence = Arc::new(old_receipt.clone());
                    replaced += 1;
                }
            }
        }
    }
    assert_eq!(replaced, 1);
    // Exact IR validity of equal bodies cannot authorize a changed source's
    // retained receipt. The source attachment gate must independently refuse.
    let stale = kernel.accept_raw(stale).unwrap();
    assert!(new_proposal.validate_source_steps(&stale).is_err());
    new_proposal.validate_source_steps(&new_checked).unwrap();
}
