//! Whole-owner exclusive calls through both public source paths.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;

use common::SourceRoot;
use qleisli::frontend::compile::{ErrorCode, ParsedProgram, check_project, compile_project};
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

const IMPORTS: &str = "use std::quantum::init0; use std::quantum::h;
    use std::quantum::x; use std::quantum::cnot; use std::observe::measure_z;";

fn selected(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

#[test]
fn selected_nonexecuted_control_obligations_refuse_before_transport() {
    for program in [
        "unitary fn unused(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
        "pub unitary fn main(q:Q<Bit>)->Q<Bit>{if static 0==0 {q}else{h(ctrl q);q}}",
        "pub unitary fn main(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry r=q {h(ctrl r);yield r;}}",
        "unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{power(oracle,0)(q)}",
        "unitary fn unused(q:Q<Bit>)->Q<Bit>{if 1 {h(ctrl q);q}else{q}}pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
    ] {
        let source = format!("use std::quantum::h;{program}");
        let concrete = selected(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        for error in [
            concrete
                .lower_raw()
                .map(|_| ())
                .expect_err("original ctrl obligation"),
            concrete
                .lower()
                .map(|_| ())
                .expect_err("original ctrl obligation"),
        ] {
            assert_eq!(error.code(), "unsupported", "{source}");
            assert_eq!(error.module(), Some("main"));
            let span = error.span();
            assert!(source[span.start..span.end].starts_with("h(ctrl "));
        }
    }
}

fn checked_raw(source: &str, entry: &str) -> qleisli::interchange::native::AcceptedProgram {
    let source = selected(source)
        .instantiate(entry, BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
    let proposal = source
        .lower_raw_with_kernel(
            &kernel,
            &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    accepted
}

#[test]
fn selected_control_checks_unused_closed_bodies_without_changing_the_entry() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    let kernel = Kernel::selected().unwrap();
    let ordinary = "pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}";
    let baseline = selected(ordinary)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    for unused in [
        "unitary fn unused(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}",
        "unitary fn oracle[const N:Nat](q:Q<Bit>)->Q<Bit>{z(ctrl q);q}
         unitary fn unused(q:Q<Bit>)->Q<Bit>{oracle[1](q)}",
        "unitary fn oracle[const N:Nat](q:Q<Bit>)->Q<Bit>{z(ctrl q);q}
         unitary fn unused(q:Q<Bit>)->Q<Bit>{oracle[1](q)}
         unitary fn other(q:Q<Bit>)->Q<Bit>{oracle[2](q)}",
    ] {
        let text = format!("use std::quantum::z;{unused}{ordinary}");
        let parsed = selected(&text);
        assert!(
            parsed
                .instantiate("main::unused", BTreeMap::new(), BTreeMap::new())
                .is_err()
        );
        let source = parsed
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let before = source.definitions().len();
        let mut budget = Budget::new(DEFAULT_EXACT_WORK);
        let proposal = source.lower_raw_with_kernel(&kernel, &mut budget).unwrap();
        assert_eq!(
            source.definitions().len(),
            before,
            "immutable original graph"
        );
        assert!(proposal.source().definitions().len() > before);
        assert_eq!(
            proposal.source().definitions()[proposal.source().root()].path(),
            "main::main"
        );
        assert_eq!(
            proposal.proposal().artifact(),
            baseline.proposal().artifact(),
            "unchanged execution root: {text}"
        );
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let spent = DEFAULT_EXACT_WORK - budget.remaining();
        assert_eq!(
            source
                .lower_raw_with_kernel(&kernel, &mut Budget::new(spent - 1))
                .unwrap_err()
                .code(),
            "limit"
        );
        assert_eq!(
            source
                .lower_raw_with_kernel(
                    &Kernel::new(env!("CARGO_MANIFEST_DIR")),
                    &mut Budget::new(DEFAULT_EXACT_WORK)
                )
                .unwrap_err()
                .code(),
            "io"
        );
        assert_eq!(source.lower_raw().unwrap_err().code(), "unsupported");
    }
}

#[test]
fn selected_control_audit_keeps_original_generic_branch_and_meaning_obligations() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    for (body, code) in [
        ("unitary fn unused[const N:Nat](q:Q<Bit>)->Q<Bit>{z(ctrl q);q}", "unsupported"),
        ("unitary fn unused(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}
          unitary fn bad(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}", "contract"),
        ("unitary fn oracle[const N:Nat](q:Q<Bit>)->Q<Bit>{h(ctrl q);q}
          unitary fn unused(q:Q<Bit>)->Q<Bit>{oracle[1](q)}", "contract"),
        ("unitary fn oracle[const N:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..N carry r=q{z(ctrl r);yield r;}}
          unitary fn unused(q:Q<Bit>)->Q<Bit>{oracle[0](q)}
          unitary fn other(q:Q<Bit>)->Q<Bit>{oracle[1](q)}", "unsupported"),
        ("unitary fn unused(q:Q<Bit>)->Q<Bit>{if static 0==0 {q}else{z(ctrl q);q}}", "unsupported"),
        ("classical fn flip(b:Bit)->Bit{not b}
          meaning Flip:Bit=permutation_by(flip);
          unitary fn identity(q:Q<Bit>)->Q<Bit>{q}
          unitary fn unused(q:Q<Bit>)->Q<Bit>{z(ctrl q);adjoint(checked_op(identity,Flip))(q)}", "meaning"),
    ] {
        let text = format!("use std::quantum::{{z,h}};{body}pub unitary fn main(q:Q<Bit>)->Q<Bit>{{q}}");
        let source = selected(&text).instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap().elaborate().unwrap();
        let error = source.lower_raw_with_kernel(&Kernel::selected().unwrap(), &mut Budget::new(DEFAULT_EXACT_WORK)).unwrap_err();
        assert_eq!(error.code(), code, "{text}: {error}");
        if code != "meaning" {
            assert_eq!(error.module(), Some("main"));
            assert!(["h(ctrl ", "z(ctrl "].iter().any(|prefix| text[error.span().start..error.span().end].starts_with(prefix)), "{error}");
        }
    }
    let parsed = ParsedProgram::parse(BTreeMap::from([
        (
            "main".into(),
            "pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}".into(),
        ),
        (
            "helper".into(),
            "use std::quantum::h;unitary fn unused(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}".into(),
        ),
    ]))
    .unwrap();
    let error = parsed
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw_with_kernel(
            &Kernel::selected().unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap_err();
    assert_eq!(error.code(), "contract");
    assert_eq!(error.module(), Some("helper"));
}

#[test]
fn selected_control_requires_checker_and_one_bounded_budget() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    let source = selected("use std::quantum::z;pub unitary fn main(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}")
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
    for limit in [0, 1, DEFAULT_EXACT_WORK + 1] {
        assert_eq!(
            source
                .lower_raw_with_kernel(&kernel, &mut Budget::new(limit))
                .unwrap_err()
                .code(),
            "limit"
        );
    }
    let unavailable = Kernel::new(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(
        source
            .lower_raw_with_kernel(&unavailable, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "io"
    );
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    source.lower_raw_with_kernel(&kernel, &mut budget).unwrap();
    let spent = DEFAULT_EXACT_WORK - budget.remaining();
    assert!(spent > 1);
    assert_eq!(
        source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(spent - 1))
            .unwrap_err()
            .code(),
        "limit"
    );
    // Reusing storage/budget does not reuse native acceptance or mutate roles.
    assert_eq!(source.lower_raw().unwrap_err().code(), "unsupported");
}

#[test]
fn selected_control_cannot_erase_inactive_original_calls_or_bad_zero_power_providers() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    for (body, code) in [
        (
            "unitary fn unused(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{q}",
            "contract",
        ),
        (
            "pub unitary fn main(q:Q<Bit>)->Q<Bit>{if static 0==0 {q}else{h(ctrl q);q}}",
            "unsupported",
        ),
        (
            "pub unitary fn main(q:Q<Bit>)->Q<Bit>{qfor static i in 0..0 carry r=q {h(ctrl r);yield r;}}",
            "unsupported",
        ),
        (
            "unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{power(oracle,0)(q)}",
            "contract",
        ),
        (
            "unitary fn oracle(q:Q<Bit>)->Q<Bit>{h(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{adjoint(oracle)(q)}",
            "contract",
        ),
        (
            "unitary fn oracle(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}pub unitary fn main(q:Q<Bit>)->Q<Bit>{adjoint(oracle)(q)}",
            "unsupported",
        ),
        (
            "unitary fn oracle[const N:Nat](q:Q<Bit>)->Q<Bit>{qfor static i in 0..N carry r=q {h(ctrl r);yield r;}}pub unitary fn main(q:Q<Bit>)->Q<Bit>{let q=oracle[0](q);oracle[1](q)}",
            "unsupported",
        ),
    ] {
        let text = format!("use std::quantum::{{h,z}};{body}");
        let source = selected(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let error = source
            .lower_raw_with_kernel(
                &Kernel::selected().unwrap(),
                &mut Budget::new(DEFAULT_EXACT_WORK),
            )
            .unwrap_err();
        assert_eq!(error.code(), code, "{text}: {error}");
        assert_eq!(error.module(), Some("main"));
        assert!(
            ["h(ctrl ", "z(ctrl "]
                .iter()
                .any(|prefix| text[error.span().start..error.span().end].starts_with(prefix)),
            "{text}: {error}"
        );
    }
}

#[test]
fn updated_owners_survive_nested_blocks_calls_and_measurement() {
    for (body, expected) in [
        ("let q=init0(); x(excl q); measure_z(q)", vec![true]),
        (
            "let q=init0(); h(excl q); h(excl q); x(excl q); measure_z(q)",
            vec![true],
        ),
        (
            "let c=init0(); let t=init0(); x(excl c); cnot(excl c,excl t); (measure_z(c),measure_z(t))",
            vec![true, true],
        ),
    ] {
        let output = if expected.len() == 1 {
            "Bit"
        } else {
            "(Bit,Bit)"
        };
        let source = format!("{IMPORTS} pub observe fn main()->{output}{{{body}}}");
        let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
        let proposal = selected(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap()
            .lower_raw()
            .unwrap();
        let concrete = Kernel::selected()
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        // These expected computational outcomes come from X/CNOT algebra,
        // independently of either frontend's ownership or lowering bookkeeping.
        for accepted in [&finite, &concrete] {
            let actual = run_closed(accepted, SimulationLimits::default()).unwrap();
            assert_eq!(actual.len(), 1, "{source}: {actual:?}");
            assert!((actual[&expected] - 1.0).abs() < 1e-12, "{source}");
        }
    }
}

#[test]
fn global_calls_preserve_exact_coefficient_and_external_reference() {
    let source = format!(
        "{IMPORTS}
        unitary fn flip(q:Q<Bit>)->Q<Bit>{{x(q)}}
        pub unitary fn apply(q:Q<Bit>)->Q<Bit>{{flip(excl q);q}}"
    );
    let proposal = selected(&source)
        .instantiate("main::apply", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let accepted = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = vec![[0.25, -0.5], [0.75, 0.125], [-0.25, 0.375], [0.5, -0.625]];
    let actual = accepted
        .execute_pure(
            &input,
            2,
            qleisli::interchange::hierarchical::execution::ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    // The system axis occupies the low bit. X toggles it while the
    // reference index (high bit) and each complex coefficient stay unchanged.
    assert_eq!(
        actual.amplitudes,
        (0..4).map(|i| input[i ^ 1]).collect::<Vec<_>>()
    );
}

#[test]
fn finite_nested_runtime_branch_retains_updated_owner() {
    let source = format!(
        "{IMPORTS} pub observe fn main()->Bit{{
        let q=init0();let u=if 1{{x(excl q);()}}else{{()}};measure_z(q)}}"
    );
    let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
    assert_eq!(
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
    // Runtime conditional preparation remains outside the existing selected
    // projection profile. Do not silently expand that unrelated contract.
    let error = selected(&source)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .expect_err("runtime conditional remains outside selected projection");
    assert_eq!(error.code(), "unsupported");
}

#[test]
fn overlap_spent_owner_wrong_interface_and_nonunitary_calls_refuse() {
    for body in [
        "let q=init0(); cnot(excl q,excl q);measure_z(q)",
        "let q=init0(); cnot(ctrl q,excl q);measure_z(q)",
        "let q=init0(); let b=measure_z(q);x(excl q);b",
        "let q=init0();measure_z(excl q);0",
        "let q=init0();bad(excl q);measure_z(q)",
        "let q=0;x(excl q);q",
    ] {
        let source = format!(
            "{IMPORTS}
            observe fn bad(q:Q<Bit>)->Q<Bit>{{let b=measure_z(q);init0()}}
            pub observe fn main()->Bit{{{body}}}"
        );
        assert!(
            check_project(&SourceRoot::new(&source).0).is_err(),
            "{source}"
        );
        assert!(
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).is_err(),
            "{source}"
        );
    }
}

#[test]
fn both_source_paths_preserve_ctrl_phase_kickback_and_an_entangled_reference() {
    for (body, expected) in [
        (
            "let c=init0();let t=init0();h(excl c);x(excl t);h(excl t);cnot(ctrl c,excl t);h(excl c);h(excl t);(measure_z(c),measure_z(t))",
            vec![true, true],
        ),
        (
            "let c=init0();let r=init0();let t=init0();h(excl c);cnot(excl c,excl r);x(excl t);h(excl t);cnot(ctrl c,excl t);cnot(excl c,excl r);h(excl c);h(excl t);(measure_z(c),measure_z(r),measure_z(t))",
            vec![true, false, true],
        ),
        (
            "let c=init0();let t=init0();x(excl t);cnot(ctrl t,excl c);(measure_z(c),measure_z(t))",
            vec![true, true],
        ),
    ] {
        let result = if expected.len() == 2 {
            "(Bit,Bit)"
        } else {
            "(Bit,Bit,Bit)"
        };
        let source = format!("{IMPORTS} pub observe fn main()->{result}{{{body}}}");
        let accepted = compile_project(&SourceRoot::new(&source).0).unwrap();
        let raw = checked_raw(&source, "main::main");
        for accepted in [&accepted, &raw] {
            let actual = run_closed(accepted, SimulationLimits::default()).unwrap();
            // X prepares |1>, H X prepares |->, and CNOT on |-> produces
            // phase kickback. Uncomputing the CNOT to r exposes that phase while
            // retaining its correlation: the expected output is exactly 101.
            assert!(
                (actual[&expected] - 1.0).abs() < 1e-12,
                "{source}: {actual:?}"
            );
            assert!(
                actual
                    .iter()
                    .filter(|(bits, _)| *bits != &expected)
                    .all(|(_, p)| *p < 1e-12)
            );
        }
        // Kernel-free preparation must still refuse control obligations;
        // checked lowering does not confer reusable native authority.
        assert_eq!(
            selected(&source)
                .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                .unwrap()
                .elaborate()
                .unwrap()
                .lower_raw()
                .unwrap_err()
                .code(),
            "unsupported"
        );
    }
}

#[test]
fn finite_ctrl_rejects_actual_sector_changes_and_unused_lying_calls() {
    for call in ["h(ctrl c)", "x(ctrl c)", "cnot(excl c,ctrl t)"] {
        let source = format!(
            "{IMPORTS} pub observe fn main()->(Bit,Bit){{let c=init0();let t=init0();{call};(measure_z(c),measure_z(t))}}"
        );
        let error = compile_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(error.code, ErrorCode::Contract, "{error}");
        assert!(error.message.contains("sector preservation"));
        assert!(error.message.contains("not read-only"));
        assert!(error.message.contains("phase kickback"));
        let source = selected(&source)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let error = source
            .lower_raw_with_kernel(
                &Kernel::selected().unwrap(),
                &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
            )
            .unwrap_err();
        assert_eq!(error.code(), "contract");
        assert!(error.message().contains("sector preservation"));
    }
    let source = format!(
        "{IMPORTS} unitary fn bad(q:Q<Bit>)->Q<Bit>{{h(ctrl q);q}} pub observe fn main()->Bit{{0}}"
    );
    assert_eq!(
        check_project(&SourceRoot::new(&source).0).unwrap_err().code,
        ErrorCode::Contract
    );
}

#[test]
fn finite_ctrl_checks_nested_calls_and_keeps_zero_width_phase() {
    let source=format!("{IMPORTS}
        unitary fn apply(c:Q<Bit>,t:Q<Bit>)->(Q<Bit>,Q<Bit>){{cnot(ctrl c,excl t);(c,t)}}
        pub observe fn main()->(Bit,Bit){{let c=init0();let t=init0();x(excl c);apply(ctrl c,excl t);(measure_z(c),measure_z(t))}}");
    let accepted = compile_project(&SourceRoot::new(&source).0).unwrap();
    assert!(
        (run_closed(&accepted, SimulationLimits::default()).unwrap()[&vec![true, true]] - 1.0)
            .abs()
            < 1e-12
    );
    let raw = checked_raw(&source, "main::main");
    assert!(
        (run_closed(&raw, SimulationLimits::default()).unwrap()[&vec![true, true]] - 1.0).abs()
            < 1e-12
    );
    let source = "use std::quantum::phase_eighth;pub unitary fn f(q:Q<Unit>)->Q<Unit>{phase_eighth(ctrl q);q}";
    check_project(&SourceRoot::new(source).0).unwrap();
    let raw = checked_raw(source, "main::f");
    assert_eq!(raw.raw().quantum_inputs.len(), 1);
    assert!(raw.raw().quantum_inputs[0].wires.is_empty());
    let root = SourceRoot::new(source);
    let unavailable = Kernel::new(env!("CARGO_MANIFEST_DIR"));
    let error = qleisli::frontend::compile::check_project_with_kernel(
        &root.0,
        qleisli::frontend::project::SourcePolicy::default(),
        &unavailable,
    )
    .unwrap_err();
    assert_eq!(error.code, "project");
    let source = "use std::quantum::{split,join,z,phase_eighth};
        unitary fn diagonal(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{
            let (b,u)=split(q);z(excl b);phase_eighth(excl u);join(b,u)
        }
        pub unitary fn f(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{diagonal(ctrl q);q}";
    check_project(&SourceRoot::new(source).0).unwrap();
}

#[test]
fn access_markers_remain_ordinary_contextual_names() {
    let source = "unitary fn excl(q:Q<Bit>)->Q<Bit>{q}
        unitary fn ctrl(q:Q<Bit>)->Q<Bit>{excl(q)}
        pub unitary fn f(q:Q<Bit>)->Q<Bit>{ctrl(q)}";
    selected(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
}

#[test]
fn zero_width_owner_keeps_phase_and_cannot_be_duplicated() {
    let source = "use std::quantum::phase_eighth;
        pub unitary fn f(q:Q<Unit>)->Q<Unit>{phase_eighth(excl q);q}";
    let proposal = selected(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap();
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let accepted = kernel
        .check_against_native(proposal.payload(), proposal.comparison_request())
        .unwrap();
    let input = vec![[0.25, -0.5], [0.75, 0.125]];
    let actual = accepted
        .execute_pure(
            &input,
            2,
            qleisli::interchange::hierarchical::execution::ExecutionLimits {
                max_amplitudes: 16,
                max_steps: 1000,
            },
        )
        .unwrap();
    let s = std::f64::consts::FRAC_1_SQRT_2;
    for (actual, [re, im]) in actual.amplitudes.iter().zip(input) {
        assert!((actual[0] - (re - im) * s).abs() < 1e-12);
        assert!((actual[1] - (re + im) * s).abs() < 1e-12);
    }
    let source = "unitary fn pair(q:Q<Unit>,r:Q<Unit>)->(Q<Unit>,Q<Unit>){(q,r)}
        pub unitary fn f(q:Q<Unit>)->Q<Unit>{pair(excl q,excl q);q}";
    assert!(check_project(&SourceRoot::new(source).0).is_err());
    assert!(ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).is_err());
}

#[test]
fn exact_owner_shape_and_actual_body_effect_are_required() {
    for (definition, finite_code, selected_code) in [
        (
            "unitary fn change(q:Q<(Bit,Unit)>)->(Q<Bit>,Q<Unit>){split(q)}",
            ErrorCode::TypeMismatch,
            "type",
        ),
        (
            "fn change(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{let (b,u)=split(q);let m=measure_z(b);discard(u);join(init0(),unit(()))}",
            ErrorCode::Effect,
            "effect",
        ),
        (
            "unitary fn change(q:Q<(Bit,Unit)>)->Q<(Unit,Bit)>{basis q as (b,()){((),b)}}",
            ErrorCode::TypeMismatch,
            "type",
        ),
    ] {
        let source = format!(
            "{IMPORTS} use std::quantum::split;
            use std::quantum::join;use std::quantum::unit;use std::observe::discard;
            {definition} pub fn f(q:Q<(Bit,Unit)>)->Q<(Bit,Unit)>{{change(excl q);q}}"
        );
        let finite = check_project(&SourceRoot::new(&source).0).unwrap_err();
        assert_eq!(finite.code, finite_code, "{source}\n{finite}");
        let selected =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.clone())])).unwrap_err();
        assert_eq!(selected.code(), selected_code, "{source}\n{selected}");
        if selected_code == "type" {
            assert!(selected.message().contains("exclusive call must return"));
            assert!(finite.message.contains("exclusive call must return"));
        } else {
            assert!(
                selected
                    .message()
                    .contains("\"externally unitary\" is not supported")
            );
            assert!(
                finite
                    .message
                    .contains("\"externally unitary\" is not supported")
            );
        }
    }
}

#[test]
fn reassembled_owner_and_callee_binders_do_not_restore_old_snapshot() {
    let source = format!(
        "{IMPORTS} use std::quantum::join;use std::quantum::split;
        unitary fn transform(q:Q<(Bit,Bit)>)->Q<(Bit,Bit)>{{
            let (a,b)=split(q);x(excl a);join(a,b)
        }}
        pub observe fn main()->(Bit,Bit){{
            let q=join(init0(),init0());transform(excl q);
            let (a,b)=split(q);(measure_z(a),measure_z(b))
        }}"
    );
    let finite = compile_project(&SourceRoot::new(&source).0).unwrap();
    let proposal = selected(&source)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw()
        .unwrap();
    let concrete = Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    for accepted in [&finite, &concrete] {
        assert_eq!(
            run_closed(accepted, SimulationLimits::default()).unwrap(),
            BTreeMap::from([(vec![true, false], 1.0)])
        );
    }
}

#[test]
fn contextual_markers_keep_original_locations_and_bounded_arity() {
    use qleisli::frontend::ast::{ExprKind, FnBody, QuantumAccess, StmtKind};
    use qleisli::frontend::parser::parse_module;
    let source = "// π source\r\npub unitary fn f(q:Q<Bit>)->Q<Bit>{h(excl q);q}";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("quantum body")
    };
    let StmtKind::Expr(call) = &body.statements[0].kind else {
        panic!("expression statement")
    };
    let ExprKind::AccessCall { args, .. } = &call.kind else {
        panic!("access call")
    };
    assert_eq!(args[0].access, QuantumAccess::Excl);
    assert_eq!(
        &source[args[0].value.span.start..args[0].value.span.end],
        "excl q"
    );
    let ExprKind::Name(owner) = &args[0].value.kind else {
        panic!("lexical owner")
    };
    assert_eq!(&source[owner.span.start..owner.span.end], "q");
    for arguments in ["excl q,q", "q,excl q", "excl q[]", "excl q()"] {
        assert!(
            parse_module(&format!("fn f(q:Q<Bit>)->Q<Bit>{{h({arguments});q}}")).is_err(),
            "{arguments}"
        );
    }
    // Whitespace before a normal call's parenthesis does not turn the
    // ordinary identifier `excl` into an argument marker.
    parse_module("fn f(q:Q<Bit>)->Q<Bit>{h(excl (q));q}").unwrap();
    let source = format!(
        "fn f(q:Q<Bit>)->Q<Bit>{{h({});q}}",
        vec!["excl q"; 65].join(",")
    );
    let error = parse_module(&source).unwrap_err();
    assert!(error.message.contains("64"), "{error}");
}

#[test]
fn indexed_places_retain_original_axis_and_owner_occurrences() {
    use qleisli::frontend::ast::{AxisSelection, ExprKind, FnBody, QuantumAccess, StmtKind};
    use qleisli::frontend::parser::parse_module;
    let source = "// π\r\npub unitary fn f[const k:Nat](q:Q<Bits<3>>)->Q<Bits<3>>{gate(excl q[k+1],ctrl q[0..k]);q}";
    let module = parse_module(source).unwrap();
    let FnBody::Quantum(body) = &module.decls[0].body else {
        panic!("quantum body")
    };
    let StmtKind::Expr(call) = &body.statements[0].kind else {
        panic!("call")
    };
    let ExprKind::AccessCall { args, .. } = &call.kind else {
        panic!("access call")
    };
    assert_eq!(args.len(), 2);
    for (arg, access, text) in [
        (&args[0], QuantumAccess::Excl, "excl q[k+1]"),
        (&args[1], QuantumAccess::Ctrl, "ctrl q[0..k]"),
    ] {
        assert_eq!(arg.access, access);
        assert_eq!(&source[arg.value.span.start..arg.value.span.end], text);
        let ExprKind::Name(owner) = &arg.value.kind else {
            panic!("parent owner")
        };
        assert_eq!(&source[owner.span.start..owner.span.end], "q");
    }
    assert!(matches!(args[0].selection, Some(AxisSelection::Index(_))));
    assert!(matches!(
        args[1].selection,
        Some(AxisSelection::Range { .. })
    ));
    for expression in [
        "q[0]",
        "q[0..1]",
        "h(q[0])",
        "h(excl q[..1])",
        "h(ctrl q[0..])",
    ] {
        assert!(
            parse_module(&format!("fn f(q:Q<Bits<2>>)->Q<Bits<2>>{{{expression};q}}")).is_err(),
            "{expression}"
        );
    }
}

#[test]
fn indexed_places_check_symbolic_bounds_and_ordered_selected_types() {
    for text in [
        "use std::quantum::h;pub unitary fn f[const N:Nat,const K:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires K<N {h(excl q[K]);q}",
        "unitary fn id[const W:Nat](r:Q<Bits<W>>)->Q<Bits<W>>{r} pub unitary fn f[const N:Nat,const A:Nat,const B:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires A<=B,B<=N {id[B-A](excl q[A..B]);q}",
        "unitary fn pair[const A:Nat,const B:Nat](a:Q<Bits<A>>,b:Q<Bits<B>>)->(Q<Bits<A>>,Q<Bits<B>>){(a,b)}pub unitary fn f[const N:Nat,const K:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires K<=N {pair[N-K,K](excl q[K..N],ctrl q[0..K]);q}",
        "use std::quantum::cnot;pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{cnot(ctrl q[0],excl q[1]);q}",
        "use std::quantum::cnot;pub unitary fn f[const N:Nat,const I:Nat,const J:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires I<J,J<N {cnot(ctrl q[I],excl q[J]);q}",
        "use std::quantum::cnot;pub unitary fn f(a:Q<Bits<1>>,b:Q<Bits<1>>)->(Q<Bits<1>>,Q<Bits<1>>){cnot(ctrl a[0],excl b[0]);(a,b)}",
        "use std::quantum::h;pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{static let k=1;h(excl q[k]);h(excl q[0]);q}",
        "unitary fn id(r:Q<Bits<0>>)->Q<Bits<0>>{r}pub unitary fn f(q:Q<Bits<0>>)->Q<Bits<0>>{id(excl q[0..0]);q}",
    ] {
        let parsed = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]));
        assert!(parsed.is_ok(), "{text}: {parsed:?}");
        assert_eq!(parsed.unwrap().source("main"), Some(text));
    }
}

#[test]
fn indexed_places_refuse_unproved_bounds_overlap_and_changed_interfaces() {
    for (body, code) in [
        ("h(excl q[2]);q", "size"),
        ("h(excl q[0-1]);q", "size"),
        (
            "h(excl q[170141183460469231731687303715884105727]);q",
            "limit",
        ),
        ("cnot(ctrl q[0],excl q[0]);q", "ownership"),
        ("range_pair(excl q[0..2],ctrl q[1..2]);q", "ownership"),
        ("range_pair(excl q,ctrl q[0..0]);q", "ownership"),
        ("h(excl q[0..1]);q", "type"),
        ("range(excl q[0]);q", "type"),
        ("change(excl q[0]);q", "type"),
        ("measure_z(excl q[0]);q", "effect"),
        ("let moved=q;h(excl q[0]);moved", "ownership"),
        ("let k=0;h(excl q[k]);q", "static"),
    ] {
        let text = format!(
            "use std::quantum::{{h,cnot}};use std::observe::measure_z;unitary fn range(r:Q<Bits<1>>)->Q<Bits<1>>{{r}}unitary fn range_pair(a:Q<Bits<2>>,b:Q<Bits<1>>)->(Q<Bits<2>>,Q<Bits<1>>){{(a,b)}}unitary fn change(r:Q<Bit>)->(Q<Bit>,Unit){{(r,())}}pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{{{body}}}"
        );
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        assert_eq!(error.code(), code, "{text}: {error}");
        if body.contains("170141183460469231731687303715884105727") {
            assert_eq!(
                &text[error.span().start..error.span().end],
                "excl q[170141183460469231731687303715884105727]"
            );
        }
    }
}

#[test]
fn indexed_place_obligations_cover_unused_branches_and_empty_loops() {
    for (program, code) in [
        (
            "unitary fn unused(q:Q<Bits<2>>)->Q<Bits<2>>{h(excl q[2]);q}pub unitary fn f(q:Q<Bit>)->Q<Bit>{q}",
            "size",
        ),
        (
            "pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{if static 0==0 {q}else{h(excl q[0..1]);q}}",
            "type",
        ),
        (
            "pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{if 1 {q}else{h(excl q[2]);q}}",
            "size",
        ),
        (
            "pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{qfor static i in 0..0 carry r=q{h(excl r[0..1]);yield r;}}",
            "type",
        ),
        (
            "pub unitary fn f[const N:Nat,const K:Nat](q:Q<Bits<N>>)->Q<Bits<N>>{h(excl q[K]);q}",
            "size",
        ),
    ] {
        let text = format!("use std::quantum::h;{program}");
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), text.clone())])).unwrap_err();
        assert_eq!(error.code(), code, "{text}: {error}");
    }
}

#[test]
fn indexed_place_profiles_preserve_the_common_judgment_before_transport() {
    let text = "use std::quantum::h;pub unitary fn f(q:Q<Bits<2>>)->Q<Bits<2>>{h(excl q[0]);q}";
    let parsed = selected(text);
    let source = parsed
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let proposal = source.lower_raw().unwrap();
    let accepted = Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    let error = check_project(&SourceRoot::new(text).0).unwrap_err();
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(
        error
            .message
            .contains("register types are outside the finite lowering profile"),
        "{error}"
    );
    // An invalid source must fail the common judgment before either lowerer.
    let invalid = text.replace("q[0]", "q[2]");
    assert_eq!(
        check_project(&SourceRoot::new(&invalid).0)
            .unwrap_err()
            .code,
        ErrorCode::TypeMismatch
    );
}

#[test]
fn symbolic_place_overlap_requires_original_binder_guards() {
    let text = "use std::quantum::cnot;pub unitary fn f[const N:Nat,const I:Nat,const J:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires I<N,J<N {cnot(ctrl q[I],excl q[J]);q}";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .expect_err("disjointness is not implied by independent bounds");
    assert_eq!(error.code(), "ownership");
    assert_eq!(&text[error.span().start..error.span().end], "excl q[J]");
    let text = "use std::quantum::h;pub unitary fn f[const N:Nat](q:Q<Bits<N>>)->Q<Bits<N>>{let N=0;h(excl q[N]);q}";
    let error = ParsedProgram::parse(BTreeMap::from([("main".into(), text.into())]))
        .expect_err("runtime shadow is not a static index");
    assert_eq!(error.code(), "name", "{error}");
}

#[test]
fn selected_indexed_places_preserve_exact_axis_phase_and_reference() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let kernel = Kernel::selected().unwrap();
    for n in 1..=3 {
        for k in 0..n {
            for (gate, flip) in [("x(excl q[K]);", true), ("z(ctrl q[K]);", false)] {
                let text = format!(
                    "use std::quantum::{{x,z,split,join}};pub unitary fn main[const K:Nat](input:Q<(Bits<{n}>,Bit)>)->Q<(Bits<{n}>,Bit)> requires K<{n}{{let(q,r)=split(input);{gate}join(q,r)}}"
                );
                let source = selected(&text)
                    .instantiate(
                        "main::main",
                        BTreeMap::from([("K".into(), k)]),
                        BTreeMap::new(),
                    )
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let proposal = source
                    .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let basis = BasisType::Pair(Box::new(BasisType::Bits(n)), Box::new(BasisType::Bit));
                let meaning = if flip {
                    FiniteMeaning::permutation(
                        basis,
                        (0..1u16 << (n + 1)).map(|label| label ^ (1 << k)).collect(),
                    )
                    .unwrap()
                } else {
                    FiniteMeaning::phase(
                        basis,
                        (0..1u16 << (n + 1))
                            .map(|label| if label & (1 << k) != 0 { 4 } else { 0 })
                            .collect(),
                    )
                    .unwrap()
                };
                proposal
                    .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let accepted = kernel.accept(proposal.proposal()).unwrap();
                proposal.validate_source_steps(&accepted).unwrap();
                assert_eq!(accepted.raw().operations.len(), 9);
                if !flip {
                    assert_eq!(source.lower_raw().unwrap_err().code(), "unsupported");
                }
            }
        }
    }
}

#[test]
fn joint_places_reassemble_updated_values_in_original_axis_order() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let kernel = Kernel::selected().unwrap();
    for (call, control, target) in [
        ("cnot(ctrl q[0],excl q[2]);", 0, 2),
        ("cnot(ctrl q[2],excl q[0]);", 2, 0),
    ] {
        let text = format!(
            "use std::quantum::{{cnot,split,join}};pub unitary fn main(input:Q<(Bits<3>,Bit)>)->Q<(Bits<3>,Bit)>{{let(q,r)=split(input);{call}join(q,r)}}"
        );
        let source = selected(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let meaning = FiniteMeaning::permutation(
            BasisType::Pair(Box::new(BasisType::Bits(3)), Box::new(BasisType::Bit)),
            (0..16u16)
                .map(|label| {
                    if label & (1 << control) != 0 {
                        label ^ (1 << target)
                    } else {
                        label
                    }
                })
                .collect(),
        )
        .unwrap();
        proposal
            .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        assert_eq!(accepted.raw().operations.len(), 15);
    }
    let bad = "use std::quantum::cnot;pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{cnot(excl q[2],ctrl q[0]);q}";
    let source = selected(bad)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let error = source
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap_err();
    assert_eq!(error.code(), "contract");
    assert_eq!(
        &bad[error.span().start..error.span().end],
        "cnot(excl q[2],ctrl q[0])"
    );
}

#[test]
fn selected_slices_apply_nontrivial_actions_in_half_open_axis_order() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let kernel = Kernel::selected().unwrap();
    for start in 0..3 {
        for end in start + 1..=3 {
            for phase in [false, true] {
                let (gate, access, index) = if phase {
                    ("z", "ctrl", "N-1")
                } else {
                    ("x", "excl", "0")
                };
                let text = format!(
                    "use std::quantum::{{x,z}};fn update[const N:Nat](r:Q<Bits<N>>)->Q<Bits<N>> requires 0<N {{{gate}({access} r[{index}]);r}}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{{update[{}](excl q[{start}..{end}]);q}}",
                    end - start
                );
                let source = selected(&text)
                    .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let proposal = source
                    .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let meaning = if phase {
                    FiniteMeaning::phase(
                        BasisType::Bits(3),
                        (0..8)
                            .map(|i| if i & (1 << (end - 1)) != 0 { 4 } else { 0 })
                            .collect(),
                    )
                } else {
                    FiniteMeaning::permutation(
                        BasisType::Bits(3),
                        (0..8).map(|i| i ^ (1 << start)).collect(),
                    )
                }
                .unwrap();
                proposal
                    .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let accepted = kernel.accept(proposal.proposal()).unwrap();
                proposal.validate_source_steps(&accepted).unwrap();
            }
        }
    }
}

#[test]
fn selected_place_control_rechecks_bound_provider_and_shared_work() {
    use qleisli::contract::{DEFAULT_EXACT_WORK, exact::Budget};
    let text = "use std::quantum::{z,h};fn provider(q:Q<Bit>)->Q<Bit>{z(q)}unitary fn apply[const U:Op<Bit>](q:Q<Bits<3>>)->Q<Bits<3>> requires Applicable(U){U(ctrl q[1]);q}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{apply[provider](q)}";
    let source = selected(text)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
    let mut budget = Budget::new(DEFAULT_EXACT_WORK);
    source.lower_raw_with_kernel(&kernel, &mut budget).unwrap();
    let spent = DEFAULT_EXACT_WORK - budget.remaining();
    assert!(spent > 1);
    assert_eq!(
        source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(spent - 1))
            .unwrap_err()
            .code(),
        "limit"
    );
    let unavailable = Kernel::new(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(
        source
            .lower_raw_with_kernel(&unavailable, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap_err()
            .code(),
        "io"
    );
    assert_eq!(source.lower_raw().unwrap_err().code(), "unsupported");
    let bad = text.replace("{z(q)}", "{h(q)}");
    let source = selected(&bad)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let error = source
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap_err();
    assert_eq!(error.code(), "contract");
    assert_eq!(&bad[error.span().start..error.span().end], "U(ctrl q[1])");
}

#[test]
fn selected_places_thread_updated_parents_through_static_branches_and_folds() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let text = "use std::quantum::x;pub unitary fn main[const R:Nat](q:Q<Bits<3>>)->Q<Bits<3>> requires R<=3 {x(excl q[2]);qfor static k in 0..R carry r=q {x(excl r[k]);let u=if static k==0 {x(excl r[2]);()}else{()};yield r;}}";
    let parsed = selected(text);
    let kernel = Kernel::selected().unwrap();
    for rounds in 0..=3 {
        let source = parsed
            .instantiate(
                "main::main",
                BTreeMap::from([("R".into(), rounds)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source.lower_raw().unwrap();
        let mask = if rounds == 0 { 4 } else { (1 << rounds) - 1 };
        let meaning =
            FiniteMeaning::permutation(BasisType::Bits(3), (0..8).map(|i| i ^ mask).collect())
                .unwrap();
        proposal
            .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
    }
}

#[test]
fn selected_places_mix_distinct_whole_parents_and_selected_owners() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let text = "use std::quantum::{split,join,cnot};pub unitary fn main(input:Q<(Bits<3>,Bit)>)->Q<(Bits<3>,Bit)>{let(q,r)=split(input);cnot(ctrl q[1],excl r);cnot(ctrl r,excl q[2]);join(q,r)}";
    let source = selected(text)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
    let proposal = source
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let meaning = FiniteMeaning::permutation(
        BasisType::Pair(Box::new(BasisType::Bits(3)), Box::new(BasisType::Bit)),
        (0..16)
            .map(|i| {
                let j = if i & 2 != 0 { i ^ 8 } else { i };
                if j & 8 != 0 { j ^ 4 } else { j }
            })
            .collect(),
    )
    .unwrap();
    proposal
        .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
}

#[test]
fn selected_places_apply_original_bound_operations_and_check_actual_ctrl_body() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    for (gate, access, phases) in [("x", "excl", false), ("z", "ctrl", true)] {
        // Static providers require an ordinary function, not a primitive name.
        let text = format!(
            "use std::quantum::{{x,z}};fn provider(q:Q<Bit>)->Q<Bit>{{{gate}(q)}}unitary fn apply[const U:Op<Bit>](q:Q<Bits<3>>)->Q<Bits<3>> requires Applicable(U){{U({access} q[1]);q}}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{{apply[provider](q)}}"
        );
        let source = selected(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let kernel = Kernel::selected().unwrap();
        let proposal = source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let meaning = if phases {
            FiniteMeaning::phase(
                BasisType::Bits(3),
                (0..8).map(|i| if i & 2 != 0 { 4 } else { 0 }).collect(),
            )
        } else {
            FiniteMeaning::permutation(BasisType::Bits(3), (0..8).map(|i| i ^ 2).collect())
        }
        .unwrap();
        proposal
            .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
    }
}

#[test]
fn selected_place_replay_rejects_native_valid_paired_partition_faults() {
    use qleisli::ir::RawOp;
    let kernel = Kernel::selected().unwrap();
    for (ty, place) in [("Bit", "q[1]"), ("Bits<1>", "q[1..2]")] {
        let text = format!(
            "unitary fn same(x:Q<{ty}>)->Q<{ty}>{{x}}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{{same(excl {place});q}}"
        );
        let source = selected(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source.lower_raw().unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        assert_eq!(accepted.raw().operations.len(), 6);
        for fault in 0..3 {
            let mut raw = accepted.raw().clone();
            if fault < 2 {
                let RawOp::Split { left_bits, .. } = &mut raw.operations[0] else {
                    panic!("selected prefix")
                };
                *left_bits = 0;
                if fault == 1 {
                    // The paired fault still implements identity, but extracts
                    // a different original place. Matrix equality is insufficient.
                    let RawOp::Split { left_bits, .. } = &mut raw.operations[3] else {
                        panic!("updated parent prefix")
                    };
                    *left_bits = 0;
                }
            } else {
                let RawOp::Join { left, right, .. } = &mut raw.operations[5] else {
                    panic!("updated parent join")
                };
                std::mem::swap(left, right);
            }
            let wrong = kernel.accept_raw(raw).unwrap();
            assert_eq!(
                proposal.validate_source_steps(&wrong).unwrap_err().code(),
                "preservation"
            );
        }
    }
}

#[test]
fn selected_place_inverse_keeps_original_phase_axis() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let text = "use std::quantum::phase;unitary fn turn(q:Q<Bits<3>>)->Q<Bits<3>>{phase[1,3](excl q[1]);q}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{adjoint(turn)(q)}";
    let source = selected(text)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let kernel = Kernel::selected().unwrap();
    let proposal = source
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let meaning = FiniteMeaning::phase(
        BasisType::Bits(3),
        (0..8)
            .map(|label| if label & 2 != 0 { 7 } else { 0 })
            .collect(),
    )
    .unwrap();
    proposal
        .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
}

#[test]
fn slices_keep_empty_views_and_scalar_phase_during_joint_access() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let kernel = Kernel::selected().unwrap();
    for calls in [
        "phase_eighth(ctrl q[0..3]);",
        "pair(ctrl q[0..3],ctrl q[1..1]);",
        "pair(ctrl q[1..1],ctrl q[0..3]);",
        "pair(ctrl q[0..1],ctrl q[2..3]);",
    ] {
        let helper = if calls.starts_with("pair") {
            "unitary fn pair[const A:Nat,const B:Nat](a:Q<Bits<A>>,b:Q<Bits<B>>)->(Q<Bits<A>>,Q<Bits<B>>){phase_eighth(ctrl a);phase_eighth(ctrl b);(a,b)}"
        } else {
            ""
        };
        let text = format!(
            "use std::quantum::phase_eighth;{helper}pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{{{calls}q}}"
        );
        // Explicit static arguments preserve the two exact selected widths.
        let text = if calls.starts_with("pair") {
            text.replace(
                "pair(ctrl",
                if calls.contains("q[0..1]") {
                    "pair[1,1](ctrl"
                } else if calls.starts_with("pair(ctrl q[1..1]") {
                    "pair[0,3](ctrl"
                } else {
                    "pair[3,0](ctrl"
                },
            )
        } else {
            text
        };
        let source = selected(&text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let phase = if calls.starts_with("pair") { 2 } else { 1 };
        let meaning = FiniteMeaning::phase(BasisType::Bits(3), vec![phase; 8]).unwrap();
        proposal
            .check_finite_meaning(&kernel, &meaning, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
    }
    let text = "use std::quantum::phase_eighth;pub unitary fn main(q:Q<Bits<0>>)->Q<Bits<0>>{phase_eighth(ctrl q[0..0]);q}";
    let proposal = selected(text)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
        .unwrap();
    proposal
        .check_finite_meaning(
            &kernel,
            &FiniteMeaning::phase(BasisType::Bits(0), vec![1]).unwrap(),
            &mut Budget::new(DEFAULT_EXACT_WORK),
        )
        .unwrap();
}

#[test]
fn closed_static_branches_and_empty_fold_thread_updated_carry() {
    let source = "use std::quantum::x;
        pub unitary fn f[const rounds:Nat](q:Q<Bit>)->Q<Bit>{
            qfor static k in 0..rounds carry r=q {
                let u=if static k==0 {x(excl r);()} else {x(excl r);()};
                yield r;
            }
        }";
    let parsed = selected(source);
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    let input = vec![[0.25, -0.5], [0.75, 0.125], [-0.25, 0.375], [0.5, -0.625]];
    for rounds in 0..=3 {
        let proposal = parsed
            .instantiate(
                "main::f",
                BTreeMap::from([("rounds".into(), rounds)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap()
            .lower()
            .unwrap();
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let actual = accepted
            .execute_pure(
                &input,
                2,
                qleisli::interchange::hierarchical::execution::ExecutionLimits {
                    max_amplitudes: 16,
                    max_steps: 1000,
                },
            )
            .unwrap();
        assert_eq!(
            actual.amplitudes,
            (0..4)
                .map(|i| input[i ^ (rounds as usize % 2)])
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn selected_control_retains_exact_scalar_phase_and_diagonal_meaning() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    for (text, basis, phases) in [
        (
            "use std::quantum::phase_eighth;pub unitary fn main(q:Q<Unit>)->Q<Unit>{phase_eighth(ctrl q);q}",
            BasisType::Unit,
            vec![1],
        ),
        (
            "use std::quantum::z;pub unitary fn main(q:Q<Bit>)->Q<Bit>{z(ctrl q);q}",
            BasisType::Bit,
            vec![0, 4],
        ),
    ] {
        let source = selected(text)
            .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap()
            .elaborate()
            .unwrap();
        let kernel = Kernel::selected().unwrap();
        let proposal = source
            .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        let target = FiniteMeaning::phase(basis.clone(), phases.clone()).unwrap();
        proposal
            .check_finite_meaning(&kernel, &target, &mut Budget::new(DEFAULT_EXACT_WORK))
            .unwrap();
        // Unitarity or preservation of sectors does not erase exact phase.
        let wrong = FiniteMeaning::phase(basis, vec![0; phases.len()]).unwrap();
        assert_eq!(
            proposal
                .check_finite_meaning(&kernel, &wrong, &mut Budget::new(DEFAULT_EXACT_WORK))
                .unwrap_err()
                .code(),
            "contract"
        );
    }
}

#[test]
fn selected_register_access_preserves_exact_axes_and_untouched_reference() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    let kernel = Kernel::selected().unwrap();
    // Every position at these small widths, including both empty end pieces
    // and the zero-width remainder at width one. These expected equations are
    // built from label bits, independently of either source or IR routing.
    for n in 1..=3 {
        for k in 0..n {
            for gate in ["", "x(excl b);", "z(ctrl b);"] {
                let text = format!(
                    "use std::registers::{{take_bit,put_bit}};use std::quantum::{{x,z,split,join}};
                    pub unitary fn main(input:Q<(Bits<{n}>,Bit)>)->Q<(Bits<{n}>,Bit)>{{
                        let(q,r)=split(input);
                        let(b,rest)=take_bit[{n},{k}](q);{gate}
                        join(put_bit[{n},{k}](b,rest),r)
                    }}"
                );
                let source = selected(&text)
                    .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
                    .unwrap()
                    .elaborate()
                    .unwrap();
                let proposal = source
                    .lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let basis = BasisType::Pair(Box::new(BasisType::Bits(n)), Box::new(BasisType::Bit));
                let required = if gate.starts_with('x') {
                    FiniteMeaning::permutation(
                        basis,
                        (0..1u16 << (n + 1)).map(|label| label ^ (1 << k)).collect(),
                    )
                    .unwrap()
                } else {
                    FiniteMeaning::phase(
                        basis,
                        (0..1u16 << (n + 1))
                            .map(|label| {
                                if gate.starts_with('z') && label & (1 << k) != 0 {
                                    4
                                } else {
                                    0
                                }
                            })
                            .collect(),
                    )
                    .unwrap()
                };
                proposal
                    .check_finite_meaning(&kernel, &required, &mut Budget::new(DEFAULT_EXACT_WORK))
                    .unwrap();
                let accepted = kernel.accept(proposal.proposal()).unwrap();
                proposal.validate_source_steps(&accepted).unwrap();
                // Six register repartitions plus two reference pack/unpack
                // operations; no physical SWAP or preparation/measurement.
                let raw = accepted.raw();
                assert_eq!(
                    raw.operations
                        .iter()
                        .filter(|op| matches!(
                            op,
                            qleisli::ir::RawOp::Split { .. } | qleisli::ir::RawOp::Join { .. }
                        ))
                        .count(),
                    8
                );
                assert_eq!(raw.operations.len(), if gate.is_empty() { 8 } else { 9 });
                if gate.starts_with('z') {
                    let wrong =
                        FiniteMeaning::phase(required.signature().clone(), vec![0; 1 << (n + 1)])
                            .unwrap();
                    assert_eq!(
                        proposal
                            .check_finite_meaning(
                                &kernel,
                                &wrong,
                                &mut Budget::new(DEFAULT_EXACT_WORK)
                            )
                            .unwrap_err()
                            .code(),
                        "contract"
                    );
                }
            }
        }
    }
}

#[test]
fn selected_register_replay_rejects_native_valid_wrong_partitions_and_axis_order() {
    use qleisli::ir::RawOp;
    let text = "use std::registers::{take_bit,put_bit};
        pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{let(b,r)=take_bit[3,1](q);put_bit[3,1](b,r)}";
    let source = selected(text)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let proposal = source.lower_raw().unwrap();
    let kernel = Kernel::selected().unwrap();
    let accepted = kernel.accept(proposal.proposal()).unwrap();
    proposal.validate_source_steps(&accepted).unwrap();
    for fault in 0..3 {
        let mut raw = accepted.raw().clone();
        if fault < 2 {
            let RawOp::Split { left_bits, .. } = &mut raw.operations[0] else {
                panic!("take prefix")
            };
            *left_bits = 0;
            if fault == 1 {
                // This paired mutation still denotes identity. Matching the
                // round-trip matrix alone cannot establish original places.
                let RawOp::Split { left_bits, .. } = &mut raw.operations[3] else {
                    panic!("put prefix")
                };
                *left_bits = 0;
            }
        } else {
            let RawOp::Join { left, right, .. } = &mut raw.operations[5] else {
                panic!("put final join")
            };
            std::mem::swap(left, right);
        }
        let wrong = kernel.accept_raw(raw).unwrap();
        assert_eq!(
            proposal.validate_source_steps(&wrong).unwrap_err().code(),
            "preservation"
        );
    }
    let bad = format!(
        "use std::quantum::h;{}",
        text.replace("put_bit[3,1](b,r)", "h(ctrl b);put_bit[3,1](b,r)")
    );
    let source = selected(&bad)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let error = source
        .lower_raw_with_kernel(
            &kernel,
            &mut qleisli::contract::exact::Budget::new(qleisli::contract::DEFAULT_EXACT_WORK),
        )
        .unwrap_err();
    assert_eq!(error.code(), "contract");
    assert_eq!(&bad[error.span().start..error.span().end], "h(ctrl b)");
}

#[test]
fn selected_generic_register_access_retains_original_static_bounds() {
    let text = "use std::registers::{take_bit,put_bit};use std::quantum::x;
        pub unitary fn main[const N:Nat,const K:Nat](q:Q<Bits<N>>)->Q<Bits<N>> requires K<N {
            let(b,r)=take_bit[N,K](q);x(excl b);put_bit[N,K](b,r)
        }";
    let original = selected(text);
    for (n, k) in [(1, 0), (3, 2)] {
        let source = original
            .instantiate(
                "main::main",
                BTreeMap::from([("N".into(), n), ("K".into(), k)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = source.lower_raw().unwrap();
        let accepted = Kernel::selected()
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
    }
    assert!(
        original
            .instantiate(
                "main::main",
                BTreeMap::from([("N".into(), 3), ("K".into(), 3)]),
                BTreeMap::new()
            )
            .is_err()
    );
    assert!(
        ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            text.replace(" requires K<N", "")
        )]))
        .is_err()
    );
    assert_eq!(original.source("main"), Some(text));
}

#[test]
fn selected_register_access_keeps_zero_width_phase_and_inverse_axis() {
    use qleisli::contract::{BasisType, DEFAULT_EXACT_WORK, exact::Budget, meaning::FiniteMeaning};
    for (text, n, phases) in [
        ("use std::registers::{take_bit,put_bit};use std::quantum::phase_eighth;
          pub unitary fn main(q:Q<Bits<1>>)->Q<Bits<1>>{let(b,r)=take_bit[1,0](q);phase_eighth(ctrl r);put_bit[1,0](b,r)}",
          1, vec![1;2]),
        ("use std::registers::{take_bit,put_bit};use std::quantum::phase;
          unitary fn turn(q:Q<Bits<3>>)->Q<Bits<3>>{let(b,r)=take_bit[3,1](q);let b=phase[1,3](b);put_bit[3,1](b,r)}
          pub unitary fn main(q:Q<Bits<3>>)->Q<Bits<3>>{adjoint(turn)(q)}",
          3, (0..8).map(|label| if label & 2 != 0 {7} else {0}).collect()),
    ] {
        let source = selected(text).instantiate("main::main", BTreeMap::new(), BTreeMap::new())
            .unwrap().elaborate().unwrap();
        let kernel = Kernel::selected().unwrap();
        let proposal = source.lower_raw_with_kernel(&kernel, &mut Budget::new(DEFAULT_EXACT_WORK)).unwrap();
        let target = FiniteMeaning::phase(BasisType::Bits(n), phases).unwrap();
        proposal.check_finite_meaning(&kernel, &target, &mut Budget::new(DEFAULT_EXACT_WORK)).unwrap();
    }
}
