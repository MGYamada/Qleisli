//! Small independent source checks for provisional acyclic static Nat helpers.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{check_project, compile_project};
use qleisli::frontend::sized::ParsedProgram;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

#[test]
fn computed_helper_sizes_and_chains_use_normalized_generic_arguments() {
    let source = "static fn twice[static n:Nat]()->Nat{n+n}
        static fn next[static n:Nat]()->Nat{twice[n]()+1}
        pub unitary fn identity[static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}
        pub unitary fn f[static n:Nat](q:Q<Bits<2*n+1>>)->Q<Bits<2*n+1>>{identity[next[n]()](q)}";
    for n in 0..=1 {
        let graph = parsed(source)
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let kernel = qleisli::interchange::hierarchical::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").unwrap(),
        );
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let input: Vec<_> = (0..(2usize << (2 * n + 1)))
            .map(|i| [i as f64 + 0.25, 0.5 - i as f64])
            .collect();
        let output = accepted
            .execute_pure(
                &input,
                2,
                qleisli::interchange::hierarchical::execution::ExecutionLimits {
                    max_amplitudes: 64,
                    max_steps: 1000,
                },
            )
            .unwrap();
        assert_eq!(output.amplitudes, input);
    }
}

#[test]
fn static_exponent_schedule_preserves_complex_phase_and_an_external_reference() {
    let source = "use std::quantum::phase;
        static fn exponent[static stage:Nat]()->Nat{stage+1}
        pub unitary fn schedule[static count:Nat](q:Q<Bit>)->Q<Bit> requires count<=3 {
            qfor static i in 0..count carry r=q {
                static let k=exponent[i](); yield phase[1,k](r);
            }
        }";
    let s = std::f64::consts::FRAC_1_SQRT_2;
    // Independent closed-form products: no gates is 1; Z, Z*S and Z*S*T
    // act on |1> by -1, -i and exp(-i*pi/4), respectively.
    for (count, phase) in [[1.0, 0.0], [-1.0, 0.0], [0.0, -1.0], [s, -s]]
        .into_iter()
        .enumerate()
    {
        let graph = parsed(source)
            .instantiate(
                "main::schedule",
                BTreeMap::from([("count".into(), count as u32)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let kernel = qleisli::interchange::hierarchical::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").unwrap(),
        );
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        let input = vec![[0.25, 0.5], [-0.75, 0.125], [0.375, -0.5], [-0.25, -0.625]];
        let output = accepted
            .execute_pure(
                &input,
                2,
                qleisli::interchange::hierarchical::execution::ExecutionLimits {
                    max_amplitudes: 8,
                    max_steps: 1000,
                },
            )
            .unwrap();
        for (i, (actual, value)) in output.amplitudes.iter().zip(&input).enumerate() {
            // The documented execution layout stores quantum basis fastest,
            // with the external reference as the outer dimension.
            let expected = if i % 2 == 0 {
                *value
            } else {
                [
                    value[0] * phase[0] - value[1] * phase[1],
                    value[0] * phase[1] + value[1] * phase[0],
                ]
            };
            assert!(
                (actual[0] - expected[0]).abs() < 1e-12 && (actual[1] - expected[1]).abs() < 1e-12,
                "count {count}, amplitude {i}: {actual:?} != {expected:?}"
            );
        }
    }
}

#[test]
fn checked_helpers_have_no_runtime_instruction_or_entry_authority() {
    let source = "static fn number()->Nat{1+2} pub observe fn main()->Bit{static let n=number();0}";
    let finite = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![false], 1.0)])
    );
    let program = parsed(source);
    assert!(program.function_effect("main::number").is_none());
    assert_eq!(
        program
            .instantiate("main::number", BTreeMap::new(), BTreeMap::new())
            .unwrap_err()
            .code(),
        "static"
    );
}

#[test]
fn same_named_helpers_in_different_modules_keep_identity_and_visibility() {
    let modules = BTreeMap::from([
        ("main".into(), "use left::left; use right::right; pub observe fn main()->Bit{left[1]() and right[1]()}".into()),
        ("left".into(), "static fn width[static n:Nat]()->Nat{n+1} pub fn left[static n:Nat]()->Bit{static let m=width[n]();if static m==n+1{1}else{0}}".into()),
        ("right".into(), "static fn width[static n:Nat]()->Nat{n+2} pub fn right[static n:Nat]()->Bit{static let m=width[n]();if static m==n+2{1}else{0}}".into()),
    ]);
    let program = ParsedProgram::parse(modules.clone()).unwrap();
    let graph = program
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    let proposal = graph.lower_raw().unwrap();
    let accepted = qleisli::interchange::native::Kernel::selected()
        .unwrap()
        .accept(proposal.proposal())
        .unwrap();
    assert_eq!(
        run_closed(&accepted, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![true], 1.0)])
    );
    let mut private = modules;
    private.insert(
        "main".into(),
        "use left::width; pub observe fn main()->Bit{0}".into(),
    );
    assert_eq!(
        ParsedProgram::parse(private).unwrap_err().code(),
        "visibility"
    );
}

#[test]
fn helper_premises_are_required_at_the_original_call() {
    let positive = "static fn previous[static n:Nat]()->Nat requires n>=1 {n-1}
        pub observe fn main()->Bit{static let n=previous[2]();0}";
    check_project(&SourceRoot::new(positive).0).unwrap();
    parsed(positive)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap();
    for source in [
        "static fn previous[static n:Nat]()->Nat requires n>=1 {n-1} pub observe fn main()->Bit{static let n=previous[0]();0}",
        "static fn previous[static n:Nat]()->Nat requires n>=1 {n-1} pub unitary fn f[static n:Nat]()->Bit{static let k=previous[n]();0}",
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), "size", "{error}");
        assert!(check_project(&SourceRoot::new(source).0).is_err());
    }
}

#[test]
fn runtime_dependencies_cycles_unused_invalid_bodies_and_arity_reject() {
    for (source, code) in [
        (
            "static fn number()->Nat{1} pub observe fn main()->Bit{number()}",
            "static",
        ),
        (
            "static fn number(x:Bit)->Nat{x} pub observe fn main()->Bit{0}",
            "static",
        ),
        (
            "static fn first()->Nat{second()} static fn second()->Nat{first()} pub observe fn main()->Bit{0}",
            "cycle",
        ),
        (
            "static fn invalid[static n:Nat]()->Nat{n-1} pub observe fn main()->Bit{0}",
            "size",
        ),
        (
            "static fn number[static n:Nat]()->Nat{n} pub observe fn main()->Bit{static let k=number[]();0}",
            "static",
        ),
        (
            "static fn nonlinear[static n:Nat]()->Nat{n*n} pub observe fn main()->Bit{0}",
            "unsupported",
        ),
        (
            "classical fn number()->Bit{1} static fn invalid()->Nat{number()} pub observe fn main()->Bit{0}",
            "static",
        ),
        (
            "static fn invalid[static n:Nat,static n:Nat]()->Nat{n} pub observe fn main()->Bit{0}",
            "name",
        ),
        (
            "static fn number()->Nat{1} pub observe fn main()->Bit{for static i in 0..0 carry a=0{let b=number();yield b;}}",
            "static",
        ),
    ] {
        let error =
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap_err();
        assert_eq!(error.code(), code, "{source}: {error}");
        assert!(
            check_project(&SourceRoot::new(source).0).is_err(),
            "{source}"
        );
    }
}

#[test]
fn normalized_and_concrete_helper_overflow_remain_capacity_failures() {
    let symbolic = "static fn invalid()->Nat{170141183460469231731687303715884105727+1} pub observe fn main()->Bit{0}";
    assert_eq!(
        ParsedProgram::parse(BTreeMap::from([("main".into(), symbolic.into())]))
            .unwrap_err()
            .code(),
        "limit"
    );
    let concrete =
        "static fn large()->Nat{4294967296} pub observe fn main()->Bit{static let n=large();0}";
    let error = parsed(concrete)
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "limit");
}
