//! Bounded independent checks for lexical static Nat aliases.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
mod common;
use common::SourceRoot;
use qleisli::frontend::compile::{check_project, compile_project};
use qleisli::frontend::sized::ParsedProgram;
use qleisli::interchange::native::Kernel;
use qleisli::sim::{SimulationLimits, run_closed};
use std::collections::BTreeMap;

fn parsed(source: &str) -> ParsedProgram {
    ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).unwrap()
}

#[test]
fn aliases_normalize_sizes_and_generic_instances_without_runtime_values() {
    let source = "pub unitary fn identity[static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}
        pub unitary fn twice[static n:Nat](q:Q<Bits<2*n>>)->Q<Bits<2*n>>{
            static let width=n+n; static let normalized=width+0; identity[normalized](q)
        }";
    for n in 0..=2 {
        let graph = parsed(source)
            .instantiate(
                "main::twice",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower().unwrap();
        let kernel = qleisli::interchange::hierarchical::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
        );
        let accepted = kernel
            .check_against_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        // Unequal complex coefficients and an external two-dimensional reference
        // detect phase/axis changes; identity must preserve every coefficient.
        let input: Vec<_> = (0..(2usize << (2 * n)))
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
fn fold_bounds_and_per_iteration_aliases_match_independent_parity() {
    let source = "classical fn flip(a:Bit)->Bit{not a}
        pub unitary fn f[static n:Nat]()->Bit{
            static let end=n+1;
            for static i in 0..end carry a=0 {
                static let next=i+1;
                let b=if static next==end {a} else {flip(a)};
                yield b;
            }
        }";
    for n in 0..=3 {
        let graph = parsed(source)
            .instantiate(
                "main::f",
                BTreeMap::from([("n".into(), n)]),
                BTreeMap::new(),
            )
            .unwrap()
            .elaborate()
            .unwrap();
        let proposal = graph.lower_raw().unwrap();
        let accepted = Kernel::selected()
            .unwrap()
            .accept(proposal.proposal())
            .unwrap();
        assert_eq!(
            run_closed(&accepted, SimulationLimits::default()).unwrap(),
            BTreeMap::from([(vec![n % 2 == 1], 1.0)])
        );
    }
}

#[test]
fn checked_unused_alias_is_erased_without_a_runtime_instruction() {
    let source = "pub observe fn main()->Bit{static let width=2+1;0}";
    let finite = compile_project(&SourceRoot::new(source).0).unwrap();
    assert_eq!(
        run_closed(&finite, SimulationLimits::default()).unwrap(),
        BTreeMap::from([(vec![false], 1.0)])
    );
}

#[test]
fn exact_nat_and_concrete_capacity_failures_remain_distinct() {
    let source = "pub unitary fn f()->Bit{static let n=4294967296;0}";
    let error = parsed(source)
        .instantiate("main::f", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap_err();
    assert_eq!(error.code(), "limit");
    let overflow =
        "pub observe fn main()->Bit{static let n=170141183460469231731687303715884105727+1;0}";
    let error =
        ParsedProgram::parse(BTreeMap::from([("main".into(), overflow.into())])).unwrap_err();
    assert_eq!(error.code(), "limit");
}

#[test]
fn runtime_capture_scope_escape_dead_body_shadow_and_invalid_arithmetic_reject() {
    for source in [
        "pub observe fn main()->Bit{let a=1;static let n=a+1;0}",
        "pub observe fn main()->Bit{static let n=1;n}",
        "pub observe fn main()->Bit{static let n=later;static let later=1;0}",
        "pub observe fn main()->Bit{let a=if static 1==1{static let n=1;0}else{0};static let k=n;a}",
        "pub observe fn main()->Bit{for static i in 0..0 carry a=0{static let n=missing;yield a;}}",
        "pub unitary fn f[static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{static let n=1;q} observe fn main()->Bit{0}",
        "pub observe fn main()->Bit{static let n=0-1;0}",
        "pub unitary fn f[static n:Nat,static m:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{static let k=n*m;q} observe fn main()->Bit{0}",
    ] {
        assert!(
            ParsedProgram::parse(BTreeMap::from([("main".into(), source.into())])).is_err(),
            "{source}"
        );
        assert!(
            check_project(&SourceRoot::new(source).0).is_err(),
            "{source}"
        );
    }
}

#[test]
fn static_accounting_does_not_expand_the_basis_domain_of_an_identity_fold() {
    let source = "pub unitary fn thread[static n:Nat,static rounds:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{
        qfor static i in 0..rounds carry r=q{yield r;}
    }";
    let program = parsed(source);
    let kernel = qleisli::interchange::hierarchical::Kernel::new(
        std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
    );
    for n in 0..=3 {
        for rounds in [0, 1, 3] {
            let graph = program
                .instantiate(
                    "main::thread",
                    BTreeMap::from([("n".into(), n), ("rounds".into(), rounds)]),
                    BTreeMap::new(),
                )
                .unwrap()
                .elaborate()
                .unwrap();
            // Width changes only the interface, not the number of source
            // definitions/steps. Fold work counts iterations, never basis rows.
            assert_eq!(graph.definitions().len(), 1);
            assert!(graph.definitions()[0].steps().is_empty());
            assert_eq!(graph.call_instances(), 1);
            assert_eq!(graph.fold_iterations(), rounds as usize);
            let input_type = graph.definitions()[0].inputs()[0].ty();
            assert!(input_type.is_quantum());
            assert_eq!(input_type.kind(), "bits");
            assert_eq!(input_type.width(), Some(n));
            let proposal = graph.lower().unwrap();
            let checked = kernel
                .check_against_native(proposal.payload(), proposal.comparison_request())
                .unwrap();
            // The only enumeration here is this bounded independent simulation
            // oracle, after elaboration/native checking have already completed.
            let input: Vec<_> = (0..(2usize << n))
                .map(|i| [0.25 + i as f64, 0.5 - 0.375 * i as f64])
                .collect();
            let output = checked
                .execute_pure(
                    &input,
                    2,
                    qleisli::interchange::hierarchical::execution::ExecutionLimits {
                        max_amplitudes: 32,
                        max_steps: 1000,
                    },
                )
                .unwrap();
            assert_eq!(output.amplitudes, input, "n={n}, rounds={rounds}");
        }
    }
}
