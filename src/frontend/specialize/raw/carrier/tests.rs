//! Original .qli bodies, independent logical requests and deliberate faults.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::contract::exact::Exact;
use crate::edition::Edition;
use crate::frontend::compile::ParsedProgram;

fn instance(source: &str) -> Instantiation {
    ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
    .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
    .unwrap()
}

fn kernel() -> native::Kernel {
    native::Kernel::new(std::env::var_os("QLEISLI_KERNEL").unwrap(), Edition::E2026)
}

fn work() -> Budget {
    Budget::new(DEFAULT_EXACT_WORK)
}

#[test]
fn ordinary_preparation_still_refuses_nominal_execution() {
    let source = instance("pub enum Tri{A,B,C} pub unitary fn main(q:Q<Tri>)->Q<Tri>{q}");
    assert_eq!(source.elaborate().unwrap_err().code(), "unsupported");
    let (prepared, _) = super::super::super::elaborate::carrier_preparation(&source).unwrap();
    assert_eq!(prepared.lower_raw().unwrap_err().code(), "unsupported");
    assert!(prepared.lower().is_err());
}

#[test]
fn public_observing_contract_and_ordinary_nominals_cannot_use_pure_carrier_route() {
    let source = instance("pub enum Tri{A,B,C} pub observe fn main(q:Q<Tri>)->Q<Tri>{q}");
    let (prepared, _) = super::super::super::elaborate::carrier_preparation(&source).unwrap();
    let error = lower_inner_profile(
        &prepared,
        prepared.root(),
        None,
        None,
        None,
        Some((&Matrix::identity(3).unwrap(), &mut work())),
    )
    .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.message().contains("pure public contract"));
    let ordinary = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([(
            "main".into(),
            "pub enum Tri{A,B,C} pub fn main()->Tri{Tri::B}".into(),
        )]),
    )
    .unwrap();
    // This case stops at its actual ordinary-value projection barrier. It
    // supplies no downstream carrier/body or ownership evidence.
    let error = ordinary
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(error.message().contains("ordinary nominal values"));
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn actual_enum_record_and_zero_width_source_bodies_use_typed_native_mode() {
    let kernel = kernel();
    for (text, dimension, owner_count) in [
        (
            "pub enum Tri{A,B,C} pub unitary fn main(q:Q<Tri>)->Q<Tri>{q}",
            3,
            1,
        ),
        (
            "pub enum Tri{A,B,C} pub struct Packet{tag:Tri,bit:Bit,zero:Unit} pub unitary fn main(q:Q<Packet>)->Q<Packet>{q}",
            6,
            1,
        ),
        (
            "pub enum One{Only} pub struct Empty{} pub unitary fn main(q:Q<One>,r:Q<Empty>)->(Q<One>,Q<Empty>){(q,r)}",
            1,
            2,
        ),
    ] {
        let checked = instance(text)
            .check_carrier(&kernel, &Matrix::identity(dimension).unwrap(), &mut work())
            .unwrap();
        assert_eq!(checked.native().mode(), "--carrier-pure-check");
        assert!(!checked.source_meaning_verified());
        assert_eq!(checked.entry(), "main::main");
        assert_eq!(checked.request().attached.inputs.len(), owner_count);
        assert_eq!(checked.request().attached.outputs.len(), owner_count);
        assert_eq!(checked.artifact(), checked.native().artifact());
        assert_eq!(checked.native().request(), Some(checked.request_bytes()));
        let ordinary = native::Proposal::new(checked.artifact(), None).unwrap();
        assert!(
            kernel.accept(&ordinary).is_err(),
            "carrier source rows cannot enter ordinary native mode"
        );
    }
}

#[test]
#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
fn source_carrier_depth_uses_the_same_zero_based_native_prefix_limit() {
    let kernel = kernel();
    for (depth, admitted) in [(31, true), (32, true), (33, false)] {
        let mut basis = "One".to_owned();
        for _ in 0..depth {
            basis = format!("(Unit,{basis})");
        }
        let source = instance(&format!(
            "pub enum One{{Only}} pub unitary fn main(q:Q<{basis}>)->Q<{basis}>{{q}}"
        ));
        let checked = source.check_carrier(&kernel, &Matrix::identity(1).unwrap(), &mut work());
        if admitted {
            assert!(checked.is_ok(), "depth {depth}: {checked:?}");
        } else {
            assert_eq!(checked.unwrap_err().code(), "unsupported");
        }
    }
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn exact_requested_phase_is_independent_of_the_actual_source_body() {
    let kernel = kernel();
    let text = "pub enum Tri{A,B,C} pub unitary fn main(q:Q<Tri>)->Q<Tri>{global_phase_eighth(q)}";
    let source = instance(text);
    let required = Matrix::new(
        3,
        3,
        (0..9)
            .map(|i| {
                if i / 3 == i % 3 {
                    Exact::phase(1)
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap();
    source
        .check_carrier(&kernel, &required, &mut work())
        .unwrap();
    assert!(
        source
            .check_carrier(&kernel, &Matrix::identity(3).unwrap(), &mut work())
            .is_err()
    );
    let identity = instance("pub enum Tri{A,B,C} pub unitary fn main(q:Q<Tri>)->Q<Tri>{q}");
    assert!(
        identity
            .check_carrier(&kernel, &required, &mut work())
            .is_err()
    );
    // A separately valid typed/native identity cannot stand in for the
    // original scalar source steps, even when dimensions and owners agree.
    let checked_identity = identity
        .check_carrier(&kernel, &Matrix::identity(3).unwrap(), &mut work())
        .unwrap();
    let (scalar_source, _) = super::super::super::elaborate::carrier_preparation(&source).unwrap();
    assert!(
        preservation::validate_subject_with_meanings(
            &scalar_source,
            scalar_source.root(),
            None,
            checked_identity.checked.raw(),
            Some(&kernel),
            &mut work(),
            &[]
        )
        .is_err()
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn ordered_source_owners_and_public_isometry_contract_are_preserved() {
    let kernel = kernel();
    let text =
        "pub enum Tri{A,B,C} pub isometry fn main(q:Q<Tri>,b:Q<Bit>)->(Q<Bit>,Q<Tri>){(b,q)}";
    // Input coordinate is tri+3*bit; output is bit+2*tri. This independent
    // logical permutation is not read back from emitted physical wires.
    let required = Matrix::new(
        6,
        6,
        (0..36)
            .map(|i| {
                let (row, col) = (i / 6, i % 6);
                if row == col / 3 + 2 * (col % 3) {
                    Exact::one()
                } else {
                    Exact::zero()
                }
            })
            .collect(),
    )
    .unwrap();
    let source = instance(text);
    let checked = source
        .check_carrier(&kernel, &required, &mut work())
        .unwrap();
    assert_eq!(checked.request().required.public_effect, Effect::Isometry);
    assert!(matches!(
        &checked.request().required.inputs[0].basis[..],
        [transport::Atom::Enum(_, _)]
    ));
    assert_eq!(
        checked.request().required.outputs[0].basis,
        [transport::Atom::Bit]
    );
    assert!(
        source
            .check_carrier(&kernel, &Matrix::identity(6).unwrap(), &mut work())
            .is_err()
    );
}

#[test]
fn helper_only_source_module_is_explicitly_unsupported_before_native_submission() {
    let program = ParsedProgram::parse(
        Edition::E2026,
        BTreeMap::from([
            (
                "main".into(),
                "pub enum Tri{A,B,C} use helper::id; pub unitary fn main(q:Q<Tri>)->Q<Tri>{id(q)}"
                    .into(),
            ),
            (
                "helper".into(),
                "use main::Tri; pub unitary fn id(q:Q<Tri>)->Q<Tri>{q}".into(),
            ),
        ]),
    )
    .unwrap();
    let instance = program
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap();
    let (prepared, _) = super::super::super::elaborate::carrier_preparation(&instance).unwrap();
    let error = lower_inner_profile(
        &prepared,
        prepared.root(),
        None,
        None,
        None,
        Some((&Matrix::identity(3).unwrap(), &mut work())),
    )
    .unwrap_err();
    assert_eq!(error.code(), "unsupported");
    assert!(
        error.message().contains("helper/import-only rows"),
        "{error}"
    );
}
