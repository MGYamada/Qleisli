//! Raw producer probes: no native request or accepted handle is constructed.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

#[test]
fn measured_tri_survives_actual_classical_table_preparation() {
    let project = project(FIRST);
    let mut compiler = untrusted_compiler(&project);
    compiler.prepare_classical_tables().unwrap();
    let is_b = compiler.source.resolution.qualified("main::is_b").unwrap();
    assert!(compiler.deferred_nominal_tables.contains(&is_b));
    assert!(!compiler.basis.contains_key(&is_b));
    let main = compiler.source.resolution.qualified("main::main").unwrap();
    let mut lower = lowerer(&mut compiler);
    let value = lower.call_user(&main, Vec::new(), None).unwrap();
    let Value::Classical(output) = value else {
        panic!("Bit result");
    };
    for outcome in [false, true] {
        let mut values = BTreeMap::new();
        classical_history(&lower.raw.operations, outcome, &mut values);
        assert_eq!(values[&output], outcome);
    }
    assert_eq!(lower.effect, Effect::Observe);
    assert!(lower.raw.registers.is_empty());
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.compiler.instrument_evidence.is_empty());
}

#[test]
fn ordinary_record_reader_does_not_require_a_physical_label_table() {
    let text = "struct Packet { bit: Bit } classical fn read(p: Packet) -> Bit { p.bit } fn main() -> Bit { read(Packet { bit: 1 }) }";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    compiler.prepare_classical_tables().unwrap();
    let read = compiler.source.resolution.qualified("main::read").unwrap();
    assert!(compiler.deferred_nominal_tables.contains(&read));
    assert!(!compiler.basis.contains_key(&read));
    let main = compiler.source.resolution.qualified("main::main").unwrap();
    let mut lower = lowerer(&mut compiler);
    let value = lower.call_user(&main, Vec::new(), None).unwrap();
    let Value::Classical(output) = value else {
        panic!("Bit result");
    };
    let mut values = BTreeMap::new();
    classical_history(&lower.raw.operations, false, &mut values);
    assert!(values[&output]);
    assert!(lower.compiler.checked.is_empty());
}

#[test]
fn actual_basis_expression_still_refuses_a_deferred_nominal_function() {
    let text = "enum Tri { A, B, C } classical fn is_b(t: Tri) -> Bit { match t { Tri::A => 0, Tri::B => 1, Tri::C => 0 } } isometry fn prepare() -> Q<Bit> { basis unit(()) as _ { is_b(Tri::A) } } fn main() -> Bit { 0 }";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    compiler.prepare_classical_tables().unwrap();
    let prepare = compiler
        .source
        .resolution
        .qualified("main::prepare")
        .unwrap();
    let mut lower = lowerer(&mut compiler);
    let Err(error) = lower.call_user(&prepare, Vec::new(), None) else {
        panic!("actual table use remains unsupported");
    };
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(
        error
            .message
            .contains("finite tables require closed built-in basis types")
    );
    assert!(lower.compiler.checked.is_empty());
}

#[test]
fn existing_builtin_classical_tables_remain_eager() {
    let text = "classical fn first(b: Bit) -> Bit { b } classical fn second(b: Bit) -> Bit { first(b) } fn main() -> Bit { 0 }";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    compiler.prepare_classical_tables().unwrap();
    for name in ["main::first", "main::second"] {
        let key = compiler.source.resolution.qualified(name).unwrap();
        assert_eq!(compiler.basis[&key].table, [0, 1]);
    }
    assert!(compiler.deferred_nominal_tables.is_empty());
    assert!(compiler.checked.is_empty());
}

#[test]
fn nominal_table_deferral_does_not_open_the_public_source_gate() {
    let project = project(FIRST);
    let error = prepare_original_source(Path::new("main.qli"), &project)
        .err()
        .expect("public nominal gate remains closed");
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(error.message.contains("typed native transport"));
}
