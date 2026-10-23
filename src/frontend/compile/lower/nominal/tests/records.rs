//! Untrusted record proposals only; these probes obtain no accepted handle.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;

const RECORD_FIRST: &str = r#"use std::state::init0;

enum Tri { A, B, C }
enum One { Only }
struct Empty {}
struct Packet { tag: Tri, bit: Bit, zero: Empty, one: One }

fn choose(b: Bit) -> Packet {
    if b {
        Packet { one: One::Only, zero: Empty {}, bit: b, tag: Tri::B }
    } else {
        Packet { tag: Tri::C, bit: b, zero: Empty {}, one: One::Only }
    }
}

classical fn is_b(p: Packet) -> Bit {
    match p.tag { Tri::A => 0, Tri::B => 1, Tri::C => 0 }
}

pub observe fn main() -> Bit {
    let b = measure_z(h(init0()));
    let (p, spare) = (choose(b), Empty {});
    let _ = spare;
    is_b(p)
}
"#;

const WRITTEN_ORDER: &str = r#"use std::state::init0;
struct Pair { first: Bit, second: Bit }
pub observe fn main() -> Pair {
    let a = init0();
    let b = init0();
    Pair { second: measure_z(x(b)), first: measure_z(a) }
}
"#;

// Executable order probe: use the built-in h while retaining the first x source.
// This changes gate semantics; the assertions concern order and single evaluation.
const WRITTEN_ORDER_TRANSLATED: &str = r#"use std::state::init0;
struct Pair { first: Bit, second: Bit }
pub observe fn main() -> Pair {
    let a = init0();
    let b = init0();
    Pair { second: measure_z(h(b)), first: measure_z(a) }
}
"#;

fn assert_record<'a>(value: &'a Value, module: &str, name: &str, names: &[&str]) -> &'a [Value] {
    let Value::Record(ty, values) = value else {
        panic!("lost typed record");
    };
    let Kind::Nominal(nominal) = &ty.kind else {
        panic!("lost original record type");
    };
    let Body::Record(fields) = &nominal.body else {
        panic!("changed declaration kind");
    };
    assert_eq!(nominal.origin.module, module);
    assert_eq!(nominal.origin.name, name);
    assert_eq!(
        fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        names
    );
    assert_eq!(values.len(), fields.len());
    for (field, value) in fields.iter().zip(values) {
        assert_eq!(field.ty, value.ty());
    }
    assert_eq!(ty.basis_bits(), None);
    assert!(!value.owns_quantum());
    values
}

#[test]
fn record_first_uses_original_calls_projections_and_tuple_binders() {
    let (value, raw, effect) = raw_main(&project(RECORD_FIRST));
    let Value::Classical(output) = value else {
        panic!("Bit result");
    };
    assert_eq!(effect, Effect::Observe);
    assert!(raw.registers.is_empty());
    for outcome in [false, true] {
        let mut values = BTreeMap::new();
        classical_history(&raw.operations, outcome, &mut values);
        assert_eq!(values[&output], outcome);
    }
}

#[test]
fn classical_record_construction_and_nested_projection_retain_original_nodes() {
    let text = "enum One{Only} struct Inner{bit:Bit,zero:One} struct Outer{inner:Inner} classical fn make()->Outer{Outer{inner:Inner{zero:One::Only,bit:1}}} classical fn read(p:Outer)->Bit{p.inner.bit} fn main()->(Outer,Bit){let p=make();(p,read(p))}";
    let (value, raw, effect) = raw_main(&project(text));
    let fields = value.into_fields().unwrap();
    let outer = assert_record(&fields[0], "main", "Outer", &["inner"]);
    let inner = assert_record(&outer[0], "main", "Inner", &["bit", "zero"]);
    assert_enum(&inner[1], "One", &["Only"], 0);
    let Value::Classical(output) = fields[1] else {
        panic!("projected Bit");
    };
    let mut values = BTreeMap::new();
    classical_history(&raw.operations, false, &mut values);
    assert!(values[&output]);
    assert_eq!(effect, Effect::Unitary);
}

#[test]
fn record_initializers_run_once_in_written_order_then_store_in_declared_order() {
    assert_eq!(
        WRITTEN_ORDER.replace("x(b)", "h(b)"),
        WRITTEN_ORDER_TRANSLATED
    );
    let (value, raw, effect) = raw_main(&project(WRITTEN_ORDER_TRANSLATED));
    let fields = assert_record(&value, "main", "Pair", &["first", "second"]);
    let prepared: Vec<_> = raw
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::LiftBasis { output, .. } => Some(*output),
            _ => None,
        })
        .collect();
    let measured: Vec<_> = raw
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::MeasureZ { input, output, .. } => Some((*input, *output)),
            _ => None,
        })
        .collect();
    let gates: Vec<_> = raw
        .operations
        .iter()
        .filter_map(|op| match op {
            RawOp::Gate {
                gate,
                input,
                output,
            } => Some((*gate, *input, *output)),
            _ => None,
        })
        .collect();
    assert_eq!(prepared.len(), 2);
    assert_eq!(measured.len(), 2);
    assert_eq!(gates.len(), 1);
    assert_eq!(gates[0].0, SingleGate::H);
    assert_eq!(gates[0].1, prepared[1]);
    assert_eq!(measured[0].0, gates[0].2);
    assert_eq!(measured[1].0, prepared[0]);
    assert!(matches!(fields[0], Value::Classical(id) if id == measured[1].1));
    assert!(matches!(fields[1], Value::Classical(id) if id == measured[0].1));
    assert_eq!(effect, Effect::Observe);
    assert!(raw.registers.is_empty());
    let mut outputs = Vec::new();
    value.outputs(&raw.registers, &mut Vec::new(), &mut outputs);
    assert_eq!(outputs, [measured[1].1, measured[0].1]);
    let projected = WRITTEN_ORDER_TRANSLATED
        .replace("pub observe fn main() -> Pair", "observe fn make() -> Pair")
        + "observe fn main()->Bit{make().first}";
    let (value, raw, _) = raw_main(&project(&projected));
    assert!(matches!(value, Value::Classical(_)));
    assert_eq!(
        raw.operations
            .iter()
            .filter(|op| matches!(op, RawOp::MeasureZ { .. }))
            .count(),
        2
    );
}

#[test]
fn record_branch_keeps_zero_width_children_inherited_ids_and_quantum_frame() {
    let text = "enum Tri{A,B,C} enum One{Only} struct Empty{} struct Packet{tag:Tri,bit:Bit,zero:Empty,one:One} unitary fn keep(b:Bit,q:Q<Unit>)->(Packet,Q<Unit>){if b{(Packet{one:One::Only,zero:Empty{},bit:b,tag:Tri::B},q)}else{(Packet{tag:Tri::C,bit:b,zero:Empty{},one:One::Only},q)}}";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::keep").unwrap();
    let mut lower = lowerer(&mut compiler);
    let condition = lower.classical();
    let returned = lower.register(Ty::unit(), Vec::new());
    let suspended = lower.raw.register(Ty::empty_bits(), Vec::new());
    let old_suspended = lower.raw.registers[&suspended].token;
    let value = lower
        .call_user(&key, vec![Value::Classical(condition), returned], None)
        .unwrap();
    let result = value.into_fields().unwrap();
    let fields = assert_record(&result[0], "main", "Packet", &["tag", "bit", "zero", "one"]);
    assert_enum(&fields[0], "Tri", &["A", "B", "C"], 2);
    assert!(matches!(fields[1], Value::Classical(id) if id == condition));
    assert_record(&fields[2], "main", "Empty", &[]);
    assert_enum(&fields[3], "One", &["Only"], 0);
    assert_ne!(fields[2].ty(), Ty::unit());
    assert_ne!(fields[2].ty(), Ty::empty_bits());
    assert_ne!(fields[2].ty(), fields[3].ty());
    assert!(result[0].clone().into_fields().is_none());
    assert_eq!(result[1].ty(), Ty::quantum(Ty::unit()));
    assert_eq!(lower.raw.registers.len(), 2);
    assert_eq!(lower.raw.registers[&suspended].basis, Ty::empty_bits());
    assert_ne!(lower.raw.registers[&suspended].token, old_suspended);
    let RawOp::ClassicalBranch {
        quantum_phis,
        classical_phis,
        ..
    } = lower.raw.operations.last().unwrap()
    else {
        panic!("actual branch");
    };
    assert_eq!(quantum_phis.len(), 2);
    assert!(quantum_phis.iter().all(|phi| phi.output_wires.is_empty()));
    assert_eq!(
        classical_phis.len(),
        2,
        "only changed enum tag axes receive destinations"
    );
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.compiler.instrument_evidence.is_empty());
}

#[test]
fn record_privacy_uses_original_declaration_and_actual_callee_frame() {
    let leaf = "pub enum One{Only} pub struct P{pub bit:Bit,hidden:One} pub fn make()->P{P{hidden:One::Only,bit:1}}";
    let mut valid = project("fn main()->alias::P{leaf::make()}");
    valid.modules.insert(
        "leaf".into(),
        source_module("leaf", leaf, ModuleOrigin::Local),
    );
    valid.modules.insert(
        "alias".into(),
        source_module(
            "alias",
            "pub use leaf::P; pub use leaf::One;",
            ModuleOrigin::Local,
        ),
    );
    let (value, _, _) = raw_main(&valid);
    let fields = assert_record(&value, "leaf", "P", &["bit", "hidden"]);
    let ty = value.ty();
    let Kind::Nominal(nominal) = &ty.kind else {
        panic!("record type");
    };
    assert_eq!(&*nominal.origin.source, leaf);
    let Body::Record(declared) = &nominal.body else {
        panic!("record declaration");
    };
    assert!(!declared[1].public);
    assert!(matches!(&fields[1], Value::Enumeration(_, ids) if ids.is_empty()));
    for main in [
        "fn main()->leaf::One{leaf::make().hidden}",
        "fn main()->alias::P{alias::P{bit:1,hidden:alias::One::Only}}",
        "classical fn hidden(p:alias::P)->alias::One{p.hidden} fn main()->Bit{0}",
    ] {
        valid.modules.insert(
            "main".into(),
            source_module("main", main, ModuleOrigin::Local),
        );
        assert!(prepare_untrusted_source_test(Path::new("main.qli"), &valid).is_err());
    }
}

#[test]
fn record_storage_refuses_missing_mistyped_and_hidden_quantum_children() {
    let project = project("struct P{bit:Bit} fn main()->P{P{bit:1}}");
    let (value, _, _) = raw_main(&project);
    let ty = value.ty();
    let mut compiler = untrusted_compiler(&project);
    let mut lower = lowerer(&mut compiler);
    for fields in [
        Vec::new(),
        vec![Value::Unit],
        vec![Value::quantum(0, Ty::unit())],
    ] {
        let forged = Value::Record(ty.clone(), fields.clone());
        assert_eq!(
            forged.owns_quantum(),
            fields.iter().any(Value::owns_quantum)
        );
        assert!(
            lower
                .validate_record("main", Span::default(), &ty, &fields)
                .is_err()
        );
    }
    lower.compiler.work = MAX_WORK;
    assert_eq!(
        lower
            .validate_record(
                "main",
                Span::default(),
                &ty,
                &[Value::Classical(ClassicalId(0))]
            )
            .unwrap_err()
            .code,
        ErrorCode::Limit
    );
}

#[test]
fn nested_record_storage_cannot_hide_incomplete_children_behind_retained_types() {
    let project = project(
        "struct Inner{bit:Bit} struct Outer{pair:(Inner,Unit)} fn main()->Outer{Outer{pair:(Inner{bit:1},())}}",
    );
    let (value, _, _) = raw_main(&project);
    let outer_ty = value.ty();
    let Value::Record(_, fields) = value else {
        panic!("outer record");
    };
    let Value::Pair(inner, _) = &fields[0] else {
        panic!("ordinary pair field");
    };
    let inner_ty = inner.ty();
    let mut compiler = untrusted_compiler(&project);
    let mut lower = lowerer(&mut compiler);
    for incomplete in [Vec::new(), vec![Value::Unit]] {
        let fields = vec![Value::pair(
            Value::Record(inner_ty.clone(), incomplete),
            Value::Unit,
        )];
        assert!(
            lower
                .validate_record("main", Span::default(), &outer_ty, &fields)
                .is_err()
        );
    }
}

#[test]
fn record_enum_descendants_require_exact_tag_coordinates_including_zero_width() {
    let project = project(
        "enum Tri{A,B,C} enum One{Only} struct Direct{tag:Tri,one:One} struct Nested{parts:(Direct,Unit,Unit)} fn main()->Nested{Nested{parts:(Direct{tag:Tri::B,one:One::Only},(),())}}",
    );
    let (value, _, _) = raw_main(&project);
    let nested_ty = value.ty();
    let Value::Record(_, nested_fields) = value else {
        panic!("outer record");
    };
    let Value::Tuple(parts) = &nested_fields[0] else {
        panic!("three-part tuple");
    };
    let Value::Record(direct_ty, direct_fields) = &parts[0] else {
        panic!("inner record");
    };
    let Value::Enumeration(tag_ty, ids) = &direct_fields[0] else {
        panic!("Tri field");
    };
    let Value::Enumeration(one_ty, one_ids) = &direct_fields[1] else {
        panic!("singleton field");
    };
    assert_eq!(ids.len(), 2);
    assert!(one_ids.is_empty());
    let mut compiler = untrusted_compiler(&project);
    let mut lower = lowerer(&mut compiler);
    lower
        .validate_record("main", Span::default(), direct_ty, direct_fields)
        .unwrap();
    lower
        .validate_record("main", Span::default(), &nested_ty, &nested_fields)
        .unwrap();
    // Both the direct record and a record under an ordinary tuple must refuse
    // truncated/extra storage; no ID is interpreted as a Boolean value here.
    for bad_ids in [vec![ids[0]], vec![ids[0], ids[1], ids[0]]] {
        let bad_fields = vec![
            Value::Enumeration(tag_ty.clone(), bad_ids),
            direct_fields[1].clone(),
        ];
        let direct_error = lower
            .validate_record("main", Span::default(), direct_ty, &bad_fields)
            .unwrap_err();
        assert_eq!(direct_error.code, ErrorCode::TypeMismatch);
        assert!(direct_error.message.contains("tag coordinates"));
        let nested = vec![Value::Tuple(vec![
            Value::Record(direct_ty.clone(), bad_fields),
            Value::Unit,
            Value::Unit,
        ])];
        let nested_error = lower
            .validate_record("main", Span::default(), &nested_ty, &nested)
            .unwrap_err();
        assert_eq!(nested_error.code, ErrorCode::TypeMismatch);
        assert!(nested_error.message.contains("tag coordinates"));
    }
    let bad_singleton = vec![
        direct_fields[0].clone(),
        Value::Enumeration(one_ty.clone(), vec![ids[0]]),
    ];
    assert!(
        lower
            .validate_record("main", Span::default(), direct_ty, &bad_singleton)
            .is_err()
    );
}

#[test]
fn record_enum_descendants_refuse_wrong_kind_and_empty_nominal_domain() {
    let project = project("enum One{Only} struct P{tag:One} fn main()->P{P{tag:One::Only}}");
    let (value, _, _) = raw_main(&project);
    let ty = value.ty();
    let Value::Record(_, fields) = value else {
        panic!("record");
    };
    let Value::Enumeration(one_ty, _) = &fields[0] else {
        panic!("singleton enum");
    };
    let Kind::Nominal(nominal) = &one_ty.kind else {
        panic!("nominal type");
    };
    let empty = Ty::nominal(crate::frontend::types::nominal::Nominal {
        origin: Arc::clone(&nominal.origin),
        body: Body::Enum(Vec::new()),
    });
    let mut compiler = untrusted_compiler(&project);
    let mut lower = lowerer(&mut compiler);
    for invalid in [Ty::unit(), ty.clone(), empty] {
        let error = lower
            .validate_record(
                "main",
                Span::default(),
                &ty,
                &[Value::Enumeration(invalid, Vec::new())],
            )
            .unwrap_err();
        assert_eq!(error.code, ErrorCode::TypeMismatch);
        assert!(
            error
                .message
                .contains("nonempty domain and tag coordinates")
        );
    }
}

#[test]
fn record_common_checks_and_all_module_native_gates_stay_closed() {
    for text in [
        "struct P{bit:Bit} fn main()->P{P{}}",
        "struct P{bit:Bit} fn main()->P{P{bit:0,bit:1}}",
        "struct P{bit:Bit} fn main()->Bit{let p=P{bit:0};p.absent}",
        "struct P{bit:Bit} fn main()->Bit{let (x,y)=P{bit:0};x}",
        "struct P{bit:Bit} fn f(q:Q<P>)->Bit{q.bit}",
        "struct P{bit:Bit} unitary fn f(q:Q<Bit>)->P{P{bit:measure_z(q)}}",
        "struct P{a:Bit,b:Bit} observe fn f(q:Q<Bit>)->P{P{b:measure_z(q),a:measure_z(q)}}",
    ] {
        assert!(prepare_untrusted_source_test(Path::new("main.qli"), &project(text)).is_err());
    }
    for text in [RECORD_FIRST, "struct Dormant{} fn main()->Bit{0}"] {
        let error = prepare_original_source(Path::new("main.qli"), &project(text))
            .err()
            .expect("public gate");
        assert_eq!(error.code, ErrorCode::Unsupported);
        assert!(error.message.contains("typed native transport"));
    }
    let mut imported = project("fn main()->Bit{0}");
    imported.modules.insert(
        "hidden".into(),
        source_module("hidden", "struct Hidden{}", ModuleOrigin::Local),
    );
    assert!(prepare_original_source(Path::new("main.qli"), &imported).is_err());
    let text = "struct P{bit:Bit} classical fn read(p:P)->Bit{p.bit}";
    let project = project(text);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::read").unwrap();
    let error = compiler
        .compile_basis(&key)
        .err()
        .expect("nominal table gate");
    assert_eq!(error.code, ErrorCode::Unsupported);
    assert!(compiler.basis.is_empty());
}
