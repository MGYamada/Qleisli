//! Producer input-boundary snapshots from original actual argument Values.
//! No qmatch body, native request or accepted handle is constructed here.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::compile::lower::call_state_tests::untrusted_compiler;
use crate::frontend::project::{ModuleOrigin, ProjectEdition, SourceModule};

// Byte-identical ordinary-copy first source retained by the authoring session.
const ORDINARY_COPY: &str = r#"pub enum Tag { A, B }
unitary fn idle(q: Q<Bit>) -> Q<Bit> { q }
fn duplicate(c: Bit) -> (Bit,Bit) { (c,c) }
pub unitary fn route(c: Bit, s: Q<Tag>, q: Q<Bit>) -> ((Bit,Bit),Q<Tag>,Q<Bit>) { let (s,q)=qmatch(s,q){Tag::A=>idle,Tag::B=>idle}; (duplicate(c),s,q) }
"#;

fn project(source: &str) -> Project {
    Project {
        edition_context: ProjectEdition::Explicit(crate::edition::Edition::E2026),
        root: PathBuf::from("main.qli"),
        modules: BTreeMap::from([(
            "main".into(),
            SourceModule {
                name: "main".into(),
                path: PathBuf::from("main.qli"),
                source: source.into(),
                ast: crate::frontend::parser::parse_module(source).expect("original source"),
                imports: BTreeMap::new(),
                origin: ModuleOrigin::Local,
            },
        )]),
    }
}

fn lowerer<'c, 'p>(compiler: &'c mut Compiler<'p>) -> Lowerer<'c, 'p> {
    Lowerer {
        compiler,
        raw: RawState::new(),
        operation_sources: BTreeMap::new(),
        instrument_calls: Vec::new(),
        nominal_modules: std::rc::Rc::new(std::cell::RefCell::new(BTreeSet::new())),
        nominal_qmatch: None,
        source_context: None,
        tuple_binding_origins: vec![BTreeMap::new()],
        access_updates: vec![BTreeSet::new()],
        effect: Effect::Unitary,
        contract_effect: Effect::Unitary,
        effect_source: None,
        depth: 0,
        bindings: BTreeMap::new(),
    }
}

#[test]
fn retained_frame_keeps_original_ordinary_input_ids() {
    let project = project(ORDINARY_COPY);
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::route").unwrap();
    let (parameters, _) = compiler.signature(&key).unwrap();
    let span = compiler.declarations[&key].span;
    let mut lower = lowerer(&mut compiler);
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    let arguments = parameters
        .iter()
        .map(|ty| lower.input(ty, "main", span, &mut quantum_inputs, &mut classical_inputs))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let frame = Frame::start(&mut lower, key, &arguments).unwrap().unwrap();
    assert!(frame.requires_source_gate());
    let Value::Classical(c) = arguments[0] else {
        panic!("original ordinary Bit argument")
    };
    let result = Value::Tuple(vec![
        Value::Pair(Box::new(Value::Classical(c)), Box::new(Value::Classical(c))),
        arguments[1].clone(),
        arguments[2].clone(),
    ]);
    let raw = retained_raw(
        &mut lower,
        "main",
        span,
        &frame.inputs,
        &frame.classical_inputs,
        frame.start,
        &result,
        Effect::Unitary,
    )
    .unwrap();
    assert_eq!(raw.quantum_inputs, quantum_inputs);
    assert_eq!(
        raw.quantum_outputs,
        quantum_inputs
            .iter()
            .map(|port| port.token)
            .collect::<Vec<_>>()
    );
    assert_eq!(raw.classical_outputs, [c, c]);
    assert_eq!(
        raw.classical_inputs, classical_inputs,
        "retained frame must contain the same original actual ordinary input IDs"
    );
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.compiler.instrument_evidence.is_empty());
}

#[test]
fn empty_ordinary_ssa_keeps_zero_width_owner_and_source_gate() {
    let project = project(
        "#![no_implicit_prelude]\npub enum Mark{Only}pub unitary fn route(c:Unit,b:Bits<0>,q:Q<Mark>)->(Unit,Bits<0>,Q<Mark>){(c,b,q)}",
    );
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::route").unwrap();
    let (parameters, _) = compiler.signature(&key).unwrap();
    let span = compiler.declarations[&key].span;
    let mut lower = lowerer(&mut compiler);
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    let arguments = parameters
        .iter()
        .map(|ty| lower.input(ty, "main", span, &mut quantum_inputs, &mut classical_inputs))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    assert!(matches!(
        &arguments[..],
        [Value::Unit, Value::EmptyBits, Value::Quantum(..)]
    ));
    let frame = Frame::start(&mut lower, key, &arguments).unwrap().unwrap();
    assert!(frame.requires_source_gate());
    let result = Value::Tuple(arguments);
    let raw = retained_raw(
        &mut lower,
        "main",
        span,
        &frame.inputs,
        &frame.classical_inputs,
        frame.start,
        &result,
        Effect::Unitary,
    )
    .unwrap();
    assert!(raw.classical_inputs.is_empty() && raw.classical_outputs.is_empty());
    assert_eq!(raw.quantum_inputs.len(), 1);
    assert_eq!(raw.quantum_inputs[0].shape.bits, 0);
    assert!(raw.quantum_inputs[0].wires.is_empty());
    assert_eq!(raw.quantum_outputs, [raw.quantum_inputs[0].token]);
    assert!(lower.compiler.checked.is_empty());
}

#[test]
fn aliased_ordinary_actuals_share_one_physical_input_without_losing_copies() {
    let project = project(
        "#![no_implicit_prelude]\npub enum Mark{Only}pub unitary fn route(c:Bit,d:Bit,q:Q<Mark>)->((Bit,Bit),Q<Mark>){((c,d),q)}",
    );
    let mut compiler = untrusted_compiler(&project);
    let key = compiler.source.resolution.qualified("main::route").unwrap();
    let (parameters, _) = compiler.signature(&key).unwrap();
    let span = compiler.declarations[&key].span;
    let mut lower = lowerer(&mut compiler);
    let mut quantum_inputs = Vec::new();
    let mut classical_inputs = Vec::new();
    let c = lower
        .input(
            &parameters[0],
            "main",
            span,
            &mut quantum_inputs,
            &mut classical_inputs,
        )
        .unwrap();
    let q = lower
        .input(
            &parameters[2],
            "main",
            span,
            &mut quantum_inputs,
            &mut classical_inputs,
        )
        .unwrap();
    let arguments = vec![c.clone(), c, q];
    let frame = Frame::start(&mut lower, key, &arguments).unwrap().unwrap();
    assert_eq!(arguments[0], arguments[1]);
    assert!(frame.requires_source_gate());
    let result = Value::Pair(
        Box::new(Value::Pair(
            Box::new(arguments[0].clone()),
            Box::new(arguments[1].clone()),
        )),
        Box::new(arguments[2].clone()),
    );
    let raw = retained_raw(
        &mut lower,
        "main",
        span,
        &frame.inputs,
        &frame.classical_inputs,
        frame.start,
        &result,
        Effect::Unitary,
    )
    .unwrap();
    assert_eq!(raw.classical_inputs, classical_inputs);
    assert_eq!(raw.classical_inputs.len(), 1);
    assert_eq!(
        raw.classical_outputs,
        [classical_inputs[0], classical_inputs[0]]
    );
    assert_eq!(raw.quantum_inputs, quantum_inputs);
    assert_eq!(raw.quantum_inputs[0].shape.bits, 0);
    assert!(lower.compiler.checked.is_empty());
    assert!(lower.compiler.function_evidence.is_empty());
    assert!(lower.compiler.instrument_evidence.is_empty());
}
