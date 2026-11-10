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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn native_v5_compares_the_original_direct_selection_and_retains_its_runtime_request() {
    use crate::frontend::compile::{lower::lower_function, snapshot_tests::compiler};

    let source = "#![no_implicit_prelude]
unitary fn keep(q: Q<Bit>) -> Q<Bit> { q }
unitary fn sign(q: Q<Bit>) -> Q<Bit> { phase[1,1](q) }
pub unitary fn route(s: Q<Bit>, q: Q<Bit>) -> (Q<Bit>,Q<Bit>) {
    qmatch(s,q) { 0 => keep, 1 => sign }
}
";
    let project = project(source);
    let mut compiler = compiler(&project);
    for name in ["main::keep", "main::sign"] {
        let key = compiler.source.resolution.qualified(name).unwrap();
        let program = lower_function(&mut compiler, &key).unwrap();
        compiler.checked.insert(key, program);
    }
    let route = compiler.source.resolution.qualified("main::route").unwrap();
    compiler.force_typed_root = true;
    compiler.selected_entry = Some(route);
    let program = lower_function(&mut compiler, &route).unwrap();
    let (artifact, request) = crate::interchange::qmatch::v5::proposal(
        program.raw(),
        Arc::new(program.runtime_result().unwrap().clone()),
        program.source_context().unwrap(),
        &[("main".into(), source.into())],
    )
    .unwrap();
    let bytes = request.encode().unwrap();
    let checked = compiler
        .kernel
        .check_qmatch_source_v5(&artifact, &bytes)
        .unwrap();
    assert_eq!(checked.artifact(), artifact);
    assert_eq!(checked.request(), Some(bytes.as_slice()));
    assert_eq!(
        checked.program().runtime_result(),
        Some(request.runtime.as_ref())
    );
    let rechecked = compiler.kernel.check_program(checked.program()).unwrap();
    assert!(std::ptr::eq(
        rechecked.program().runtime_result().unwrap(),
        checked.program().runtime_result().unwrap(),
    ));
    assert!(
        compiler
            .kernel
            .check_qmatch_source(&artifact, &bytes)
            .is_err()
    );
}

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn named_call_keeps_its_literal_qmatch_and_each_supplied_provider() {
    use crate::frontend::compile::{lower::lower_function, snapshot_tests::compiler};
    use crate::interchange::qmatch::{OperationNode as Node, OriginalBody};

    let source = "#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Identity:Bit=reference(keep);
meaning Sign:Bit=reference(sign);
unitary fn choose[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U) {
    qmatch(s,q){0=>keep,1=>checked_op(U,Identity)}
}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){
    choose[then_op(sign,sign)](s,q)
}
";
    let project = project(source);
    let mut compiler = compiler(&project);
    for name in ["main::keep", "main::sign"] {
        let key = compiler.source.resolution.qualified(name).unwrap();
        let program = lower_function(&mut compiler, &key).unwrap();
        compiler.checked.insert(key, program);
    }
    let meaning = compiler
        .source
        .resolution
        .qualified("main::Identity")
        .unwrap();
    compiler.compile_meaning(&meaning).unwrap();
    let route = compiler.source.resolution.qualified("main::route").unwrap();
    compiler.force_typed_root = true;
    compiler.selected_entry = Some(route);
    let program = lower_function(&mut compiler, &route).unwrap();
    let caller = program.source_context().unwrap();
    let [(call, body)] = caller.calls.as_slice() else {
        panic!("expected the original named call")
    };
    assert_eq!(call.offset as usize, source.find("choose[then_op").unwrap());
    let [(formal, actual)] = body.supplies.as_slice() else {
        panic!("callee's original Op actual")
    };
    assert_eq!(formal, "U");
    assert!(matches!(
        actual.description.nodes.as_slice(),
        [
            Node::Provider { .. },
            Node::Provider { .. },
            Node::Then(0, 1)
        ]
    ));
    let [site] = body.selections.as_slice() else {
        panic!("missing the original Bit selection in its callee: {body:?}")
    };
    assert_eq!(
        site.position.offset as usize,
        source.find("qmatch(s,q)").unwrap()
    );
    assert_eq!((site.position.start, site.position.count), (0, call.count));
    let [plain, refined] = site.arms.as_slice() else {
        panic!("written arms")
    };
    let plain = plain.operation.as_ref().unwrap();
    assert!(
        matches!(plain.description.nodes.as_slice(), [Node::Provider { function, .. }] if function == "keep")
    );
    let supplied = refined.operation.as_ref().unwrap();
    assert!(
        matches!(supplied.description.nodes.as_slice(), [
        Node::Provider { function: first, .. }, Node::Provider { function: second, .. },
        Node::Then(0,1), Node::Formal { function, ordinal: 0, operations, .. },
        Node::Requested { child: 3, function: meaning, .. }
    ] if first == "sign" && second == "sign" && function == "choose" && operations == &[("U".into(), 2)] && meaning == "Identity"),
        "original operation graph: {:?}",
        supplied.description
    );
    assert!(matches!(
        supplied.bodies.as_slice(),
        [OriginalBody::Function { .. }, OriginalBody::Function { .. }]
    ));
    let [group] = supplied.meaning_references.as_slice() else {
        panic!("one original requested Meaning")
    };
    assert!(
        matches!(group.as_slice(), [OriginalBody::Pure { program, .. }] if program.raw().operations.is_empty())
    );
    let (artifact, request) = crate::interchange::qmatch::v5::proposal(
        program.raw(),
        Arc::new(program.runtime_result().unwrap().clone()),
        caller,
        &[("main".into(), source.into())],
    )
    .unwrap();
    let bytes = request.encode().unwrap();
    let view = compiler
        .kernel
        .qmatch_context_view(&artifact, &bytes)
        .unwrap();
    assert!(view.starts_with(b"QDV1"));
    assert_eq!(
        crate::interchange::qmatch::v5::Request::decode(&bytes).unwrap(),
        request
    );
    let [call] = request.context.calls.as_slice() else {
        panic!("one original caller interval")
    };
    assert_eq!(call.body.bodies.len(), 5);
    let [actual, keep, refined] = call.body.references.as_slice() else {
        panic!("one prefix graph and two original arms")
    };
    assert!(actual.is_empty() && keep.is_empty());
    assert!(matches!(refined.as_slice(), [leaves] if leaves.len()==1));
    let mut regrouped = request.clone();
    regrouped.context.calls[0].body.references.swap(0, 2);
    assert_ne!(
        view,
        compiler
            .kernel
            .qmatch_context_view(&artifact, &regrouped.encode().unwrap())
            .unwrap()
    );
    let mut missing = request.clone();
    missing.context.calls[0].body.references[2][0].clear();
    assert!(
        compiler
            .kernel
            .qmatch_context_view(&artifact, &missing.encode().unwrap())
            .is_err()
    );
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

#[cfg_attr(
    not(qleisli_native_tests),
    ignore = "native-kernel gate: requires QLEISLI_KERNEL"
)]
#[test]
fn original_general_nested_meaning_proposal() {
    use crate::frontend::compile::{lower::lower_function, snapshot_tests::compiler};
    let source = r#"#![no_implicit_prelude]
unitary fn keep(q:Q<Bit>)->Q<Bit>{q}
unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}
meaning Inner:Bit=reference(sign);
meaning Outer:Bit=reference(keep);
unitary fn choose[const W:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(W),Controllable(W) {qmatch(s,q){0=>keep,1=>checked_op(W,Outer)}}
unitary fn relay[const U:Op<Bit>,const V:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>)
    requires Applicable(U),Controllable(U),Applicable(V),Controllable(V) {choose[then_op(U,V)](s,q)}
pub unitary fn route(s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>){relay[checked_op(sign,Inner),sign](s,q)}
"#;
    let project = project(source);
    let mut compiler = compiler(&project);
    for name in ["main::keep", "main::sign"] {
        let key = compiler.source.resolution.qualified(name).unwrap();
        let program = lower_function(&mut compiler, &key).unwrap();
        compiler.checked.insert(key, program);
    }
    for name in ["main::Inner", "main::Outer"] {
        let key = compiler.source.resolution.qualified(name).unwrap();
        compiler.compile_meaning(&key).unwrap();
    }
    let route = compiler.source.resolution.qualified("main::route").unwrap();
    // Keep the original Raw producer as a baseline for the public typed route.
    compiler.selected_entry = Some(route);
    let program = lower_function(&mut compiler, &route).unwrap();
    let caller = program.source_context().expect("original root body");
    let [(_, relay)] = caller.calls.as_slice() else {
        panic!("one original relay")
    };
    assert_eq!(
        relay
            .supplies
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["U", "V"]
    );
    let [(_, choose)] = relay.calls.as_slice() else {
        panic!("one original choose")
    };
    assert_eq!(
        choose
            .supplies
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        ["W"]
    );
    assert_eq!(choose.selections.len(), 1);
    // This is untrusted test metadata for the fixed two-Bit library interface.
    // The same independently checked body request must validate it before any
    // source claim. No typed accepted handle or public entry is manufactured.
    use crate::interchange::{carrier, ordinary_root, runtime_root};
    let bit = vec![
        runtime_root::Atom::Quantum,
        runtime_root::Atom::Finite(carrier::Atom::Bit),
    ];
    let owner = |port: &crate::ir::QuantumPort| {
        runtime_root::Storage::Quantum(carrier::Owner {
            port: port.clone(),
            basis: vec![carrier::Atom::Bit],
        })
    };
    let runtime = runtime_root::Request {
        selection: ordinary_root::Selection::Exported,
        module: "main".into(),
        declaration: "route".into(),
        static_bases: vec![],
        static_naturals: vec![],
        parameters: vec![bit.clone(), bit.clone()],
        input_storage: program
            .raw()
            .quantum_inputs
            .iter()
            .map(|p| vec![owner(p)])
            .collect(),
        input_rows: vec![vec![]],
        result: [
            vec![runtime_root::Atom::Finite(carrier::Atom::Pair)],
            bit.clone(),
            bit,
        ]
        .concat(),
        storage: std::iter::once(runtime_root::Storage::Tuple(2))
            .chain(program.output_ports().iter().map(owner))
            .collect(),
        public_effect: Effect::Unitary,
    };
    let (artifact, request) = crate::interchange::qmatch::v5::proposal(
        program.raw(),
        Arc::new(runtime),
        caller,
        &[("main".into(), source.into())],
    )
    .unwrap();
    let bytes = request.encode().unwrap();
    let view = compiler
        .kernel
        .qmatch_context_view(&artifact, &bytes)
        .unwrap();
    assert!(
        view.starts_with(b"QDV1"),
        "inspection only; not native body acceptance"
    );
    assert_eq!(
        artifact,
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/qmatch_v030/general-meaning-artifact.json"
        ))
    );
    assert_eq!(
        bytes,
        include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/qmatch_v030/general-meaning-request.json"
        ))
    );
    let selected = crate::frontend::compile::ParsedProgram::parse(
        crate::edition::Edition::E2026,
        BTreeMap::from([("main".into(), source.into())]),
    )
    .unwrap()
    .instantiate_runtime_with_types(
        "main::route",
        Default::default(),
        Default::default(),
        Default::default(),
    )
    .unwrap()
    .compile_runtime_with_kernel(&compiler.kernel)
    .unwrap();
    let checked = selected.program();
    assert!(checked.qmatch_source_checked());
    assert_eq!(checked.artifact(), artifact);
    assert_eq!(checked.request().unwrap(), bytes);
    assert!(
        compiler
            .kernel
            .check_program(checked)
            .unwrap()
            .native_exact_work()
            <= 20_000_000
    );
}
