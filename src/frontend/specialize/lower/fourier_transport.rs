//! Inert original source and bounded Fourier producer replay, never acceptance.
//! Both actual artifacts still require fresh native checks. This records the
//! existing complete-trace factoring premise, not a Lean source theorem.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::specialize::elaborate::OperationKey;
use crate::interchange::json::{self, Value};
use std::sync::Arc;

const RETAINED_BYTES: usize = 16 << 20;
const RETAINED_CELLS: usize = 100_000;
// Same structural ceiling as the existing hierarchical runtime; each full
// Fourier word additionally keeps its original TRACE_WORK bound.
const REPLAY_WORK: usize = 2_000_000;

#[derive(Clone, PartialEq, Eq)]
struct Binding {
    caller: usize,
    step: usize,
    path: Vec<usize>,
    key: OperationKey,
    original: usize,
    actual: usize,
}

/// One immutable original, with exact caller/constructor selections and roots.
pub(super) struct Transport {
    pub(super) original: Arc<HierarchyProposal>,
    bindings: Vec<Binding>,
}

struct Rewrite {
    payload: Vec<u8>,
    comparison: Vec<u8>,
    graph: Vec<u8>,
    bindings: Vec<Binding>,
}

fn retained_bytes(
    original: &HierarchyProposal,
    payload: &[u8],
    graph: &[u8],
    comparison: &[u8],
) -> usize {
    [
        original.payload.len(),
        original.graph.len(),
        original.comparison.len(),
        original.precursor.len(),
        payload.len(),
        graph.len(),
        comparison.len(),
    ]
    .into_iter()
    .fold(0usize, usize::saturating_add)
}

fn invalid(message: &str) -> Error {
    preservation::invalid(message)
}
fn spend(work: &mut usize, amount: usize) -> Result<()> {
    *work = work
        .checked_sub(amount)
        .ok_or_else(|| limit("retained Fourier replay exceeds shared work"))?;
    Ok(())
}
fn parse(bytes: &[u8]) -> Result<Value> {
    if bytes.len() > RETAINED_BYTES {
        return Err(limit("retained Fourier graph exceeds proposal bytes"));
    }
    json::parse(bytes).map_err(|_| invalid("invalid retained Fourier JSON"))
}
fn bytes(value: &Value) -> Result<Vec<u8>> {
    json::encode(value).map_err(|_| invalid("invalid retained Fourier JSON"))
}
fn fields(value: &mut Value) -> Result<&mut BTreeMap<String, Value>> {
    if let Value::Object(fields) = value {
        Ok(fields)
    } else {
        Err(invalid("retained Fourier transport expected an object"))
    }
}

fn port_cells(port: &Port) -> usize {
    port.basis
        .storage_size(4096, 64)
        .map_or(RETAINED_CELLS + 1, |size| size.nodes)
        .saturating_add(port.axes.len())
        .saturating_add(4)
}
fn event_cells(event: &SourceEvent) -> usize {
    let items = |items: &[Item]| {
        items.iter().fold(0usize, |n, item| {
            n.saturating_add(match item {
                Item::Quantum(port) => port_cells(port),
                Item::Classical(values) => values.len().saturating_add(1),
            })
        })
    };
    fn frame<'a>(frame: impl Iterator<Item = FramePort<'a>>) -> usize {
        frame.fold(0usize, |n, port| {
            n.saturating_add(
                port.basis()
                    .storage_size(4096, 64)
                    .map_or(RETAINED_CELLS + 1, |size| size.nodes),
            )
            .saturating_add(port.axes().len())
            .saturating_add(4)
        })
    }
    12usize
        .saturating_add(event.call_path().len())
        .saturating_add(event.module().len())
        .saturating_add(items(&event.inputs))
        .saturating_add(items(&event.outputs))
        .saturating_add(event.preparation.as_ref().map_or(0, port_cells))
        .saturating_add(frame(event.input_frame()))
        .saturating_add(frame(event.output_frame()))
}
/// Debit the existing retained provenance as well as the added selectors.
/// Shared immutable Raw witnesses are counted once, never a fresh allowance.
fn source_cells(original: &HierarchyProposal) -> usize {
    let mut cells = original.source.witness_clone_cells().saturating_mul(2);
    for event in &original.events {
        cells = cells.saturating_add(event_cells(event));
    }
    for trace in &original.pure_traces {
        cells = cells.saturating_add(8);
        for port in trace.inputs.iter().chain(&trace.outputs) {
            cells = cells.saturating_add(port_cells(port));
        }
        for event in &trace.events {
            cells = cells.saturating_add(event_cells(event));
        }
    }
    cells = cells.saturating_add(original.zero_basis.len().saturating_mul(128));
    for movement in &original.moves {
        cells = cells.saturating_add(movement.crossed_events().len().saturating_add(2));
    }
    let mut witnesses = BTreeSet::new();
    for trace in &original.native_sources {
        cells = cells.saturating_add(8);
        if witnesses.insert(Arc::as_ptr(trace.retained_witness()) as usize) {
            cells = cells.saturating_add(trace.retained_witness().retained_cells());
        }
    }
    cells
}

/// Import complete original bytes; no native validity is inferred from parsing.
fn graph(bytes: &[u8], work: &mut usize) -> Result<(Graph, usize, u32)> {
    spend(work, bytes.len())?;
    let value = parse(bytes)?;
    let definitions = preservation::array(preservation::field(&value, "definitions")?)?;
    let meanings = preservation::array(preservation::field(&value, "meanings")?)?;
    let proofs = preservation::array(preservation::field(&value, "proofs")?)?;
    if definitions.is_empty()
        || definitions.len() > 10_000
        || definitions.len() != meanings.len()
        || definitions.len() != proofs.len()
    {
        return Err(invalid("retained Fourier tables have different lengths"));
    }
    let mut graph = Graph::new();
    let mut owner = 100;
    for ((definition, meaning), proof) in definitions.iter().zip(meanings).zip(proofs) {
        spend(work, 1)?;
        let (before, after) = preservation::endpoints(definition)?;
        for port in before.iter().chain(&after) {
            owner = owner.max(port.owner);
        }
        let definition = fourier::encoded(definition)?;
        let meaning = fourier::encoded(meaning)?;
        let proof = fourier::encoded(proof)?;
        graph.charge(definition.len() + meaning.len() + proof.len())?;
        graph.nodes.push(Node {
            before,
            after,
            definition,
            meaning,
            proof,
        });
    }
    for encoding in preservation::array(preservation::field(&value, "encodings")?)? {
        let encoding = fourier::encoded(encoding)?;
        graph.charge(encoding.len())?;
        graph.encodings.push(encoding);
    }
    let root = preservation::number(preservation::field(
        preservation::field(&value, "entry")?,
        "implementation",
    )?)?;
    if root >= graph.nodes.len() {
        return Err(invalid("retained Fourier entry is outside its graph"));
    }
    Ok((graph, root, owner))
}

/// Rebuild only the reachable original spine, replacing selected complete roots.
/// Every other complete body and rule is preserved, with exact index transport.
fn copy(
    source: &Graph,
    root: usize,
    replacements: &BTreeMap<usize, usize>,
    work: &mut usize,
) -> Result<(Graph, usize, BTreeMap<usize, usize>)> {
    struct CopyState {
        target: Graph,
        mapping: BTreeMap<usize, usize>,
        active: BTreeSet<usize>,
    }
    fn visit(
        source: &Graph,
        index: usize,
        replacements: &BTreeMap<usize, usize>,
        state: &mut CopyState,
        work: &mut usize,
        depth: usize,
    ) -> Result<usize> {
        spend(work, 1)?;
        if depth > 128 || !state.active.insert(index) {
            return Err(limit(
                "retained Fourier copy exceeds graph depth or has a cycle",
            ));
        }
        if let Some(&mapped) = state.mapping.get(&index) {
            state.active.remove(&index);
            return Ok(mapped);
        }
        if let Some(&replacement) = replacements.get(&index) {
            let mapped = visit(source, replacement, replacements, state, work, depth + 1)?;
            state.mapping.insert(index, mapped);
            state.active.remove(&index);
            return Ok(mapped);
        }
        let node = source
            .nodes
            .get(index)
            .ok_or_else(|| invalid("missing retained Fourier definition"))?;
        spend(
            work,
            node.definition.len() + node.meaning.len() + node.proof.len(),
        )?;
        let definition = parse(node.definition.as_bytes())?;
        let meaning = parse(node.meaning.as_bytes())?;
        let proof = parse(node.proof.as_bytes())?;
        // The existing Graph producer emits exactly these inert proof wrappers.
        // Refuse rather than erase a future nonempty template dependency.
        let expected = Value::object([
            ("template_version", Value::Number(1)),
            ("parameters", Value::Array(vec![])),
            ("references", Value::Array(vec![])),
        ]);
        if preservation::text(preservation::field(&proof, "kind")?)? != "equation"
            || preservation::field(&proof, "witness")? != &expected
            || preservation::number(preservation::field(&proof, "implementation")?)? != index
            || preservation::number(preservation::field(&proof, "meaning")?)? != index
        {
            return Err(invalid(
                "retained Fourier copy changes an original proof dependency",
            ));
        }
        let children = preservation::indices(preservation::field(&proof, "premises")?)?;
        spend(work, children.len())?;
        let mut premises = Vec::with_capacity(children.len());
        for child in children {
            premises.push(visit(source, child, replacements, state, work, depth + 1)?);
        }
        let remap = |value: &Value| {
            let body = preservation::field(value, "body")?;
            fourier::encoded(
                &fourier::remap_body(body, &state.mapping)
                    .ok_or_else(|| invalid("retained Fourier copy lost an original child"))?,
            )
        };
        let rule = preservation::tag(preservation::field(&proof, "rule")?)?;
        if preservation::field(&proof, "rule")?
            != &Value::object([("tag", Value::String(rule.into()))])
        {
            return Err(invalid(
                "retained Fourier copy cannot erase rule parameters",
            ));
        }
        for (name, ports) in [
            ("input_encoding", &node.before),
            ("output_encoding", &node.after),
        ] {
            let encoding = preservation::number(preservation::field(&proof, name)?)?;
            let actual = source
                .encodings
                .get(encoding)
                .ok_or_else(|| invalid("missing original Fourier encoding"))?;
            let side = side(ports, &[]);
            let expected = object(&[
                ("logical", side.clone()),
                ("physical", side),
                ("body", tagged("identity", &[])),
            ]);
            if parse(actual.as_bytes())? != parse(expected.as_bytes())? {
                return Err(invalid(
                    "retained Fourier copy cannot erase an original encoding",
                ));
            }
        }
        let mapped = state.target.add(
            node.before.clone(),
            node.after.clone(),
            remap(&definition)?,
            remap(&meaning)?,
            rule,
            premises,
        )?;
        state.mapping.insert(index, mapped);
        state.active.remove(&index);
        Ok(mapped)
    }
    let mut state = CopyState {
        target: Graph::new(),
        mapping: BTreeMap::new(),
        active: BTreeSet::new(),
    };
    let mapped = visit(source, root, replacements, &mut state, work, 0)?;
    Ok((state.target, mapped, state.mapping))
}

fn rewrite(original: &HierarchyProposal, work: &mut usize) -> Result<Option<Rewrite>> {
    let (source_graph, root, owner) = graph(&original.graph, work)?;
    let mut lower = Lower {
        source: &original.source,
        native_operations: &[],
        graph: source_graph,
        owner,
        pure: BTreeMap::new(),
        gate_cache: BTreeMap::new(),
        finite_gates: BTreeMap::new(),
        inline_visits: 0,
        zero_basis: vec![],
        pure_traces: vec![],
        native_sources: vec![],
        trace_zero_basis: false,
        pure_trace_cells: 0,
    };
    let mut wrappers = BTreeMap::<usize, Vec<usize>>::new();
    for (index, node) in lower.graph.nodes.iter().enumerate() {
        spend(work, 1)?;
        let definition = parse(node.definition.as_bytes())?;
        let body = preservation::field(&definition, "body")?;
        if preservation::tag(body)? == "sequence" {
            let children = preservation::indices(preservation::field(body, "children")?)?;
            if children.len() == 3 {
                wrappers.entry(children[1]).or_default().push(index);
            }
        }
    }
    let mut bindings = vec![];
    let mut replacements = BTreeMap::new();
    let mut cells = source_cells(original);
    if cells > RETAINED_CELLS {
        return Err(limit("retained Fourier source exceeds aggregate cells"));
    }
    for (caller, definition) in original.source.definitions().iter().enumerate() {
        for (step, source_step) in definition.steps().iter().enumerate() {
            let Some(operation) = source_step.operation() else {
                continue;
            };
            let mut pending = vec![(operation, vec![])];
            while let Some((operation, path)) = pending.pop() {
                spend(work, 1)?;
                if path.len() > 64 {
                    return Err(limit("retained Fourier source selector exceeds depth"));
                }
                for (child, operation) in operation.children().iter().enumerate().rev() {
                    cells = cells.saturating_add(path.len().saturating_add(1));
                    if cells > RETAINED_CELLS {
                        return Err(limit(
                            "retained Fourier selector paths exceed aggregate cells",
                        ));
                    }
                    let mut nested = path.clone();
                    nested.push(child);
                    pending.push((operation, nested));
                }
                let Some(definition) = operation.definition() else {
                    continue;
                };
                if zero_basis::operation_uses_table(&original.source, operation)? {
                    continue;
                }
                // Keep the full caller-visible effect and exact selected instance.
                cells = cells.saturating_add(
                    operation
                        .expanded_key_cells()
                        .saturating_mul(2)
                        .saturating_add(path.len().saturating_mul(2))
                        .saturating_add(8),
                );
                if cells > RETAINED_CELLS {
                    return Err(limit("retained Fourier selectors exceed source cells"));
                }
                let key = operation.key();
                if !matches!(&key, OperationKey::SourceEffect(Effect::Unitary, _)) {
                    continue;
                }
                let Some(trace) = original
                    .pure_traces
                    .iter()
                    .find(|t| t.definition == definition)
                else {
                    continue;
                };
                for &closed in wrappers.get(&trace.root).into_iter().flatten() {
                    if replacements.contains_key(&closed) {
                        continue;
                    }
                    let node = &lower.graph.nodes[closed];
                    if node.before != trace.inputs || node.after != trace.inputs {
                        continue;
                    }
                    let candidate = lower.factor_fourier_with_work(closed, work)?;
                    if candidate != closed {
                        replacements.insert(closed, candidate);
                        bindings.push(Binding {
                            caller,
                            step,
                            path: path.clone(),
                            key: key.clone(),
                            original: closed,
                            actual: candidate,
                        });
                    }
                }
            }
        }
    }
    if replacements.is_empty() {
        return Ok(None);
    }
    let (target, target_root, mapping) = copy(&lower.graph, root, &replacements, work)?;
    // An outer complete-word replacement can subsume an inner candidate. Only
    // actually emitted replacements need actual roots; the unchanged original
    // still retains every inner source root and its native/source obligations.
    bindings.retain(|binding| mapping.contains_key(&binding.original));
    for binding in &mut bindings {
        binding.actual = *mapping
            .get(&binding.original)
            .ok_or_else(|| invalid("retained Fourier replacement is not actually reachable"))?;
    }
    let target_graph = target.artifact(target_root).into_bytes();
    let mut payload = parse(&original.payload)?;
    fields(&mut payload)?.insert("circuit".into(), parse(&target_graph)?);
    let mut comparison = parse(&original.comparison)?;
    fields(&mut comparison)?.insert(
        "circuit".into(),
        parse(target.comparison(target_root).as_bytes())?,
    );
    Ok(Some(Rewrite {
        payload: bytes(&payload)?,
        comparison: bytes(&comparison)?,
        graph: target_graph,
        bindings,
    }))
}

pub(super) fn propose(original: HierarchyProposal) -> Result<HierarchyProposal> {
    if !original.instrument || !zero_basis::needs_replay(&original) {
        return Ok(original);
    }
    let mut work = REPLAY_WORK;
    let rewritten = match rewrite(&original, &mut work) {
        Ok(Some(rewritten)) => rewritten,
        Ok(None) => return Ok(original),
        Err(error) if error.code() == "limit" => return Ok(original),
        Err(error) => return Err(error),
    };
    let retained = retained_bytes(
        &original,
        &rewritten.payload,
        &rewritten.graph,
        &rewritten.comparison,
    );
    if retained > RETAINED_BYTES {
        return Ok(original);
    }
    let source = original.source.clone();
    let transport = Arc::new(Transport {
        original: Arc::new(original),
        bindings: rewritten.bindings,
    });
    let fallback = transport.original.clone();
    let result = HierarchyProposal {
        source,
        payload: rewritten.payload,
        comparison: rewritten.comparison,
        graph: rewritten.graph,
        precursor: vec![],
        instrument: true,
        events: vec![],
        moves: vec![],
        zero_basis: vec![],
        pure_traces: vec![],
        native_sources: vec![],
        fourier_transport: Some(transport),
    };
    match validate(&result) {
        Ok(()) => Ok(result),
        Err(error) if error.code() == "limit" => {
            // Optional replay cannot remove the valid original producer path.
            drop(result);
            Arc::try_unwrap(fallback)
                .map_err(|_| invalid("optional Fourier rollback retained an unexpected owner"))
        }
        Err(error) => Err(error),
    }
}

/// Replay against the immutable original and exact actual bytes; no accepted
/// handle or semantic/source guarantee is created by this producer-side audit.
pub(super) fn validate(proposal: &HierarchyProposal) -> Result<()> {
    let Some(transport) = &proposal.fourier_transport else {
        return Ok(());
    };
    let original = &transport.original;
    if retained_bytes(
        original,
        &proposal.payload,
        &proposal.graph,
        &proposal.comparison,
    ) > RETAINED_BYTES
    {
        return Err(limit(
            "retained original and actual Fourier bytes exceed proposal capacity",
        ));
    }
    if !proposal.instrument
        || original.fourier_transport.is_some()
        || !proposal.source.same_witness_source(&original.source)
        || !proposal.events.is_empty()
        || !proposal.moves.is_empty()
        || !proposal.zero_basis.is_empty()
        || !proposal.pure_traces.is_empty()
        || !proposal.native_sources.is_empty()
        || !proposal.precursor.is_empty()
    {
        return Err(invalid(
            "retained Fourier proposal changes its original source binding",
        ));
    }
    zero_basis::validate(original)?;
    preservation::validate(original)?;
    let mut work = REPLAY_WORK;
    let expected = rewrite(original, &mut work)?
        .ok_or_else(|| invalid("retained Fourier proposal has no complete source rewrite"))?;
    if expected.payload != proposal.payload
        || expected.graph != proposal.graph
        || expected.comparison != proposal.comparison
        || expected.bindings != transport.bindings
    {
        return Err(invalid(
            "actual Fourier graph differs from the complete retained rewrite",
        ));
    }
    // Re-read both graphs under the same remaining replay budget, not flags.
    let (source, _, _) = graph(&original.graph, &mut work)?;
    let (actual, _, _) = graph(&proposal.graph, &mut work)?;
    for binding in &transport.bindings {
        if !fourier::retained_trace_pair(
            &source,
            binding.original,
            &actual,
            binding.actual,
            &mut work,
        ) {
            return Err(invalid(
                "actual Fourier replacement differs from the complete source trace",
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::compile::ParsedProgram;
    use crate::interchange::hierarchical::{Kernel, execution::ExecutionLimits};

    // One fixed H Fourier stage plus one ordinary basis preparation. The
    // reference remains outside the source and is retained by native execution.
    const SOURCE: &str = "
        isometry fn fresh()->Q<Bit>{basis unit(()) as () {0}}
        unitary fn fourier(q:Q<Bits<1>>)->Q<Bits<1>>{
            let (high,rest)=take_bit[1,0](q);
            let high=h(high);put_bit[1,0](high,rest)
        }
        pub observe fn entry(q:Q<Bits<1>>)->(Bits<1>,Q<Bits<1>>){
            let q=adjoint(fourier)(q);let fresh=fresh();
            let bit=measure_z(fresh);(prepend_bit[0](bit,empty_bits()),q)
        }
    ";
    fn proposal() -> HierarchyProposal {
        proposal_with_source(SOURCE)
    }
    fn proposal_with_source(source: &str) -> HierarchyProposal {
        ParsedProgram::parse(
            crate::edition::Edition::E2026,
            BTreeMap::from([("main".into(), source.into())]),
        )
        .unwrap()
        .instantiate("main::entry", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
        .lower()
        .unwrap()
    }

    #[test]
    fn fixed_fourier_transport_retains_every_original_source_root_and_selector() {
        let proposal = proposal();
        let transport = proposal.fourier_transport.as_ref().unwrap();
        assert!(!transport.original.pure_traces.is_empty());
        assert!(!transport.original.zero_basis.is_empty());
        assert_ne!(proposal.pure_graph(), proposal.source_trace_graph());
        assert!(!proposal.source_events().is_empty());
        assert!(!transport.bindings.is_empty());
        zero_basis::validate(&transport.original).unwrap();
        preservation::validate(&transport.original).unwrap();
        validate(&proposal).unwrap();
        let mut other = proposal.clone();
        other.source = self::proposal().source;
        assert!(validate(&other).is_err());
    }

    #[test]
    fn outer_fixed_fourier_replacement_retains_subsumed_inner_source_obligations() {
        let source = format!(
            "{SOURCE}
             fn invoke[const U:Op<Bits<1>>](q:Q<Bits<1>>)->Q<Bits<1>>
                 requires Applicable(U), Adjointable(U) {{U(q)}}
             unitary fn outer(q:Q<Bits<1>>)->Q<Bits<1>>{{invoke[fourier](q)}}"
        )
        .replacen("adjoint(fourier)(q)", "adjoint(outer)(q)", 1);
        let proposal = proposal_with_source(&source);
        let transport = proposal.fourier_transport.as_ref().unwrap();
        assert!(transport.original.pure_traces.iter().any(|trace| {
            transport.original.source.definitions()[trace.definition].path() == "main::invoke"
        }));
        // The original invoke/root/native obligations remain even when only the
        // outer complete word is emitted; this must not be a dangling binding.
        zero_basis::validate(&transport.original).unwrap();
        validate(&proposal).unwrap();
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn native_original_and_factored_fixed_fourier_keep_complex_reference_and_full_phase() {
        let kernel = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
            crate::edition::Edition::E2026,
        );
        let proposal = proposal();
        let original = &proposal.fourier_transport.as_ref().unwrap().original;
        let checked = kernel
            .check_instrument_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        proposal
            .validate_initialization_moves_native(&checked)
            .unwrap();
        let before = kernel
            .check_instrument_native(original.payload(), original.comparison_request())
            .unwrap();
        let s = std::f64::consts::FRAC_1_SQRT_2;
        let input = [[s, 0.0], [0.0, 0.0], [0.0, 0.0], [0.0, s]];
        // Quantum basis is fastest; reference r=0 contains (s,0), and r=1
        // contains (0,i*s). H acts separately on each complete reference block.
        let expected = [[0.5, 0.0], [0.5, 0.0], [0.0, 0.5], [0.0, -0.5]];
        for report in [&before, &checked] {
            let output = report
                .execute_instrument(
                    &input,
                    2,
                    ExecutionLimits {
                        max_amplitudes: 64,
                        max_steps: 10_000,
                    },
                )
                .unwrap();
            assert_eq!(output.measured_bits, 1);
            assert_eq!(output.residual_quantum_bits, 1);
            assert_eq!(output.reference_dimension, 2);
            assert_eq!(output.branches.len(), 2);
            assert_eq!(output.branches[0].len(), 4);
            assert_eq!(output.branches[1].len(), 4);
            for (actual, expected) in output.branches[0].iter().zip(expected) {
                assert!((actual[0] - expected[0]).abs() < 1e-12);
                assert!((actual[1] - expected[1]).abs() < 1e-12);
            }
            assert!(output.branches[1].iter().all(|z| z == &[0.0, 0.0]));
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn native_valid_x_cannot_replace_the_retained_fixed_fourier_h() {
        let kernel = Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
            crate::edition::Edition::E2026,
        );
        let mut changed = proposal();
        let mut work = REPLAY_WORK;
        let (actual, _, _) = graph(&changed.graph, &mut work).unwrap();
        let leaf = actual
            .nodes
            .iter()
            .position(|node| {
                let definition = parse(node.definition.as_bytes()).unwrap();
                preservation::tag(preservation::field(&definition, "body").unwrap()).unwrap()
                    == "leaf"
            })
            .unwrap();
        let mut producer = Lower {
            source: &changed.source,
            native_operations: &[],
            graph: Graph::new(),
            owner: 100,
            pure: BTreeMap::new(),
            gate_cache: BTreeMap::new(),
            finite_gates: BTreeMap::new(),
            inline_visits: 0,
            zero_basis: vec![],
            pure_traces: vec![],
            native_sources: vec![],
            trace_zero_basis: false,
            pure_trace_cells: 0,
        };
        let node = &actual.nodes[leaf];
        let x = producer
            .finite_gate(SingleGate::X, &node.before[0], &node.after[0])
            .unwrap();
        let definition = parse(producer.graph.nodes[x].definition.as_bytes()).unwrap();
        let meaning = parse(producer.graph.nodes[x].meaning.as_bytes()).unwrap();
        let mut mutated = parse(&changed.graph).unwrap();
        for (table, replacement) in [("definitions", definition), ("meanings", meaning)] {
            let Value::Array(rows) = fields(&mut mutated).unwrap().get_mut(table).unwrap() else {
                panic!("expected graph rows")
            };
            fields(&mut rows[leaf]).unwrap().insert(
                "body".into(),
                preservation::field(&replacement, "body").unwrap().clone(),
            );
        }
        changed.graph = bytes(&mutated).unwrap();
        let mut payload = parse(&changed.payload).unwrap();
        fields(&mut payload)
            .unwrap()
            .insert("circuit".into(), mutated);
        changed.payload = bytes(&payload).unwrap();
        let (mutated, root, _) = graph(&changed.graph, &mut work).unwrap();
        let mut request = parse(&changed.comparison).unwrap();
        fields(&mut request).unwrap().insert(
            "circuit".into(),
            parse(mutated.comparison(root).as_bytes()).unwrap(),
        );
        changed.comparison = bytes(&request).unwrap();
        // The complete X artifact is natively unitary and composed correctly;
        // that does not make it the retained original H source operation.
        let checked = kernel
            .check_instrument_native(changed.payload(), changed.comparison_request())
            .unwrap();
        assert!(
            changed
                .validate_initialization_moves_native(&checked)
                .is_err()
        );
    }
    #[cfg(unix)]
    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn source_validation_requires_a_fresh_original_check_after_main_acceptance() {
        use std::sync::atomic::{AtomicU64, Ordering};
        static SERIAL: AtomicU64 = AtomicU64::new(0);
        let original = std::fs::canonicalize(
            std::env::var_os("QLEISLI_KERNEL").expect("explicit native checker"),
        )
        .unwrap();
        let directory = std::env::temp_dir().join(format!(
            "qleisli-fourier-source-checker-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        let executable = directory.join("checker");
        if std::fs::hard_link(&original, &executable).is_err() {
            std::fs::copy(&original, &executable).unwrap();
        }
        let proposal = proposal();
        assert!(proposal.fourier_transport.is_some());
        let kernel = Kernel::new(&executable, crate::edition::Edition::E2026);
        let checked = kernel
            .check_instrument_native(proposal.payload(), proposal.comparison_request())
            .unwrap();
        proposal
            .validate_initialization_moves_native(&checked)
            .unwrap();
        std::fs::remove_file(&executable).unwrap();
        // The already accepted main payload and decoded execution plan remain;
        // neither can replace a fresh check of the retained original artifact.
        assert!(
            proposal
                .validate_initialization_moves_native(&checked)
                .is_err()
        );
    }
}
