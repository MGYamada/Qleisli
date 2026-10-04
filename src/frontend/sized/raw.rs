//! Source-bound finite proposals. This adapter supplies no acceptance decision.
//! Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{ElaboratedProgram, Error, Result, SourceType, SourceValue, Span};
use crate::frontend::types::Kind;
use crate::interchange::{Version, native};
use crate::ir::{ClassicalId, Effect, RawOp, RawProgram};
use std::collections::BTreeMap;

mod preservation;

const MAX_OPERATIONS: usize = 10_000;
const MAX_CALLS: usize = 1_024;
const MAX_DEPTH: usize = 16;
const MAX_CELLS: usize = 100_000;

/// An immutable finite transport proposal alongside its exact source instance.
///
/// This initial adapter supports ordinary Unit/Bit/product values and ordinary
/// calls. Other source capabilities reject explicitly. Native Raw validity and
/// source-step correspondence are distinct checks; neither proves that source
/// elaboration itself preserves meaning. The source retains whole argument and
/// result types, which the flat classical SSA transport cannot represent.
#[derive(Clone, Debug)]
pub struct RawSourceProposal {
    source: ElaboratedProgram,
    proposal: native::Proposal,
}
impl RawSourceProposal {
    pub fn source(&self) -> &ElaboratedProgram {
        &self.source
    }
    pub fn proposal(&self) -> &native::Proposal {
        &self.proposal
    }
    pub fn payload(&self) -> &[u8] {
        self.proposal.artifact()
    }
    /// Check the actual native-accepted artifact against the retained ordered
    /// source steps. This does not issue an execution handle or establish the
    /// AST-to-step translation. No independent classical meaning was requested.
    pub fn validate_source_steps(&self, accepted: &native::AcceptedProgram) -> Result<()> {
        if accepted.artifact() != self.payload() || accepted.request().is_some() {
            return Err(Error::new(
                "preservation",
                Span::default(),
                "native accepted artifact differs from the source-bound Raw proposal",
            ));
        }
        preservation::validate(&self.source, accepted.raw())
    }
}

fn located(source: &ElaboratedProgram, id: usize, span: Span, message: &str) -> Error {
    let path = source.definitions()[id].path();
    Error::new("unsupported", span, message)
        .in_module(path.rsplit_once("::").map_or(path, |(module, _)| module))
}

fn bit_count(ty: &SourceType) -> Option<usize> {
    match &ty.kind {
        Kind::Unit => Some(0),
        Kind::Bit => Some(1),
        Kind::Tuple(fields) => fields
            .iter()
            .try_fold(0usize, |n, field| n.checked_add(bit_count(field)?)),
        Kind::Bits(_) | Kind::Q(_) => None,
    }
}

fn effect(source: &ElaboratedProgram) -> Effect {
    match source.definitions()[source.root()].effect() {
        "unitary" => Effect::Unitary,
        "iso" => Effect::Iso,
        "observe" => Effect::Observe,
        _ => unreachable!("private source effect"),
    }
}

// Capability selection precedes emission and native acceptance. In particular,
// a rejected hierarchy request is never retried under a weaker Raw request.
fn check_profile(source: &ElaboratedProgram) -> Result<()> {
    for (id, definition) in source.definitions().iter().enumerate() {
        if !definition.operations().is_empty() {
            return Err(located(
                source,
                id,
                definition.span(),
                "finite ordinary source lowering does not yet support operation providers",
            ));
        }
        for value in definition.inputs().iter().chain([definition.output()]) {
            if bit_count(value.ty()).is_none() {
                return Err(located(
                    source,
                    id,
                    definition.span(),
                    "finite ordinary source lowering currently requires Unit, Bit or exact products; quantum and Bits values need their explicit target support",
                ));
            }
        }
        for step in definition.steps() {
            if step
                .inputs()
                .iter()
                .chain([step.output()])
                .any(|value| bit_count(value.ty()).is_none())
            {
                return Err(located(
                    source,
                    id,
                    step.span(),
                    "finite ordinary source lowering requires ordinary intermediate values",
                ));
            }
            if step.boolean().is_none() && step.called_definition().is_none() {
                return Err(located(
                    source,
                    id,
                    step.span(),
                    "finite ordinary source lowering does not yet support this primitive or operation capability",
                ));
            }
        }
    }
    Ok(())
}

type Values = BTreeMap<u32, ClassicalId>;

fn read(value: &SourceValue, values: &Values) -> Vec<ClassicalId> {
    match &value.ty().kind {
        Kind::Unit => vec![],
        Kind::Bit => vec![values[&value.identity().expect("ordinary Bit identity")]],
        Kind::Tuple(_) => value
            .fields()
            .iter()
            .flat_map(|v| read(v, values))
            .collect(),
        _ => unreachable!("preflighted ordinary source type"),
    }
}

fn bind(value: &SourceValue, ids: &[ClassicalId], values: &mut Values) {
    match &value.ty().kind {
        Kind::Unit => debug_assert!(ids.is_empty()),
        Kind::Bit => {
            debug_assert_eq!(ids.len(), 1);
            values.insert(value.identity().expect("ordinary Bit identity"), ids[0]);
        }
        Kind::Tuple(_) => {
            let mut offset = 0;
            for field in value.fields() {
                let count = bit_count(field.ty()).expect("preflighted ordinary type");
                bind(field, &ids[offset..offset + count], values);
                offset += count;
            }
            debug_assert_eq!(offset, ids.len());
        }
        _ => unreachable!("preflighted ordinary source type"),
    }
}

struct Emitter<'a> {
    source: &'a ElaboratedProgram,
    operations: Vec<RawOp>,
    next_classical: u32,
    calls: usize,
    cells: usize,
}
impl Emitter<'_> {
    fn charge_value(&mut self, value: &SourceValue, span: Span) -> Result<()> {
        self.cells = self
            .cells
            .saturating_add(value.ty().owner_shape_size().nodes);
        if self.cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "finite source lowering exceeds 100000 value cells",
            ));
        }
        Ok(())
    }
    fn fresh(&mut self) -> ClassicalId {
        let value = ClassicalId(self.next_classical);
        self.next_classical += 1;
        value
    }
    fn invoke(
        &mut self,
        id: usize,
        arguments: Vec<Vec<ClassicalId>>,
        depth: usize,
    ) -> Result<Vec<ClassicalId>> {
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(Error::new(
                "limit",
                Span::default(),
                "finite source lowering exceeds call/depth capacity",
            ));
        }
        let definition = &self.source.definitions()[id];
        let mut values = Values::new();
        debug_assert_eq!(arguments.len(), definition.inputs().len());
        for (value, ids) in definition.inputs().iter().zip(arguments) {
            self.charge_value(value, definition.span())?;
            bind(value, &ids, &mut values);
        }
        for step in definition.steps() {
            let mut inputs = vec![];
            for value in step.inputs() {
                self.charge_value(value, step.span())?;
                inputs.push(read(value, &values));
            }
            let output = if let Some(operation) = step.boolean() {
                let operands: Vec<_> = inputs.iter().map(|ids| ids[0]).collect();
                if self.operations.len() >= MAX_OPERATIONS {
                    return Err(Error::new(
                        "limit",
                        step.span(),
                        "finite source lowering exceeds 10000 operations",
                    )
                    .in_module(step.module()));
                }
                let output = self.fresh();
                self.operations.push(
                    crate::frontend::ordinary::emit(operation, &operands, output)
                        .expect("checked Boolean operand arity"),
                );
                vec![output]
            } else {
                self.invoke(
                    step.called_definition().expect("preflighted ordinary call"),
                    inputs,
                    depth + 1,
                )?
            };
            self.charge_value(step.output(), step.span())?;
            bind(step.output(), &output, &mut values);
        }
        self.charge_value(definition.output(), definition.span())?;
        Ok(read(definition.output(), &values))
    }
}

pub(super) fn lower(source: &ElaboratedProgram) -> Result<RawSourceProposal> {
    check_profile(source)?;
    let root = &source.definitions()[source.root()];
    let mut emitter = Emitter {
        source,
        operations: vec![],
        next_classical: 0,
        calls: 0,
        cells: 0,
    };
    let mut arguments: Vec<Vec<_>> = vec![];
    for value in root.inputs() {
        emitter.charge_value(value, root.span())?;
        arguments.push(
            (0..bit_count(value.ty()).expect("preflighted ordinary type"))
                .map(|_| emitter.fresh())
                .collect(),
        );
    }
    let classical_inputs = arguments.iter().flatten().copied().collect();
    let classical_outputs = emitter.invoke(source.root(), arguments, 0)?;
    let raw = RawProgram {
        quantum_inputs: vec![],
        classical_inputs,
        operations: emitter.operations,
        quantum_outputs: vec![],
        classical_outputs,
        declared_effect: effect(source),
    };
    // Independent inspection of the generated Raw instructions catches producer
    // discrepancies before handing the untrusted bytes to the native boundary.
    preservation::validate(source, &raw)?;
    let proposal = native::Proposal::from_raw(&raw, None, Version::V2, None)
        .map_err(|error| Error::new("transport", root.span(), error.to_string()))?;
    Ok(RawSourceProposal {
        source: source.clone(),
        proposal,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sized::ParsedProgram;

    fn example() -> ElaboratedProgram {
        ParsedProgram::parse(BTreeMap::from([(
            "main".into(),
            "unitary fn f((a,b): (Bit,Bit)) -> (Bit,Bit,Bit) { (not a, a and b, a xor b) }\n\
             pub observe fn main() -> (Bit,Bit,Bit) { f((1,1)) }"
                .into(),
        )]))
        .unwrap()
        .instantiate("main::main", BTreeMap::new(), BTreeMap::new())
        .unwrap()
        .elaborate()
        .unwrap()
    }

    #[test]
    fn raw_source_replay_rejects_native_valid_semantic_and_structural_mutations() {
        let source = example();
        let proposal = source.lower_raw().unwrap();
        let kernel = native::Kernel::new(
            std::env::var_os("QLEISLI_KERNEL").expect("select the matching native checker"),
        );
        let accepted = kernel.accept(proposal.proposal()).unwrap();
        proposal.validate_source_steps(&accepted).unwrap();
        let original = accepted.raw();
        let mut mutations = vec![];
        let mut changed = original.clone();
        let index = changed
            .operations
            .iter()
            .position(|op| matches!(op, RawOp::ClassicalAnd { .. }))
            .unwrap();
        let RawOp::ClassicalAnd {
            left,
            right,
            output,
        } = &changed.operations[index]
        else {
            unreachable!()
        };
        changed.operations[index] = RawOp::ClassicalXor {
            left: *left,
            right: *right,
            output: *output,
        };
        mutations.push(("and changed to xor", changed));

        let mut changed = original.clone();
        let RawOp::ClassicalConst { value, .. } = &mut changed.operations[0] else {
            unreachable!()
        };
        *value = !*value;
        mutations.push(("literal substituted", changed));

        let mut changed = original.clone();
        changed.operations.push(RawOp::ClassicalConst {
            value: true,
            output: ClassicalId(900),
        });
        mutations.push(("extra unused operation", changed));

        let mut changed = original.clone();
        changed.classical_outputs.reverse();
        mutations.push(("output order reversed", changed));

        for (name, raw) in mutations {
            let accepted_mutation = kernel.accept_raw(raw).expect(name);
            // Exercise the direct opcode/tree matcher, not just the proposal's
            // outer byte-identity check. These programs remain native-valid.
            let error = preservation::validate(&source, accepted_mutation.raw()).expect_err(name);
            assert_eq!(error.code(), "preservation", "{name}: {error}");
            assert!(
                proposal.validate_source_steps(&accepted_mutation).is_err(),
                "{name}"
            );
        }
    }
}
