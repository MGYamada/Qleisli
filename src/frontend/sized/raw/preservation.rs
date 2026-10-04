//! Independent comparison of a retained ordinary source-step graph with Raw IR.
//! This untrusted check issues neither native acceptance nor a source theorem.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

use crate::frontend::ordinary::Boolean;
use crate::frontend::sized::{
    ElaboratedProgram, Error, Result, SourceDefinition, SourceType, SourceValue, Span,
};
use crate::frontend::types::Kind;
use crate::ir::{ClassicalId, Effect, RawOp, RawProgram};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CALLS: usize = 1024;
const MAX_DEPTH: usize = 16;
const MAX_STEPS: usize = 10_000;
const MAX_CELLS: usize = 100_000;

#[derive(Clone, Copy)]
struct Site<'a> {
    module: &'a str,
    span: Span,
}
impl<'a> Site<'a> {
    fn definition(definition: &'a SourceDefinition) -> Self {
        Self {
            module: definition
                .path()
                .rsplit_once("::")
                .map_or(definition.path(), |(module, _)| module),
            span: definition.span(),
        }
    }
    fn error(self, code: &'static str, message: impl Into<String>) -> Error {
        Error::new(code, self.span, message).in_module(self.module)
    }
    fn invalid(self, message: impl Into<String>) -> Error {
        self.error("preservation", message)
    }
}

fn effect(name: &str, site: Site<'_>) -> Result<Effect> {
    match name {
        "unitary" => Ok(Effect::Unitary),
        "iso" => Ok(Effect::Iso),
        "observe" => Ok(Effect::Observe),
        _ => Err(site.invalid("unknown source effect")),
    }
}

type Environment = BTreeMap<u32, ClassicalId>;

struct Argument<'a> {
    ty: &'a SourceType,
    bits: Vec<ClassicalId>,
}

struct Replay<'a> {
    source: &'a ElaboratedProgram,
    raw: &'a RawProgram,
    cursor: usize,
    calls: usize,
    steps: usize,
    cells: usize,
    issued: BTreeSet<u32>,
}

impl Replay<'_> {
    /// Inspect exact constructors before collecting ordinary Bit leaves. In
    /// particular, neither Bits<0> nor a zero-width owner is ordinary Unit.
    fn atoms(&mut self, value: &SourceValue, site: Site<'_>) -> Result<Vec<u32>> {
        let mut pending = vec![(value, value.ty(), 0usize)];
        let mut result = Vec::new();
        while let Some((value, expected, depth)) = pending.pop() {
            self.cells += 1;
            if self.cells > MAX_CELLS || depth > 64 {
                return Err(site.error(
                    "limit",
                    "ordinary Raw replay exceeds its value-cell/depth bound",
                ));
            }
            if value.ty() != expected {
                return Err(site.invalid("source value field differs from its exact type tree"));
            }
            match &expected.kind {
                Kind::Unit => {
                    if value.identity().is_some() || !value.fields().is_empty() {
                        return Err(site.invalid("ordinary Unit has an identity or fields"));
                    }
                }
                Kind::Bit => {
                    if !value.fields().is_empty() {
                        return Err(site.invalid("ordinary Bit has product fields"));
                    }
                    result.push(
                        value.identity().ok_or_else(|| {
                            site.invalid("ordinary Bit lacks its source identity")
                        })?,
                    );
                }
                Kind::Tuple(fields) => {
                    if value.identity().is_some()
                        || fields.is_empty()
                        || fields.len() != value.fields().len()
                    {
                        return Err(site
                            .invalid("source product loses its exact arity or identity boundary"));
                    }
                    pending.extend(
                        value
                            .fields()
                            .iter()
                            .zip(fields)
                            .rev()
                            .map(|(value, ty)| (value, ty, depth + 1)),
                    );
                }
                Kind::Bits(_) | Kind::Q(_) => {
                    return Err(site.error(
                        "unsupported",
                        "ordinary Raw replay supports only Unit, Bit and their exact products",
                    ));
                }
            }
        }
        Ok(result)
    }

    fn bind(
        &mut self,
        value: &SourceValue,
        bits: &[ClassicalId],
        environment: &mut Environment,
        site: Site<'_>,
    ) -> Result<()> {
        let atoms = self.atoms(value, site)?;
        if atoms.len() != bits.len() {
            return Err(site.invalid("Raw values differ from the source value's leaf count"));
        }
        for (source, actual) in atoms.into_iter().zip(bits) {
            if environment.insert(source, *actual).is_some() {
                return Err(site.invalid("source step redefines a local value identity"));
            }
        }
        Ok(())
    }

    fn read(
        &mut self,
        value: &SourceValue,
        environment: &Environment,
        site: Site<'_>,
    ) -> Result<Vec<ClassicalId>> {
        self.atoms(value, site)?
            .into_iter()
            .map(|id| {
                environment
                    .get(&id)
                    .copied()
                    .ok_or_else(|| site.invalid("source step uses an unavailable ordinary value"))
            })
            .collect()
    }

    fn boolean(
        &mut self,
        operation: Boolean,
        inputs: &[Argument<'_>],
        site: Site<'_>,
    ) -> Result<ClassicalId> {
        if inputs
            .iter()
            .any(|input| !matches!(input.ty.kind, Kind::Bit) || input.bits.len() != 1)
        {
            return Err(site.invalid("Boolean source step has a non-Bit operand"));
        }
        let actual = self
            .raw
            .operations
            .get(self.cursor)
            .ok_or_else(|| site.invalid("Raw program omits a Boolean source step"))?;
        // Do not call the emitter here: the checker reads actual opcodes,
        // literals and operands independently, including their exact order.
        let output = match (operation, inputs, actual) {
            (Boolean::Constant(expected), [], RawOp::ClassicalConst { value, output })
                if expected == *value =>
            {
                *output
            }
            (
                Boolean::Not,
                [input],
                RawOp::ClassicalNot {
                    input: actual,
                    output,
                },
            ) if input.bits[0] == *actual => *output,
            (
                Boolean::And,
                [a, b],
                RawOp::ClassicalAnd {
                    left,
                    right,
                    output,
                },
            ) if a.bits[0] == *left && b.bits[0] == *right => *output,
            (
                Boolean::Xor,
                [a, b],
                RawOp::ClassicalXor {
                    left,
                    right,
                    output,
                },
            ) if a.bits[0] == *left && b.bits[0] == *right => *output,
            _ => {
                return Err(
                    site.invalid("Raw Boolean instruction differs from the original source step")
                );
            }
        };
        if !self.issued.insert(output.0) {
            return Err(site.invalid("Raw Boolean output reuses an issued classical identity"));
        }
        self.cursor += 1;
        Ok(output)
    }

    fn function(
        &mut self,
        id: usize,
        arguments: &[Argument<'_>],
        depth: usize,
        call_site: Site<'_>,
    ) -> Result<Vec<ClassicalId>> {
        self.calls += 1;
        if self.calls > MAX_CALLS || depth > MAX_DEPTH {
            return Err(
                call_site.error("limit", "ordinary Raw replay exceeds its call/depth bound")
            );
        }
        let source = self.source;
        let definition = source
            .definitions()
            .get(id)
            .ok_or_else(|| call_site.invalid("source call refers to a missing definition"))?;
        let site = Site::definition(definition);
        let declared = effect(definition.effect(), site)?;
        if !definition.operations().is_empty() {
            return Err(site.error(
                "unsupported",
                "ordinary Raw replay does not support operation providers",
            ));
        }
        if arguments.len() != definition.inputs().len() {
            return Err(call_site.invalid("source call changes whole-argument arity"));
        }
        // A new map is required on every activation, even when a cached source
        // definition is called twice. Its IDs are not global Raw SSA IDs.
        let mut environment = Environment::new();
        for (input, actual) in definition.inputs().iter().zip(arguments) {
            if input.ty() != actual.ty {
                return Err(call_site.invalid("source call changes an argument's exact type tree"));
            }
            self.bind(input, &actual.bits, &mut environment, site)?;
        }
        for step in definition.steps() {
            self.steps += 1;
            let site = Site {
                module: step.module(),
                span: step.span(),
            };
            if self.steps > MAX_STEPS {
                return Err(site.error("limit", "ordinary Raw replay exceeds 10000 source steps"));
            }
            let step_effect = effect(step.effect(), site)?;
            if step_effect > declared {
                return Err(site.invalid("source step exceeds its declaration's effect"));
            }
            let mut inputs = Vec::new();
            for input in step.inputs() {
                inputs.push(Argument {
                    ty: input.ty(),
                    bits: self.read(input, &environment, site)?,
                });
            }
            let output = if let Some(operation) = step.boolean() {
                if step_effect != Effect::Unitary || !matches!(step.output().ty().kind, Kind::Bit) {
                    return Err(site.invalid("Boolean source result or effect differs"));
                }
                vec![self.boolean(operation, &inputs, site)?]
            } else if let Some(child) = step.called_definition() {
                if step
                    .operation_bindings()
                    .is_some_and(|bindings| !bindings.is_empty())
                {
                    return Err(site.error(
                        "unsupported",
                        "ordinary Raw replay does not support operation arguments",
                    ));
                }
                let callee = source
                    .definitions()
                    .get(child)
                    .ok_or_else(|| site.invalid("source call refers to a missing definition"))?;
                if callee.output().ty() != step.output().ty()
                    || effect(callee.effect(), site)? != step_effect
                {
                    return Err(
                        site.invalid("source call changes its result type or declared effect")
                    );
                }
                self.function(child, &inputs, depth + 1, site)?
            } else {
                return Err(site.error(
                    "unsupported",
                    "ordinary Raw replay supports only Boolean steps and ordinary calls",
                ));
            };
            self.bind(step.output(), &output, &mut environment, site)?;
        }
        self.read(definition.output(), &environment, site)
    }
}

pub(super) fn validate(source: &ElaboratedProgram, raw: &RawProgram) -> Result<()> {
    let definition = source
        .definitions()
        .get(source.root())
        .ok_or_else(|| Error::new("preservation", Span::default(), "source root is absent"))?;
    let site = Site::definition(definition);
    if !raw.quantum_inputs.is_empty() || !raw.quantum_outputs.is_empty() {
        return Err(site.invalid("ordinary Raw proposal has a quantum interface"));
    }
    if raw.declared_effect != effect(definition.effect(), site)? {
        return Err(site.invalid("Raw declared effect differs from the source root"));
    }
    if raw.classical_inputs.len() > MAX_CELLS
        || raw.classical_outputs.len() > MAX_CELLS
        || raw.operations.len() > MAX_STEPS
    {
        return Err(site.error("limit", "ordinary Raw proposal exceeds replay bounds"));
    }
    let mut replay = Replay {
        source,
        raw,
        cursor: 0,
        calls: 0,
        steps: 0,
        cells: 0,
        issued: BTreeSet::new(),
    };
    for id in &raw.classical_inputs {
        if !replay.issued.insert(id.0) {
            return Err(site.invalid("Raw classical input identity is repeated"));
        }
    }
    let mut offset = 0;
    let mut arguments = Vec::new();
    for input in definition.inputs() {
        let count = replay.atoms(input, site)?.len();
        let bits = raw
            .classical_inputs
            .get(offset..offset + count)
            .ok_or_else(|| site.invalid("Raw program omits ordinary source inputs"))?;
        arguments.push(Argument {
            ty: input.ty(),
            bits: bits.to_vec(),
        });
        offset += count;
    }
    if offset != raw.classical_inputs.len() {
        return Err(site.invalid("Raw program has extra ordinary inputs"));
    }
    let outputs = replay.function(source.root(), &arguments, 0, site)?;
    if replay.cursor != raw.operations.len() {
        return Err(site.invalid("Raw program contains extra instructions after source replay"));
    }
    if outputs != raw.classical_outputs {
        return Err(site.invalid("Raw outputs differ from the source's ordered ordinary result"));
    }
    Ok(())
}
