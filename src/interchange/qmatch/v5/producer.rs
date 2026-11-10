//! Encode the original lowering and all of its body requests into one fresh QIRF graph.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::{Request, Source};
use crate::interchange::qmatch::{
    self, ArmBody, BodyRequest, Branch, Call, Context, ContextArm, ContextSite, ContextSubject,
    OperationSubject, OriginalBody, ProviderSubject, StaticInterval,
};
use crate::interchange::{self, Encoder, Error, Result, Version};
use crate::ir::RawProgram;
use std::sync::Arc;

struct Builder {
    graph: Encoder,
    remaining: usize,
}

impl Builder {
    fn body(&mut self, original: &OriginalBody, depth: usize) -> Result<BodyRequest> {
        qmatch::charge(&mut self.remaining, 64)?;
        let subject = match original {
            OriginalBody::Function { evidence, .. } => ProviderSubject::Function {
                evidence: self.graph.evidence(evidence)? as u32,
            },
            OriginalBody::Pure { program, .. } => ProviderSubject::Pure {
                program: self.graph.program(program.raw())? as u32,
            },
        };
        Ok(BodyRequest {
            subject,
            body: self.context(original.context(), depth + 1)?,
        })
    }

    fn operation(
        &mut self,
        original: &OperationSubject,
        result: &mut Context,
        depth: usize,
    ) -> Result<()> {
        qmatch::charge(
            &mut self.remaining,
            32 + original.meaning_references.len().saturating_mul(32),
        )?;
        for provider in &original.bodies {
            result.bodies.push(self.body(provider, depth)?);
        }
        let groups = original
            .meaning_references
            .iter()
            .map(|leaves| {
                leaves
                    .iter()
                    .map(|leaf| self.body(leaf, depth))
                    .collect::<Result<_>>()
            })
            .collect::<Result<_>>()?;
        result.references.push(groups);
        Ok(())
    }

    fn context(&mut self, original: &ContextSubject, depth: usize) -> Result<Context> {
        if depth > 128 || original.selections.len() > 128 {
            return Err(Error::limit("qmatch source context capacity"));
        }
        qmatch::positions_storage(original.positions.len(), &mut self.remaining)?;
        StaticInterval::storage(&original.static_intervals, &mut self.remaining)?;
        qmatch::charge(
            &mut self.remaining,
            original.calls.len().saturating_mul(160),
        )?;
        qmatch::charge(
            &mut self.remaining,
            original.branches.len().saturating_mul(192),
        )?;
        let mut result = Context {
            positions: original.positions.clone(),
            static_intervals: original.static_intervals.clone(),
            ..Context::default()
        };
        for (_, actual) in &original.supplies {
            self.operation(actual, &mut result, depth)?;
        }
        if let Some(operation) = &original.operation {
            self.operation(operation, &mut result, depth)?;
        }
        for selection in &original.selections {
            if selection.arms.is_empty() || selection.arms.len() > 64 {
                return Err(Error::limit("qmatch arm capacity"));
            }
            qmatch::interface_storage(&selection.interface, &mut self.remaining)?;
            qmatch::interface_storage(&selection.interface, &mut self.remaining)?;
            qmatch::charge(
                &mut self.remaining,
                selection.arms.len().saturating_mul(128) + 512,
            )?;
            let mut arms = Vec::new();
            for arm in &selection.arms {
                let raw = match &arm.body {
                    ArmBody::Evidence(evidence) => evidence.implementation(),
                    ArmBody::Program(raw) | ArmBody::Physical { raw, .. } => raw,
                };
                let implementation = self.graph.program(raw)? as u32;
                let controlled = self.graph.program(&arm.controlled)? as u32;
                let operation = arm
                    .operation
                    .as_ref()
                    .ok_or_else(|| Error::format("missing original qmatch arm operation"))?;
                self.operation(operation, &mut result, depth)?;
                arms.push(ContextArm {
                    implementation,
                    controlled,
                });
            }
            result.sites.push(ContextSite {
                position: selection.position.clone(),
                attached: selection.interface.clone(),
                required: selection.interface.clone(),
                arms,
            });
        }
        for (position, body) in &original.calls {
            result.calls.push(Call {
                position: position.clone(),
                body: self.context(body, depth + 1)?,
            });
        }
        for (position, then_body, else_body) in &original.branches {
            result.branches.push(Branch {
                position: position.clone(),
                then_body: self.context(then_body, depth + 1)?,
                else_body: self.context(else_body, depth + 1)?,
            });
        }
        Ok(result)
    }
}

pub(crate) fn proposal(
    raw: &RawProgram,
    runtime: Arc<interchange::runtime_root::Request>,
    original: &ContextSubject,
    sources: &[(String, String)],
) -> Result<(Vec<u8>, Request)> {
    let mut graph = Encoder::new(Version::V2);
    for (module, text) in sources {
        graph.source(module, text)?;
    }
    let (root, graph) = interchange::prepare_proposal(raw, None, graph)?;
    let mut builder = Builder {
        graph,
        remaining: interchange::json::MAX_BYTES,
    };
    super::runtime::bounded(&runtime, &mut builder.remaining)?;
    for (formal, actual) in &original.supplies {
        qmatch::charge(&mut builder.remaining, formal.len().saturating_mul(6) + 64)?;
        actual.description.bounded(&mut builder.remaining)?;
    }
    let source = Source {
        module: runtime.module.clone(),
        function: runtime.declaration.clone(),
        arguments: qmatch::StaticArguments {
            bases: runtime.static_bases.clone(),
            naturals: runtime.static_naturals.clone(),
            operations: original
                .supplies
                .iter()
                .map(|(name, actual)| (name.clone(), actual.description.clone()))
                .collect(),
        },
    };
    let context = builder.context(original, 0)?;
    let request = Request {
        source,
        runtime,
        context,
    };
    request.bounded()?;
    Ok((
        interchange::finish_proposal(root, None, builder.graph)?,
        request,
    ))
}
