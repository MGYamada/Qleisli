//! Non-authoritative execution metadata decoded from a native-accepted body.
//! This maps token coordinates; it does not check liveness, freshness, effects,
//! equations, separability, controls or basis-table injectivity.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{Error, Result};
use crate::ir::*;
use std::collections::BTreeMap;

pub(super) fn metadata(program: &RawProgram) -> Result<(Effect, Vec<QuantumPort>)> {
    let mut coordinates: BTreeMap<TokenId, Vec<WireId>> = program
        .quantum_inputs
        .iter()
        .map(|p| (p.token, p.wires.clone()))
        .collect();
    fn wires(map: &BTreeMap<TokenId, Vec<WireId>>, token: TokenId) -> Result<Vec<WireId>> {
        map.get(&token)
            .cloned()
            .ok_or_else(|| Error::format("native execution view has no token coordinates"))
    }
    fn visit(ops: &[RawOp], map: &mut BTreeMap<TokenId, Vec<WireId>>) -> Result<Effect> {
        let mut effect = Effect::Unitary;
        for op in ops {
            match op {
                RawOp::ApplyUnitary { input, output, .. } | RawOp::Gate { input, output, .. } => {
                    map.insert(*output, wires(map, *input)?);
                }
                RawOp::CertifiedCompute {
                    source, source_out, ..
                } => {
                    map.insert(*source_out, wires(map, *source)?);
                }
                RawOp::Init0 { output, wire } => {
                    map.insert(*output, vec![*wire]);
                    effect = effect.max(Effect::Iso);
                }
                RawOp::Reset {
                    output, fresh_wire, ..
                } => {
                    map.insert(*output, vec![*fresh_wire]);
                    effect = Effect::Observe;
                }
                RawOp::Cnot {
                    control,
                    target,
                    control_out,
                    target_out,
                }
                | RawOp::QuantumIf {
                    control,
                    target,
                    control_out,
                    target_out,
                    ..
                } => {
                    map.insert(*control_out, wires(map, *control)?);
                    map.insert(*target_out, wires(map, *target)?);
                }
                RawOp::Toffoli {
                    control_a,
                    control_b,
                    target,
                    control_a_out,
                    control_b_out,
                    target_out,
                } => {
                    for (input, output) in [
                        (control_a, control_a_out),
                        (control_b, control_b_out),
                        (target, target_out),
                    ] {
                        map.insert(*output, wires(map, *input)?);
                    }
                }
                RawOp::Split {
                    input,
                    left,
                    right,
                    left_bits,
                } => {
                    let source = wires(map, *input)?;
                    let split = usize::from(*left_bits);
                    let left_wires = source
                        .get(..split)
                        .ok_or_else(|| Error::format("native split view exceeds coordinates"))?
                        .to_vec();
                    let right_wires = source
                        .get(split..)
                        .ok_or_else(|| Error::format("native split view exceeds coordinates"))?
                        .to_vec();
                    map.insert(*left, left_wires);
                    map.insert(*right, right_wires);
                }
                RawOp::Join {
                    left,
                    right,
                    output,
                } => {
                    let mut combined = wires(map, *left)?;
                    combined.extend(wires(map, *right)?);
                    map.insert(*output, combined);
                }
                RawOp::LiftBasis {
                    input,
                    output,
                    output_wires,
                    ..
                } => {
                    if wires(map, *input)?.len() != output_wires.len() {
                        effect = effect.max(Effect::Iso);
                    }
                    map.insert(*output, output_wires.clone());
                }
                RawOp::MeasureZ { .. } | RawOp::Discard { .. } => {
                    effect = Effect::Observe;
                }
                RawOp::ClassicalBranch {
                    then_ops,
                    else_ops,
                    quantum_phis,
                    ..
                } => {
                    effect = effect.max(visit(then_ops, map)?).max(visit(else_ops, map)?);
                    for phi in quantum_phis {
                        map.insert(phi.output, phi.output_wires.clone());
                    }
                }
                RawOp::ComputeUseUncompute {
                    source,
                    source_out,
                    targets,
                    ..
                } => {
                    map.insert(*source_out, wires(map, *source)?);
                    for t in targets {
                        map.insert(t.output, wires(map, t.input)?);
                    }
                }
                RawOp::ClassicalConst { .. }
                | RawOp::ClassicalNot { .. }
                | RawOp::ClassicalXor { .. }
                | RawOp::ClassicalAnd { .. } => {}
            }
        }
        Ok(effect)
    }
    let effect = visit(&program.operations, &mut coordinates)?;
    let ports = program
        .quantum_outputs
        .iter()
        .map(|&token| {
            let wires = wires(&coordinates, token)?;
            let bits = u8::try_from(wires.len())
                .map_err(|_| Error::format("native output shape exceeds representation"))?;
            Ok(QuantumPort {
                token,
                wires,
                shape: BasisShape { bits },
            })
        })
        .collect::<Result<Vec<_>>>()?;
    Ok((effect, ports))
}
