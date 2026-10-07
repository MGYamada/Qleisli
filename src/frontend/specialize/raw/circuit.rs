//! Untrusted flattening of a produced pure Raw trace for access transforms.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{Error, MAX_CELLS, MAX_OPERATIONS, Result, Span};
use crate::ir::{BitControl, CircuitAction, CircuitStep, RawOp, SingleGate, TokenId, WireId};
use std::collections::BTreeMap;

fn gate(gate: SingleGate, axis: usize) -> CircuitStep {
    CircuitStep {
        controls: vec![],
        action: match gate {
            SingleGate::H => CircuitAction::Hadamard { target: axis },
            SingleGate::X => CircuitAction::Monomial {
                indices: vec![axis],
                permutation: vec![1, 0],
                phases: vec![0, 0],
            },
            SingleGate::Z | SingleGate::T => CircuitAction::Monomial {
                indices: vec![axis],
                permutation: vec![0, 1],
                phases: vec![0, if gate == SingleGate::Z { 4 } else { 1 }],
            },
        },
    }
}

pub(super) fn remap(step: &mut CircuitStep, axes: &[usize]) {
    for control in &mut step.controls {
        control.index = axes[control.index];
    }
    match &mut step.action {
        CircuitAction::Hadamard { target } => *target = axes[*target],
        CircuitAction::Monomial { indices, .. } | CircuitAction::Contract { indices, .. } => {
            for axis in indices {
                *axis = axes[*axis];
            }
        }
    }
}

pub(super) fn charge(steps: &[CircuitStep], cells: &mut usize, span: Span) -> Result<()> {
    for step in steps {
        let size = 1
            + step.controls.len()
            + match &step.action {
                CircuitAction::Hadamard { .. } => 1,
                CircuitAction::Monomial {
                    indices,
                    permutation,
                    phases,
                } => indices.len() + permutation.len() + phases.len(),
                CircuitAction::Contract { .. } => {
                    return Err(Error::new(
                        "unsupported",
                        span,
                        "source access flattening does not accept opaque contract assertions",
                    ));
                }
            };
        *cells = cells.saturating_add(size);
        if *cells > MAX_CELLS {
            return Err(Error::new(
                "limit",
                span,
                "Raw access circuit exceeds existing value-cell bounds",
            ));
        }
    }
    if steps.len() > MAX_OPERATIONS {
        return Err(Error::new(
            "limit",
            span,
            "Raw access circuit exceeds existing operation bounds",
        ));
    }
    Ok(())
}

/// Input and output wires define logical coordinate order independently of
/// fresh intermediate token IDs. Structural maps become explicit routing.
pub(super) fn flatten(
    operations: &[RawOp],
    input: TokenId,
    input_wires: &[WireId],
    output: TokenId,
    cells: &mut usize,
    span: Span,
) -> Result<Vec<CircuitStep>> {
    let fail = || {
        Error::new(
            "preservation",
            span,
            "produced access trace changes its pure owner interface",
        )
    };
    let indices: BTreeMap<_, _> = input_wires
        .iter()
        .copied()
        .enumerate()
        .map(|(i, w)| (w, i))
        .collect();
    let mut owners = BTreeMap::from([(input, input_wires.to_vec())]);
    let mut steps = Vec::new();
    for operation in operations {
        let before = steps.len();
        match operation {
            RawOp::Gate {
                gate: kind,
                input,
                output,
            } => {
                let wires = owners.remove(input).ok_or_else(fail)?;
                if wires.len() != 1 {
                    return Err(fail());
                }
                steps.push(gate(*kind, *indices.get(&wires[0]).ok_or_else(fail)?));
                owners.insert(*output, wires);
            }
            RawOp::Cnot {
                control,
                target,
                control_out,
                target_out,
            } => {
                let c = owners.remove(control).ok_or_else(fail)?;
                let t = owners.remove(target).ok_or_else(fail)?;
                if c.len() != 1 || t.len() != 1 || c == t {
                    return Err(fail());
                }
                steps.push(CircuitStep {
                    controls: vec![],
                    action: CircuitAction::Monomial {
                        indices: vec![
                            *indices.get(&c[0]).ok_or_else(fail)?,
                            *indices.get(&t[0]).ok_or_else(fail)?,
                        ],
                        permutation: vec![0, 3, 2, 1],
                        phases: vec![0; 4],
                    },
                });
                owners.insert(*control_out, c);
                owners.insert(*target_out, t);
            }
            RawOp::Split {
                input,
                left,
                right,
                left_bits,
            } => {
                let mut wires = owners.remove(input).ok_or_else(fail)?;
                if usize::from(*left_bits) > wires.len() {
                    return Err(fail());
                }
                let right_wires = wires.split_off(usize::from(*left_bits));
                owners.insert(*left, wires);
                owners.insert(*right, right_wires);
            }
            RawOp::Join {
                left,
                right,
                output,
            } => {
                let mut wires = owners.remove(left).ok_or_else(fail)?;
                wires.extend(owners.remove(right).ok_or_else(fail)?);
                owners.insert(*output, wires);
            }
            RawOp::ApplyUnitary {
                input,
                output,
                steps: child,
            } => {
                let wires = owners.remove(input).ok_or_else(fail)?;
                charge(child, cells, span)?;
                if steps.len().saturating_add(child.len()) > MAX_OPERATIONS {
                    return Err(Error::new(
                        "limit",
                        span,
                        "Raw access circuit exceeds existing operation bounds",
                    ));
                }
                let axes: Vec<_> = wires
                    .iter()
                    .map(|w| indices.get(w).copied().ok_or_else(fail))
                    .collect::<Result<_>>()?;
                for child in child {
                    let mut child = child.clone();
                    remap(&mut child, &axes);
                    steps.push(child);
                }
                owners.insert(*output, wires);
            }
            RawOp::ClassicalConst { .. }
            | RawOp::ClassicalNot { .. }
            | RawOp::ClassicalAnd { .. }
            | RawOp::ClassicalXor { .. } => {}
            _ => {
                return Err(Error::new(
                    "unsupported",
                    span,
                    "source operation access requires a pure exact circuit in the current Raw profile",
                ));
            }
        }
        // ApplyUnitary children were charged before cloning their storage.
        if !matches!(operation, RawOp::ApplyUnitary { .. }) {
            charge(&steps[before..], cells, span)?;
        }
        if steps.len() > MAX_OPERATIONS {
            return Err(Error::new(
                "limit",
                span,
                "Raw access circuit exceeds existing operation bounds",
            ));
        }
    }
    let wires = owners.remove(&output).ok_or_else(fail)?;
    if !owners.is_empty() || wires.len() != input_wires.len() {
        return Err(fail());
    }
    let desired: Vec<_> = wires
        .iter()
        .map(|w| indices.get(w).copied().ok_or_else(fail))
        .collect::<Result<_>>()?;
    let mut order: Vec<_> = (0..input_wires.len()).collect();
    for (i, desired_axis) in desired.iter().enumerate() {
        let j = order
            .iter()
            .position(|v| v == desired_axis)
            .ok_or_else(fail)?;
        if i != j {
            let step = CircuitStep {
                controls: vec![],
                action: CircuitAction::Monomial {
                    indices: vec![i, j],
                    permutation: vec![0, 2, 1, 3],
                    phases: vec![0; 4],
                },
            };
            charge(std::slice::from_ref(&step), cells, span)?;
            steps.push(step);
            order.swap(i, j);
        }
    }
    if steps.len() > MAX_OPERATIONS {
        return Err(Error::new(
            "limit",
            span,
            "Raw access circuit exceeds existing operation bounds",
        ));
    }
    Ok(steps)
}

pub(super) fn controlled(mut steps: Vec<CircuitStep>) -> Vec<CircuitStep> {
    for step in &mut steps {
        match &mut step.action {
            CircuitAction::Hadamard { target } => *target += 1,
            CircuitAction::Monomial { indices, .. } | CircuitAction::Contract { indices, .. } => {
                for index in indices {
                    *index += 1;
                }
            }
        }
        for control in &mut step.controls {
            control.index += 1;
        }
        step.controls.push(BitControl {
            index: 0,
            when_one: true,
        });
    }
    steps
}
