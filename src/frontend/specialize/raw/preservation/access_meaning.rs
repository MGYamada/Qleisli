//! Fresh exact equations for actual transformed substeps and source boundaries.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
use super::{MAX_CELLS, Result, Site, access::Interval};
use crate::contract::{
    BasisType,
    exact::{Budget, Exact, MAX_MATRIX_DIMENSION, Matrix},
};
use crate::interchange::{RootInterface, Version, finite_leaf, native};
use crate::ir::{
    BasisShape, BitControl, CircuitAction, CircuitStep, Effect, QuantumPort, RawOp, RawProgram,
    TokenId, WireId,
};
use std::collections::{BTreeMap, BTreeSet};

fn charge(cells: &mut usize, amount: usize, site: Site<'_>) -> Result<()> {
    *cells = cells.saturating_add(amount);
    if *cells > MAX_CELLS {
        return Err(site.error(
            "limit",
            "source Meaning access exceeds existing value-cell bounds",
        ));
    }
    Ok(())
}

pub(super) fn check(
    kernel: &native::Kernel,
    meanings: &[super::super::CheckedMeaning],
    intervals: &[Interval],
    actual: &[CircuitStep],
    budget: &mut Budget,
    cells: &mut usize,
    site: Site<'_>,
) -> Result<()> {
    for interval in intervals {
        let leaf = &meanings
            .get(interval.leaf)
            .ok_or_else(|| site.invalid("access interval loses its original Meaning"))?
            .1;
        let input: Vec<_> = interval
            .controls
            .iter()
            .chain(&interval.input)
            .copied()
            .collect();
        let output: Vec<_> = interval
            .controls
            .iter()
            .chain(&interval.output)
            .copied()
            .collect();
        if input.len() > MAX_MATRIX_DIMENSION.ilog2() as usize {
            return Err(site.error(
                "limit",
                "transformed Meaning exceeds the existing six-bit finite profile",
            ));
        }
        charge(cells, 1 + input.len() + output.len(), site)?;
        let axes: BTreeMap<_, _> = input
            .iter()
            .copied()
            .enumerate()
            .map(|(i, axis)| (axis, i))
            .collect();
        if axes.len() != input.len()
            || input.len() != output.len()
            || input.iter().copied().collect::<BTreeSet<_>>() != output.iter().copied().collect()
            || leaf
                .boundary()
                .signature()
                .bits()
                .map_err(|e| site.invalid(e.to_string()))?
                != interval.input.len()
        {
            return Err(
                site.invalid("transformed Meaning changes or aliases its exact axis boundary")
            );
        }
        let selected = actual
            .get(interval.first..interval.end)
            .ok_or_else(|| site.invalid("Meaning substep interval is outside the actual action"))?;
        let mut steps = Vec::with_capacity(selected.len() + input.len());
        let map = |axis: &mut usize| -> Result<()> {
            *axis = *axes
                .get(axis)
                .ok_or_else(|| site.invalid("actual Meaning substep touches a suspended axis"))?;
            Ok(())
        };
        for original in selected {
            let size = 1
                + original.controls.len()
                + match &original.action {
                    CircuitAction::Hadamard { .. } => 1,
                    CircuitAction::Monomial {
                        indices,
                        permutation,
                        phases,
                    } => indices.len() + permutation.len() + phases.len(),
                    CircuitAction::Contract { .. } => {
                        return Err(
                            site.invalid("transformed Meaning cannot acquire opaque evidence")
                        );
                    }
                };
            charge(cells, size, site)?;
            let mut step = original.clone();
            for control in &mut step.controls {
                map(&mut control.index)?;
            }
            match &mut step.action {
                CircuitAction::Hadamard { target } => map(target)?,
                CircuitAction::Monomial { indices, .. } => {
                    for axis in indices {
                        map(axis)?;
                    }
                }
                CircuitAction::Contract { .. } => unreachable!("rejected above"),
            }
            steps.push(step);
        }
        // Translate the independently retained output coordinate order to a
        // canonical native boundary. These explicit swaps are coordinate
        // reconstruction, not omitted/replaced steps of the actual interval.
        // A surrounding coherent control also controls this coordinate map;
        // the inactive sector retains its original input order.
        let mut arrangement = input.clone();
        for position in 0..output.len() {
            if arrangement[position] != output[position] {
                let other = arrangement
                    .iter()
                    .position(|axis| *axis == output[position])
                    .ok_or_else(|| site.invalid("Meaning output loses an axis"))?;
                charge(cells, 11 + interval.controls.len(), site)?;
                if steps.len() >= super::MAX_STEPS {
                    return Err(site.error(
                        "limit",
                        "Meaning coordinate reconstruction exceeds existing step bounds",
                    ));
                }
                steps.push(CircuitStep {
                    controls: (0..interval.controls.len())
                        .map(|index| BitControl {
                            index,
                            when_one: true,
                        })
                        .collect(),
                    action: CircuitAction::Monomial {
                        indices: vec![position, other],
                        permutation: vec![0, 2, 1, 3],
                        phases: vec![0; 4],
                    },
                });
                arrangement.swap(position, other);
            }
        }
        let meaning = if interval.adjoint {
            leaf.meaning()
                .adjoint(budget)
                .map_err(|e| site.error("limit", e.to_string()))?
        } else {
            leaf.meaning().clone()
        };
        let mut signature = leaf.boundary().signature().clone();
        for _ in &interval.controls {
            signature = BasisType::Pair(Box::new(BasisType::Bit), Box::new(signature));
        }
        let controls = interval.controls.len();
        let dim = 1usize << input.len();
        budget
            .charge(dim * dim)
            .map_err(|e| site.error("limit", e.to_string()))?;
        charge(cells, dim * dim, site)?;
        let mask = (1usize << controls) - 1;
        let mut entries = vec![Exact::zero(); dim * dim];
        for row in 0..dim {
            for column in 0..dim {
                entries[row * dim + column] = if row & mask == mask && column & mask == mask {
                    meaning
                        .get(row >> controls, column >> controls)
                        .ok_or_else(|| site.invalid("original Meaning has a different dimension"))?
                } else if row == column {
                    Exact::one()
                } else {
                    Exact::zero()
                };
            }
        }
        let required = Matrix::new(dim, dim, entries).map_err(|e| site.invalid(e.to_string()))?;
        let wires = (0..input.len())
            .map(|i| WireId(i as u32))
            .collect::<Vec<_>>();
        let port = |token| QuantumPort {
            token: TokenId(token),
            wires: wires.clone(),
            shape: BasisShape {
                bits: input.len() as u8,
            },
        };
        let raw = RawProgram {
            quantum_inputs: vec![port(0)],
            classical_inputs: vec![],
            operations: vec![RawOp::ApplyUnitary {
                input: TokenId(0),
                output: TokenId(1),
                steps,
            }],
            quantum_outputs: vec![TokenId(1)],
            classical_outputs: vec![],
            declared_effect: Effect::Unitary,
        };
        let interface = RootInterface {
            input: signature.clone(),
            output: signature.clone(),
        };
        let proposal = native::Proposal::from_raw(&raw, Some(&interface), Version::V2, None)
            .map_err(|e| site.invalid(e.to_string()))?;
        budget
            .charge(proposal.artifact().len())
            .map_err(|e| site.error("limit", e.to_string()))?;
        let boundary = finite_leaf::UnitaryBoundary::new(signature, port(0), port(1))
            .map_err(|e| site.invalid(e.to_string()))?;
        finite_leaf::check_with_kernel(kernel, proposal.artifact(), &boundary, &required, budget)
            .map_err(|e| {
            site.error(
                e.code,
                format!("actual transformed Raw substeps violate original Meaning: {e}"),
            )
        })?;
    }
    Ok(())
}
