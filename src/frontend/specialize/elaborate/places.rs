//! Ordered static place formation and updated-parent reconstruction proposals.
//! No native acceptance or source-preservation theorem is issued here.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::*;

struct Parent {
    identity: usize,
    ty: SourceType,
    value: Option<SourceValue>,
    removed: Vec<(u32, u32)>,
}

impl Builder<'_> {
    fn partition_step(
        &mut self,
        p: PlacePartition,
        values: Vec<SourceValue>,
        frame: &mut Frame,
        span: Span,
    ) -> Result<SourceValue> {
        if p.start > p.end || p.end > p.width || p.width > 16 || (p.bit && p.end - p.start != 1) {
            return Err(error(
                "preservation",
                span,
                "concrete place partition has invalid ordered bounds",
            ));
        }
        let parent = SourceType::quantum(SourceType::bits(p.width));
        let selected = p.selected_type();
        let rest = SourceType::quantum(SourceType::bits(p.width - (p.end - p.start)));
        let (inputs, output) = if p.taking {
            (vec![parent], tuple(vec![selected, rest]))
        } else {
            (vec![selected, rest], parent)
        };
        self.step(
            StepKind::Partition(p),
            inputs,
            output,
            Effect::Unitary,
            values,
            frame,
            span,
            0,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn place_call(
        &mut self,
        name: &Reference,
        arguments: &[Argument],
        inputs: &[Expr],
        accesses: &[crate::frontend::ast::QuantumAccess],
        selections: &[Option<AxisSelection>],
        scope: &mut Scope,
        frame: &mut Frame,
        depth: usize,
        span: Span,
    ) -> Result<SourceValue> {
        if inputs.is_empty()
            || inputs.len() > 64
            || inputs.len() != selections.len()
            || inputs.len() != accesses.len()
        {
            return Err(error(
                "preservation",
                span,
                "place call loses its original ordered arguments",
            ));
        }
        self.charge_cells(inputs.len() * 12, span)?;
        let mut parents: BTreeMap<BinderKey, Parent> = BTreeMap::new();
        let mut identities = BTreeSet::new();
        let mut records = Vec::new();
        let mut values = Vec::new();
        for (input, selection) in inputs.iter().zip(selections) {
            let ExprKind::Name(owner) = &input.kind else {
                return Err(error(
                    "ownership",
                    input.span,
                    "place access requires its original lexical parent",
                ));
            };
            let key = owner
                .local
                .as_ref()
                .ok_or_else(|| error("ownership", input.span, "place parent is unavailable"))?;
            if !parents.contains_key(key) {
                let binding = scope.values.get(key).ok_or_else(|| {
                    error(
                        "ownership",
                        input.span,
                        "place parent is consumed or hidden",
                    )
                })?;
                if !binding.value.ty.is_quantum_owner() || !identities.insert(binding.identity) {
                    return Err(error(
                        "ownership",
                        input.span,
                        "place parents alias or are not quantum owners",
                    ));
                }
                self.charge_cells(
                    key.name.len() + binding.value.cells() + binding.value.ty.cells() + 4,
                    input.span,
                )?;
                let binding = scope.values.remove(key).expect("live parent");
                scope.moved.insert(binding.identity);
                parents.insert(
                    key.clone(),
                    Parent {
                        identity: binding.identity,
                        ty: binding.value.ty.clone(),
                        value: Some(binding.value),
                        removed: Vec::new(),
                    },
                );
            }
            let parent = parents.get_mut(key).expect("retained parent");
            let partition = if let Some(selection) = selection {
                let Some(SourceType {
                    kind: TypeKind::Bits(width),
                }) = parent.ty.quantum_basis()
                else {
                    return Err(error(
                        "type",
                        input.span,
                        "indexed access requires Q<Bits<N>>",
                    ));
                };
                let (start, end, bit) = match selection {
                    AxisSelection::Index(index) => {
                        let i = natural(index, &scope.naturals, &mut self.cells, &mut self.calls)?;
                        (
                            i,
                            i.checked_add(1).ok_or_else(|| {
                                error("limit", input.span, "quantum index successor overflow")
                            })?,
                            true,
                        )
                    }
                    AxisSelection::Range(start, end) => (
                        natural(start, &scope.naturals, &mut self.cells, &mut self.calls)?,
                        natural(end, &scope.naturals, &mut self.cells, &mut self.calls)?,
                        false,
                    ),
                };
                if start > end || end > *width || *width > 16 {
                    return Err(error(
                        "size",
                        input.span,
                        "quantum place is outside its original ordered parent",
                    ));
                }
                self.charge_cells(parent.removed.len() * 4 + 4, input.span)?;
                if start < end
                    && parent
                        .removed
                        .iter()
                        .any(|(a, b)| a < b && start < *b && *a < end)
                {
                    return Err(error(
                        "ownership",
                        input.span,
                        "quantum places overlap their original parent axes",
                    ));
                }
                let removed: u32 = parent.removed.iter().map(|(a, b)| b - a).sum();
                let before: u32 = parent
                    .removed
                    .iter()
                    .map(|(a, b)| start.saturating_sub(*a).min(b - a))
                    .sum();
                let p = PlacePartition {
                    taking: true,
                    width: width - removed,
                    start: start - before,
                    end: start - before + (end - start),
                    bit,
                };
                let value = parent.value.take().ok_or_else(|| {
                    error(
                        "ownership",
                        input.span,
                        "whole-parent access overlaps a place",
                    )
                })?;
                let selected = self.partition_step(p, vec![value], frame, input.span)?;
                let mut fields = selected.fields.into_iter();
                values.push(fields.next().expect("selected owner"));
                parent.value = Some(fields.next().expect("ordered remainder"));
                parent.removed.push((start, end));
                Some(p)
            } else {
                if !parent.removed.is_empty() {
                    return Err(error(
                        "ownership",
                        input.span,
                        "whole-parent access overlaps selected places",
                    ));
                }
                values.push(parent.value.take().ok_or_else(|| {
                    error("ownership", input.span, "whole-parent access is duplicated")
                })?);
                None
            };
            records.push((key.clone(), partition, input.span));
        }
        let first_step = frame.steps.len();
        let result = self.runtime_call(
            RuntimeCall {
                name,
                arguments,
                inputs: RuntimeInputs::Values(values),
                span,
            },
            scope,
            frame,
            depth,
        )?;
        if frame.steps.len() != first_step + 1 {
            return Err(error(
                "preservation",
                span,
                "place call must retain one original callee interval",
            ));
        }
        frame.steps[first_step].accesses = accesses.to_vec();
        frame.steps[first_step].check_access_shape()?;
        let returned = if inputs.len() == 1 {
            vec![result]
        } else {
            result.fields
        };
        if returned.len() != records.len() {
            return Err(error(
                "preservation",
                span,
                "place call loses returned selected owners",
            ));
        }
        // Reverse extraction, using the callee's updated values, never snapshots.
        for ((key, p, origin), updated) in records.into_iter().zip(returned).rev() {
            let parent = parents.get_mut(&key).expect("retained parent");
            parent.value = Some(if let Some(mut p) = p {
                p.taking = false;
                let rest = parent
                    .value
                    .take()
                    .ok_or_else(|| error("ownership", origin, "place remainder is absent"))?;
                self.partition_step(p, vec![updated, rest], frame, origin)?
            } else {
                updated
            });
        }
        for (key, parent) in parents {
            let value = parent
                .value
                .ok_or_else(|| error("ownership", span, "updated parent is absent"))?;
            expected(&value, &parent.ty, span)?;
            scope.moved.remove(&parent.identity);
            scope.values.insert(
                key,
                Binding {
                    identity: parent.identity,
                    value,
                },
            );
        }
        Ok(SourceValue::unit())
    }
}
