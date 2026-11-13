//! Concrete project access proposals over original ordered owner places.
//! Native checking still governs the emitted IR and each concrete Ctrl call.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::frontend::resolve::locals::BinderKey;
use std::{collections::btree_map::Entry, ops::Range};

struct Parent {
    original: Ty,
    remainder: Option<Value>,
    removed: Vec<Range<usize>>,
}

struct Access {
    parent: BinderKey,
    span: Span,
    position: Option<usize>,
}

pub(super) struct Places {
    parents: BTreeMap<BinderKey, Parent>,
    accesses: Vec<Access>,
}

impl Lowerer<'_, '_> {
    pub(super) fn prepare_places(
        &mut self,
        module: &str,
        arguments: &[AccessArgument],
        env: &mut Env,
    ) -> Result<(Vec<Value>, Places), CompileError> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut places = Places {
            parents: BTreeMap::new(),
            accesses: Vec::with_capacity(arguments.len()),
        };
        let mut slots = BTreeSet::new();
        for argument in arguments {
            let span = argument.value.span;
            let ExprKind::Name(name) = &argument.value.kind else {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "quantum access requires its original lexical owner",
                ));
            };
            let key = self
                .compiler
                .locals()
                .local_key(name)
                .cloned()
                .ok_or_else(|| {
                    self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "quantum access owner is unavailable",
                    )
                })?;
            self.compiler
                .charge(module, span, key.name.len().saturating_mul(3) + 8)?;
            if let Entry::Vacant(entry) = places.parents.entry(key.clone()) {
                let value = self.expr(module, &argument.value, env)?;
                let slot = self.quantum(module, span, &value, false)?;
                if !slots.insert(slot) {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "quantum access parents alias",
                    ));
                }
                entry.insert(Parent {
                    original: value.ty(),
                    remainder: Some(value),
                    removed: Vec::new(),
                });
            } else {
                self.compiler.tick(module, span)?;
            }
            let parent = places
                .parents
                .get_mut(&key)
                .expect("retained original parent");
            let remainder = parent.remainder.take().ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "quantum access overlaps a whole owner",
                )
            })?;
            let (value, position) = if let Some(selection) = &argument.selection {
                self.extract_place(module, span, selection, parent, remainder)?
            } else {
                if !parent.removed.is_empty() {
                    return Err(self.error(
                        module,
                        span,
                        ErrorCode::Ownership,
                        "whole owner access overlaps selected places",
                    ));
                }
                (remainder, None)
            };
            values.push(value);
            places.accesses.push(Access {
                parent: key,
                span,
                position,
            });
        }
        Ok((values, places))
    }

    fn extract_place(
        &mut self,
        module: &str,
        span: Span,
        selection: &AxisSelection,
        parent: &mut Parent,
        remainder: Value,
    ) -> Result<(Value, Option<usize>), CompileError> {
        let Some(Ty {
            kind: Kind::Bits(width),
        }) = parent.original.quantum_basis()
        else {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "indexed quantum access requires an exact Bits owner",
            ));
        };
        let (start, end, bit) = match selection {
            AxisSelection::Index(index) => {
                let start = self.static_natural_value(module, index)?;
                let end = start.checked_add(1).ok_or_else(|| {
                    self.error(
                        module,
                        index.span,
                        ErrorCode::Limit,
                        "quantum index successor overflow",
                    )
                })?;
                (start, end, true)
            }
            AxisSelection::Range { start, end } => (
                self.static_natural_value(module, start)?,
                self.static_natural_value(module, end)?,
                false,
            ),
        };
        if start > end || end > *width {
            return Err(self.error(
                module,
                span,
                ErrorCode::TypeMismatch,
                "quantum place is outside its original ordered owner",
            ));
        }
        let range = start as usize..end as usize;
        self.compiler.charge(
            module,
            span,
            20 + *width as usize * 5 + parent.removed.len() * 4,
        )?;
        if !range.is_empty()
            && parent.removed.iter().any(|prior| {
                !prior.is_empty() && range.start < prior.end && prior.start < range.end
            })
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::Ownership,
                "quantum access places overlap",
            ));
        }
        // Original coordinates stay stable while earlier disjoint selections
        // are absent. Empty slices may sit inside an earlier selection.
        let before: usize = parent
            .removed
            .iter()
            .map(|prior| range.start.saturating_sub(prior.start).min(prior.len()))
            .sum();
        let position = range.start - before;
        let selected_basis = if bit {
            Ty::bit()
        } else {
            Ty::bits(end - start)
        };
        let remainder_slot = self.quantum(module, span, &remainder, false)?;
        let remaining_width = self.raw.registers[&remainder_slot].wires.len();
        let remainder_width = remaining_width
            .checked_sub(range.len())
            .filter(|width| position <= *width)
            .ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Ownership,
                    "quantum place differs from its remaining ordered owner",
                )
            })?;
        let remainder_basis = Ty::bits(remainder_width as u32);
        let (selected, remaining) = self.raw.take_range(
            remainder_slot,
            position..position + range.len(),
            selected_basis.clone(),
            remainder_basis.clone(),
        );
        parent.remainder = Some(Value::quantum(remaining, remainder_basis));
        parent.removed.push(range);
        Ok((Value::quantum(selected, selected_basis), Some(position)))
    }

    pub(super) fn restore_places(
        &mut self,
        module: &str,
        mut places: Places,
        returned: Vec<Value>,
        env: &mut Env,
    ) -> Result<(), CompileError> {
        for (access, returned) in places.accesses.into_iter().zip(returned).rev() {
            let parent = places
                .parents
                .get_mut(&access.parent)
                .expect("retained original parent");
            let value = if let Some(position) = access.position {
                let remainder = parent.remainder.take().expect("retained remainder");
                let selected = self.quantum(module, access.span, &returned, false)?;
                let remainder = self.quantum(module, access.span, &remainder, false)?;
                let remainder_width = self.raw.registers[&remainder].wires.len();
                if selected == remainder || position > remainder_width {
                    return Err(self.error(
                        module,
                        access.span,
                        ErrorCode::Ownership,
                        "returned quantum place cannot be reinserted into its owner",
                    ));
                }
                let width = self.raw.registers[&selected].wires.len() + remainder_width;
                self.compiler.charge(module, access.span, 20 + width * 5)?;
                let basis = Ty::bits(width as u32);
                let updated = self
                    .raw
                    .put_range(selected, remainder, position, basis.clone());
                Value::quantum(updated, basis)
            } else {
                returned
            };
            parent.remainder = Some(value);
        }
        for (key, parent) in places.parents {
            let value = parent.remainder.expect("restored original parent");
            debug_assert_eq!(value.ty(), parent.original);
            self.access_updates
                .last_mut()
                .expect("access call inside a block")
                .insert(key.clone());
            env.insert(key, Binding::Live(value));
        }
        Ok(())
    }
}
