//! Static ordered-axis places, checked on original lexical occurrences.
//! These source judgments confer no native acceptance or preservation proof.
// Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
use super::operations::{CallArguments, PreparedAccess};
use super::*;

enum Footprint {
    Whole,
    Interval { start: Linear, end: Linear },
}

impl Checker<'_, '_> {
    fn place_le(&self, a: &Linear, b: &Linear, scope: &Scope, span: Span) -> Result<bool> {
        Ok(scope.context.proves_le_budgeted(
            a,
            b,
            span,
            "while checking static quantum place bounds or disjointness",
            &mut |span, cells| self.program.budget.preparation_charge(span, cells),
        )?)
    }

    fn selected_place(
        &self,
        argument: &AccessArgument,
        binding: &Binding,
        scope: &Scope,
    ) -> Result<(Ty, Footprint)> {
        let span = argument.value.span;
        let Some(selection) = &argument.selection else {
            if !binding.ty.is_quantum_owner() {
                return Err(SourceError::new(
                    "type",
                    span,
                    "quantum access requires one Q<A> owner",
                ));
            }
            return Ok((
                self.program.budget.copy_ty(span, &binding.ty)?,
                Footprint::Whole,
            ));
        };
        let Some(Ty {
            kind: Kind::Bits(width),
        }) = binding.ty.quantum_basis()
        else {
            return Err(SourceError::new(
                "type",
                span,
                "indexed quantum access requires a Q<Bits<N>> owner",
            ));
        };
        let (start, end, bit) = match selection {
            AxisSelection::Index(index) => {
                let start =
                    normalize::natural(index, self.index(), scope, None, &self.program.budget)?;
                let end = crate::frontend::linear::at(
                    start.add_budgeted(&Linear::constant(1), span, &mut |span, cells| {
                        self.program.budget.preparation_charge(span, cells)
                    }),
                    span,
                    "while forming the exclusive end of a quantum axis",
                )?;
                (start, end, true)
            }
            AxisSelection::Range { start, end } => (
                normalize::natural(start, self.index(), scope, None, &self.program.budget)?,
                normalize::natural(end, self.index(), scope, None, &self.program.budget)?,
                false,
            ),
        };
        if !self.place_le(&Linear::constant(0), &start, scope, span)?
            || !self.place_le(&start, &end, scope, span)?
            || !self.place_le(&end, width, scope, span)?
        {
            return Err(SourceError::new(
                "size",
                span,
                "quantum place requires compile-time proof of 0 <= start <= end <= N; an index additionally requires index < N",
            ));
        }
        let basis = if bit {
            Ty::bit()
        } else {
            Ty::bits(crate::frontend::linear::at(
                end.sub_budgeted(&start, span, &mut |span, cells| {
                    self.program.budget.preparation_charge(span, cells)
                }),
                span,
                "while forming a quantum slice width",
            )?)
        };
        Ok((Ty::quantum(basis), Footprint::Interval { start, end }))
    }

    fn disjoint_places(
        &self,
        a: &Footprint,
        b: &Footprint,
        scope: &Scope,
        span: Span,
    ) -> Result<bool> {
        let (Footprint::Interval { start: a, end: b }, Footprint::Interval { start: c, end: d }) =
            (a, b)
        else {
            // Whole-owner access suspends that owner, including zero-width
            // owners. An empty footprint is not permission to duplicate it.
            return Ok(false);
        };
        Ok(self.place_le(b, c, scope, span)?
            || self.place_le(d, a, scope, span)?
            || self.place_le(b, a, scope, span)?
            || self.place_le(d, c, scope, span)?)
    }

    pub(super) fn indexed_access_call(
        &mut self,
        name: &Ident,
        static_args: &[StaticOp],
        arguments: &[AccessArgument],
        scope: &mut Scope,
        span: Span,
    ) -> Result<Ty> {
        self.program
            .budget
            .charge(span, arguments.len().saturating_mul(6))?;
        if arguments.is_empty() || arguments.len() > 64 {
            return Err(SourceError::new(
                "arity",
                span,
                "quantum access calls require one to 64 arguments",
            ));
        }
        let mut owners = BTreeMap::new();
        let mut footprints: BTreeMap<usize, Vec<Footprint>> = BTreeMap::new();
        let mut prepared = Vec::new();
        for argument in arguments {
            let ExprKind::Name(owner) = &argument.value.kind else {
                return Err(SourceError::new(
                    "ownership",
                    argument.value.span,
                    "quantum places require a lexical owner",
                ));
            };
            let key = self.local(owner).ok_or_else(|| {
                SourceError::new(
                    "ownership",
                    owner.span,
                    "quantum place requires a live lexical owner",
                )
            })?;
            let binding = scope.values.get(key).ok_or_else(|| {
                SourceError::new(
                    "ownership",
                    owner.span,
                    "quantum place cannot access a consumed or hidden owner",
                )
            })?;
            let (ty, footprint) = self.selected_place(argument, binding, scope)?;
            let previous = footprints.entry(binding.identity).or_default();
            for other in previous.iter() {
                self.program.budget.charge(argument.value.span, 1)?;
                if !self.disjoint_places(other, &footprint, scope, argument.value.span)? {
                    return Err(SourceError::new(
                        "ownership",
                        argument.value.span,
                        "quantum access places overlap or lack compile-time proof of disjointness; distinct argument names do not establish separate axes",
                    ));
                }
            }
            previous.push(footprint);
            if !owners.contains_key(key) {
                owners.insert(
                    self.program.budget.key(owner.span, key)?,
                    Binding {
                        identity: binding.identity,
                        ty: self.program.budget.copy_ty(owner.span, &binding.ty)?,
                    },
                );
            }
            prepared.push(PreparedAccess {
                expression: &argument.value,
                ty,
            });
        }
        self.require_access_unitary(name, scope, span)?;
        // Suspend each parent exactly once for the joint call. Types below
        // describe selected interfaces; they do not move/copy the parent again.
        for (key, binding) in &owners {
            scope.values.remove(key);
            scope.moved.insert(binding.identity);
        }
        let result = self.call_arguments(
            name,
            static_args,
            CallArguments::Places(&prepared),
            scope,
            span,
        )?;
        let mut types = prepared
            .iter()
            .map(|argument| self.program.budget.copy_ty(span, &argument.ty))
            .collect::<Result<Vec<_>>>()?;
        let expected = if types.len() == 1 {
            types.pop().expect("one selected owner")
        } else {
            Ty::tuple(types)
        };
        normalize::expect(
            &result,
            &expected,
            &scope.context,
            span,
            &self.program.budget,
        )
        .map_err(|mut error| {
            error.message = format!(
                "access call must return the same exact ordered selected interface: {}",
                error.message
            );
            error
        })?;
        if arguments
            .iter()
            .any(|argument| argument.access == QuantumAccess::Ctrl)
        {
            self.obligation(span, ObligationKind::ControlSectors)?;
        }
        for (key, binding) in owners {
            scope.moved.remove(&binding.identity);
            scope.values.insert(key, binding);
        }
        Ok(Ty::unit())
    }
}
