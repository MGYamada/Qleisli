//! Static ordered-axis places, checked on original lexical occurrences.
//! These source judgments confer no native acceptance or preservation proof.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::operations::{CallArguments, PreparedArgument};
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
        let Some(selection) = argument.selection() else {
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
        let control = arguments
            .iter()
            .any(|argument| argument.access() == Some(QuantumAccess::Ctrl));
        for argument in arguments {
            if argument.access().is_none() {
                let expression = &argument.value;
                if !matches!(expression.kind, ExprKind::Unit | ExprKind::Name(_)) {
                    return Err(SourceError::new(
                        "unsupported",
                        expression.span,
                        "ordinary access arguments require `()` or a lexical Unit or Bit value",
                    ));
                }
                // Check against the current lexical state. A reference to a
                // parent reserved by any earlier access must remain unavailable.
                let ty = self.expr(expression, scope, None)?;
                let expected = if !control
                    && matches!(ty.kind, Kind::Bit)
                    && matches!(&expression.kind, ExprKind::Name(name) if self.local(name).is_some())
                {
                    Ty::bit()
                } else {
                    Ty::unit()
                };
                normalize::expect(
                    &ty,
                    &expected,
                    &scope.context,
                    expression.span,
                    &self.program.budget,
                )?;
                prepared.push(PreparedArgument {
                    expression,
                    ty,
                    access: None,
                });
                continue;
            }
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
            let binding = scope
                .values
                .get(key)
                .or_else(|| owners.get(key))
                .ok_or_else(|| {
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
                let identity = binding.identity;
                owners.insert(
                    self.program.budget.key(owner.span, key)?,
                    Binding {
                        identity,
                        ty: self.program.budget.copy_ty(owner.span, &binding.ty)?,
                    },
                );
                scope.values.remove(key);
                scope.moved.insert(identity);
            }
            prepared.push(PreparedArgument {
                expression: &argument.value,
                ty,
                access: argument.access(),
            });
        }
        self.require_access_unitary(name, scope, span)?;
        let result = self.call_arguments(
            name,
            static_args,
            CallArguments::Prepared(&prepared),
            scope,
            span,
        )?;
        let mut types = prepared
            .iter()
            .zip(arguments)
            .filter(|(_, original)| original.access().is_some())
            .map(|(argument, _)| self.program.budget.copy_ty(span, &argument.ty))
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
        for (key, binding) in owners {
            scope.moved.remove(&binding.identity);
            scope.values.insert(key, binding);
        }
        if control {
            let ports = expected
                .tuple_fields()
                .unwrap_or_else(|| std::slice::from_ref(&expected));
            self.control_obligation(span, scope, Some(ports))?;
        }
        Ok(Ty::unit())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::parse_module;

    fn check(source: &str) -> Result<()> {
        let syntax = parse_module(source).expect("mixed access source syntax");
        crate::frontend::check::program_with(
            BTreeMap::from([("main", &syntax)]),
            SourceLimits::selected(),
            |_, _, _, _, _, _, _| Ok(()),
        )
        .map(|_| ())
    }

    #[test]
    fn mixed_access_checks_unit_slots_and_restores_only_the_marked_owners() {
        let source = "#![no_implicit_prelude]
            unitary fn step(left: Q<Bit>, marker: Unit, right: Q<Bit>)
              -> (Q<Bit>, Q<Bit>) { (h(left), right) }
            pub unitary fn probe(marker: Unit, q: Q<Bits<2>>) -> Q<Bits<2>> {
                step(excl q[0], marker, excl q[1]); q
            }";
        check(source).unwrap();

        let overlap = source.replace("excl q[1]", "excl q[0]");
        let error = check(&overlap).unwrap_err();
        assert_eq!(error.code, "ownership");
        assert!(error.message.contains("overlap"));
    }

    #[test]
    fn mixed_exclusive_access_checks_lexical_bit_slots_in_source_order() {
        let source = "#![no_implicit_prelude]
            unitary fn turn(tag: Unit, flag: Bit, data: Q<Bit>, spare: Bit)
              -> Q<Bit> { if flag { h(data) } else { data } }
            pub unitary fn probe(tag: Unit, flag: Bit, spare: Bit, q: Q<Bits<2>>) -> Q<Bits<2>> {
                turn(tag, flag, excl q[1], spare); q
            }";
        check(source).unwrap();

        let wrong_slot = source.replace("turn(tag, flag, excl", "turn(flag, tag, excl");
        let error = check(&wrong_slot).unwrap_err();
        assert_eq!(error.code, "type");
        assert_eq!(&wrong_slot[error.span.start..error.span.end], "flag");

        let control = source.replace("excl q[1]", "ctrl q[1]");
        let error = check(&control).unwrap_err();
        assert_eq!(error.code, "type");
        assert_eq!(&control[error.span.start..error.span.end], "flag");

        let literal = source.replace("turn(tag, flag, excl", "turn(tag, 1, excl");
        let error = check(&literal).unwrap_err();
        assert_eq!(error.code, "unsupported");
        assert_eq!(&literal[error.span.start..error.span.end], "1");
    }

    #[test]
    fn declared_access_returns_the_original_quantum_owners_at_scope_exit() {
        let source = "#![no_implicit_prelude]
            unitary fn turn(tag: Unit, target: excl Q<Bit>) -> Unit { h(excl target); }
            unitary fn idle[const N: Nat](target: excl Q<Bits<N>>) -> Unit { () }
            unitary fn phase_target(target: ctrl Q<Bit>) -> Unit { phase[1,1](ctrl target); }
            pub unitary fn probe(q: Q<Bits<2>>) -> Q<Bits<2>> {
                turn((), excl q[0]); phase_target(ctrl q[1]); idle[2](excl q); q
            }";
        check(source).unwrap();

        let wrong_role = source.replace("turn((), excl q[0])", "turn((), ctrl q[0])");
        let error = check(&wrong_role).unwrap_err();
        assert_eq!(error.code, "ownership");
        assert!(error.message.contains("explicit excl owner"));

        let by_value = source.replace("idle[2](excl q)", "idle[2](q)");
        let error = check(&by_value).unwrap_err();
        assert_eq!(error.code, "ownership");
        assert!(error.message.contains("explicit excl owner"));

        let consumed = source.replace("h(excl target);", "discard(target);");
        let error = check(&consumed).unwrap_err();
        assert_eq!(error.code, "ownership");
        assert!(error.message.contains("return the original owner `target`"));

        let wider_result = source.replace(
            "excl Q<Bit>) -> Unit { h(excl target); }",
            "excl Q<Bit>) -> Q<Bit> { h(target) }",
        );
        let error = check(&wider_result).unwrap_err();
        assert_eq!(error.code, "type");
        assert!(error.message.contains("expected `Unit`"));
    }

    #[test]
    fn declared_access_does_not_mask_an_observing_body() {
        let source = "#![no_implicit_prelude]
            pub unitary fn bad(target: excl Q<Bit>) -> Unit {
                let measured = measure_z(basis unit(()) as _ { 0 });
                h(excl target);
            }";
        let error = check(source).unwrap_err();
        assert_eq!(error.code, "effect");
    }

    #[test]
    fn mixed_access_ordinary_slots_cannot_use_suspended_or_consumed_owners() {
        let source = "#![no_implicit_prelude]
            unitary fn step(before: Unit, q: Q<Bit>, after: Unit)
              -> Q<Bit> { h(q) }
            pub unitary fn probe(q: Q<Bit>) -> Q<Bit> {
                step((), excl q, ()); q
            }";
        check(source).unwrap();

        let suspended = source.replace("excl q, ()", "excl q, q");
        let error = check(&suspended).unwrap_err();
        assert_eq!(error.code, "ownership");
        assert_eq!(&suspended[error.span.start..error.span.end], "q");

        let consuming = source.replace("excl q, ()", "excl q, discard(q)");
        let error = check(&consuming).unwrap_err();
        assert_eq!(error.code, "unsupported");
        assert_eq!(&consuming[error.span.start..error.span.end], "discard(q)");
    }
}
