//! Ordinary finite adapters for already checked language primitive arguments.
//! Original Nat operands are materialized before entering these adapters.
//! Every emitted Raw proposal still requires the common independent checker.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.

use super::*;
use crate::frontend::check::plans::{
    BodyStaticKind, BodyStaticOriginal, ResolvedStaticKind, original_body_static,
};
use crate::frontend::check::primitive::Primitive;
use crate::frontend::resolve::Target;
use crate::frontend::resolve::locals::ResolvedUse;

fn plan_refusal(
    compiler: &Compiler<'_>,
    work: &mut usize,
    module: &str,
    span: Span,
    code: ErrorCode,
    message: &'static str,
) -> Result<CompileError, CompileError> {
    compiler.charge_at(work, module, span, message.len() + 1)?;
    Ok(compiler.error(module, span, code, message))
}

impl Lowerer<'_, '_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn primitive_static_with_source(
        &mut self,
        module: &str,
        source: &Expr,
        supplied_callee: &Ident,
        primitive: Primitive,
        args: Vec<Value>,
        supplied_args: RuntimeArguments<'_>,
    ) -> Result<Value, CompileError> {
        let mut work = self.compiler.work;
        let original = (|| {
            let compiler = &*self.compiler;
            compiler.charge_at(
                &mut work,
                module,
                source.span,
                module.len() + supplied_callee.text.len() + supplied_args.len() + 24,
            )?;
            let same = match (&source.kind, supplied_args) {
                (ExprKind::Call { callee, args, .. }, RuntimeArguments::Values(supplied)) => {
                    std::ptr::eq(callee, supplied_callee) && std::ptr::eq(args.as_slice(), supplied)
                }
                (
                    ExprKind::AccessCall { callee, args, .. },
                    RuntimeArguments::Accesses(supplied),
                ) => {
                    std::ptr::eq(callee, supplied_callee) && std::ptr::eq(args.as_slice(), supplied)
                }
                _ => false,
            };
            if !same {
                return Err(plan_refusal(
                    compiler,
                    &mut work,
                    module,
                    source.span,
                    ErrorCode::TypeMismatch,
                    "primitive callee or runtime argument slice differs from its original call",
                )?);
            }
            let locals = compiler.locals();
            let Some(owner) = locals
                .try_node_id_expr(source)
                .map(|node| node.definition())
            else {
                return Err(plan_refusal(
                    compiler,
                    &mut work,
                    module,
                    source.span,
                    ErrorCode::TypeMismatch,
                    "primitive lacks an original source occurrence",
                )?);
            };
            let Some(module_id) = compiler.source.resolution.module(module) else {
                return Err(plan_refusal(
                    compiler,
                    &mut work,
                    module,
                    source.span,
                    ErrorCode::TypeMismatch,
                    "primitive lacks its original module",
                )?);
            };
            let plan = original_body_static(
                &compiler.source,
                &locals,
                owner,
                module_id,
                BodyStaticOriginal::Expression(source),
                &mut |span, cells| compiler.charge_at(&mut work, module, span, cells),
                &|span, message| compiler.error(module, span, ErrorCode::TypeMismatch, message),
            )?;
            let BodyStaticKind::PrimitiveCall { callee, arguments } = &plan.kind else {
                return Err(plan_refusal(
                    compiler,
                    &mut work,
                    module,
                    source.span,
                    ErrorCode::TypeMismatch,
                    "original body plan is not a primitive call",
                )?);
            };
            if callee.target != ResolvedUse::Global(Target::Primitive(primitive)) {
                return Err(plan_refusal(
                    compiler,
                    &mut work,
                    module,
                    source.span,
                    ErrorCode::TypeMismatch,
                    "primitive target differs from original call",
                )?);
            }
            compiler.charge_at(
                &mut work,
                module,
                source.span,
                arguments.len().saturating_mul(2).saturating_add(2),
            )?;
            Ok((Arc::clone(&plan.environment), arguments.clone()))
        })();
        self.compiler.work = work;
        let (environment, arguments) = original?;
        self.compiler.charge(module, source.span, arguments.len())?;
        let mut naturals = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let value = match &argument.kind {
                ResolvedStaticKind::Natural(value) => {
                    self.compiler.evaluate_plan_natural(value, &environment)?
                }
                ResolvedStaticKind::Name(reference) => {
                    self.compiler
                        .evaluate_plan_reference(reference, argument.span, &environment)?
                }
                _ => {
                    return Err(self.primitive_refusal(
                        module,
                        argument.span,
                        ErrorCode::TypeMismatch,
                        "primitive static operand is not an original Nat",
                    )?);
                }
            };
            naturals.push(value);
        }
        self.primitive_naturals(module, source.span, primitive, &naturals, args)
    }

    pub(super) fn primitive_refusal(
        &mut self,
        module: &str,
        span: Span,
        code: ErrorCode,
        message: &'static str,
    ) -> Result<CompileError, CompileError> {
        self.compiler.charge(module, span, message.len() + 1)?;
        Ok(self.error(module, span, code, message))
    }

    pub(super) fn primitive_naturals(
        &mut self,
        module: &str,
        span: Span,
        primitive: Primitive,
        naturals: &[u32],
        mut args: Vec<Value>,
    ) -> Result<Value, CompileError> {
        self.compiler.charge(
            module,
            span,
            total_size(args.iter().map(|value| value.tree_size().nodes))
                .saturating_mul(8)
                .saturating_add(naturals.len())
                .saturating_add(16),
        )?;
        if naturals.len() != primitive.natural_arity() || args.len() != primitive.runtime_arity() {
            return Err(self.primitive_refusal(
                module,
                span,
                ErrorCode::Arity,
                "primitive argument arity mismatch",
            )?);
        }
        match primitive {
            Primitive::Phase => {
                let [j, k] = naturals else {
                    unreachable!("checked arity")
                };
                let Some(denominator) = 1u32.checked_shl(*k).filter(|_| *k <= 8) else {
                    return Err(self.primitive_refusal(
                        module,
                        span,
                        ErrorCode::Unsupported,
                        "finite Raw phase requires an exact supported dyadic denominator",
                    )?);
                };
                if *j >= denominator {
                    return Err(self.primitive_refusal(
                        module,
                        span,
                        ErrorCode::Contract,
                        "phase numerator must be canonical modulo one",
                    )?);
                }
                if (j * 8) % denominator != 0 {
                    return Err(self.primitive_refusal(module, span, ErrorCode::Unsupported, "finite Raw phase is not an exact multiple of one eighth; no rounding or fallback is permitted")?);
                }
                let exponent = (j * 8 / denominator) as u8;
                self.compiler.charge(module, span, 20)?;
                for value in &args {
                    self.quantum(module, span, value, true)?;
                }
                let value = args.pop().expect("one phase target");
                let slot = self.quantum(module, span, &value, false)?;
                self.apply_circuit(
                    slot,
                    vec![CircuitStep {
                        controls: vec![],
                        action: CircuitAction::Monomial {
                            indices: vec![0],
                            permutation: vec![0, 1],
                            phases: vec![0, exponent],
                        },
                    }],
                );
                Ok(value)
            }

            Primitive::TakeBit | Primitive::PutBit => {
                let [n, k] = naturals else {
                    unreachable!("checked arity")
                };
                if *n > MAX_BITS as u32 || k >= n {
                    return Err(self.primitive_refusal(
                        module,
                        span,
                        ErrorCode::Limit,
                        "register repartition requires k < n <= 12",
                    )?);
                }
                self.compiler
                    .charge(module, span, 20usize.saturating_add(*n as usize * 5))?;
                let position = *k as usize;
                if primitive == Primitive::TakeBit {
                    let value = args.pop().expect("one register");
                    if value.ty() != Ty::quantum(Ty::bits(*n)) {
                        return Err(self.primitive_refusal(
                            module,
                            span,
                            ErrorCode::TypeMismatch,
                            "take_bit requires its exact Bits<n> owner",
                        )?);
                    }
                    let slot = self.quantum(module, span, &value, false)?;
                    let original = self
                        .raw
                        .registers
                        .remove(&slot)
                        .expect("live original register");
                    let prefix = self.token();
                    let tail = self.token();
                    let suffix = self.token();
                    let selected = self.register(Ty::bit(), vec![original.wires[position]]);
                    let mut rest_wires = Vec::with_capacity(*n as usize - 1);
                    rest_wires.extend_from_slice(&original.wires[..position]);
                    rest_wires.extend_from_slice(&original.wires[position + 1..]);
                    let rest = self.register(Ty::bits(n - 1), rest_wires);
                    let bit = self.quantum(module, span, &selected, true)?;
                    let remaining = self.quantum(module, span, &rest, false)?;
                    self.raw.operations.extend([
                        RawOp::Split {
                            input: original.token,
                            left: prefix,
                            right: tail,
                            left_bits: *k as u8,
                        },
                        RawOp::Split {
                            input: tail,
                            left: self.raw.registers[&bit].token,
                            right: suffix,
                            left_bits: 1,
                        },
                        RawOp::Join {
                            left: prefix,
                            right: suffix,
                            output: self.raw.registers[&remaining].token,
                        },
                    ]);
                    Ok(Value::pair(selected, rest))
                } else {
                    if args[0].ty() != Ty::quantum(Ty::bit())
                        || args[1].ty() != Ty::quantum(Ty::bits(n - 1))
                    {
                        return Err(self.primitive_refusal(
                            module,
                            span,
                            ErrorCode::TypeMismatch,
                            "put_bit requires Bit and its exact Bits<n-1> owner",
                        )?);
                    }
                    let bit = self.quantum(module, span, &args[0], true)?;
                    let rest = self.quantum(module, span, &args[1], false)?;
                    if bit == rest {
                        return Err(self.primitive_refusal(
                            module,
                            span,
                            ErrorCode::Ownership,
                            "put_bit operands alias",
                        )?);
                    }
                    let bit = self.raw.registers.remove(&bit).expect("live Bit owner");
                    let rest = self
                        .raw
                        .registers
                        .remove(&rest)
                        .expect("live register owner");
                    let mut wires = Vec::with_capacity(*n as usize);
                    wires.extend_from_slice(&rest.wires[..position]);
                    wires.extend_from_slice(&bit.wires);
                    wires.extend_from_slice(&rest.wires[position..]);
                    let value = self.register(Ty::bits(*n), wires);
                    let slot = self.quantum(module, span, &value, false)?;
                    let prefix = self.token();
                    let suffix = self.token();
                    let head = self.token();
                    self.raw.operations.extend([
                        RawOp::Split {
                            input: rest.token,
                            left: prefix,
                            right: suffix,
                            left_bits: *k as u8,
                        },
                        RawOp::Join {
                            left: prefix,
                            right: bit.token,
                            output: head,
                        },
                        RawOp::Join {
                            left: head,
                            right: suffix,
                            output: self.raw.registers[&slot].token,
                        },
                    ]);
                    Ok(value)
                }
            }
            Primitive::PrependBit => {
                let [n] = naturals else {
                    unreachable!("checked arity")
                };
                let limit = if self.compiler.force_typed_root {
                    8
                } else {
                    MAX_BITS as u32
                };
                if *n >= limit {
                    return Err(self.primitive_refusal(
                        module,
                        span,
                        ErrorCode::Limit,
                        if self.compiler.force_typed_root {
                            "ordinary word exceeds eight bits"
                        } else {
                            "ordinary word exceeds 12 bits"
                        },
                    )?);
                }
                if args[0].ty() != Ty::bit() || args[1].ty() != Ty::bits(*n) {
                    return Err(self.primitive_refusal(
                        module,
                        span,
                        ErrorCode::TypeMismatch,
                        "prepend_bit requires Bit and exact Bits<n>",
                    )?);
                }
                self.compiler
                    .charge(module, span, 6usize.saturating_add(*n as usize * 2))?;
                let tail = args.pop().expect("word argument");
                let Value::Classical(head) = args.pop().expect("Bit argument") else {
                    unreachable!("checked Bit")
                };
                let mut ids = Vec::with_capacity(*n as usize + 1);
                ids.push(head);
                match tail {
                    Value::Bits(tail) => ids.extend(tail),
                    Value::EmptyBits => {}
                    _ => unreachable!("checked word"),
                }
                Ok(Value::bits(ids))
            }
            _ => Err(self.primitive_refusal(
                module,
                span,
                ErrorCode::Unsupported,
                "primitive has no finite Nat adapter",
            )?),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, SourceModule};

    fn project() -> Project {
        let source = "
            unitary fn f(q:Q<Bit>)->Q<Bit>{phase[1,4](q)}";
        Project {
            edition_context: crate::frontend::project::ProjectEdition::Explicit(
                crate::edition::Edition::E2026,
            ),
            root: PathBuf::from("main.qli"),
            modules: BTreeMap::from([(
                "main".into(),
                SourceModule {
                    name: "main".into(),
                    path: PathBuf::from("main.qli"),
                    source: source.into(),
                    ast: crate::frontend::parser::parse_module(source).unwrap(),
                    imports: BTreeMap::new(),
                    origin: ModuleOrigin::Local,
                },
            )]),
        }
    }

    fn lowerer<'c, 'p>(compiler: &'c mut Compiler<'p>) -> Lowerer<'c, 'p> {
        Lowerer {
            nominal_modules: std::rc::Rc::new(std::cell::RefCell::new(BTreeSet::new())),
            compiler,
            raw: RawState::new(),
            operation_sources: BTreeMap::new(),
            instrument_calls: Vec::new(),
            tuple_binding_origins: Vec::new(),
            access_updates: Vec::new(),
            effect: Effect::Unitary,
            contract_effect: Effect::Unitary,
            effect_source: None,
            depth: 0,
            bindings: BTreeMap::new(),
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn static_primitive_refuses_same_span_foreign_callee_and_runtime_slices() {
        let project = project();
        let FnBody::Quantum(body) = &project.modules["main"].ast.decls[0].body else {
            unreachable!()
        };
        let original = &body.result;
        let ExprKind::Call { callee, args, .. } = &original.kind else {
            unreachable!()
        };
        let copied_callee = callee.clone();
        let copied_arguments = args.clone();
        for (supplied_callee, supplied_args) in [
            (&copied_callee, RuntimeArguments::Values(args)),
            (callee, RuntimeArguments::Values(&copied_arguments)),
            (callee, RuntimeArguments::Accesses(&[])),
        ] {
            let mut compiler = super::super::call_state_tests::checked_compiler(&project);
            let owner = compiler.source.resolution.qualified("main::f").unwrap();
            compiler.checking = Some(owner);
            let (kernel, decisions) = compiler.kernel.recording();
            compiler.kernel = kernel;
            let mut lower = lowerer(&mut compiler);
            let wire = lower.wire();
            let value = lower.register(Ty::bit(), vec![wire]);
            let before = lower.compiler.work;
            let failure = lower
                .primitive_static_with_source(
                    "main",
                    original,
                    supplied_callee,
                    Primitive::Phase,
                    vec![value],
                    supplied_args,
                )
                .unwrap_err();
            assert_eq!(failure.code, ErrorCode::TypeMismatch);
            assert_eq!(failure.span, original.span);
            assert!(failure.message.contains("original call"));
            assert!(lower.compiler.work > before);
            assert_eq!(lower.compiler.checking, Some(owner));
            assert!(lower.raw.operations.is_empty());
            assert_eq!(decisions.summary().requests_checked(), 0);
            assert!(lower.compiler.checked.is_empty());
        }
    }

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn unsupported_exact_phase_reserves_rejection_storage_before_allocation() {
        let project = project();
        let span = project.modules["main"].ast.decls[0].span;
        let mut limited = false;
        let mut unsupported = false;
        for allowance in [0, 1, 64, 128, 4096] {
            let mut compiler = super::super::call_state_tests::checked_compiler(&project);
            let owner = compiler.source.resolution.qualified("main::f").unwrap();
            compiler.checking = Some(owner);
            compiler.work = MAX_WORK - allowance;
            let mut lower = lowerer(&mut compiler);
            let wire = lower.wire();
            let value = lower.register(Ty::bit(), vec![wire]);
            let before = lower.compiler.work;
            let failure = lower
                .primitive_naturals("main", span, Primitive::Phase, &[1, 4], vec![value])
                .unwrap_err();
            assert!(lower.compiler.work >= before && lower.compiler.work <= MAX_WORK);
            assert_eq!(lower.compiler.checking, Some(owner));
            assert!(lower.raw.operations.is_empty());
            match failure.code {
                ErrorCode::Limit => limited = true,
                ErrorCode::Unsupported => {
                    assert!(failure.message.contains("no rounding or fallback"));
                    unsupported = true;
                }
                other => panic!("unexpected phase refusal: {other:?}"),
            }
        }
        assert!(limited && unsupported);
    }
}
