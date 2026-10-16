//! Two-port providers keep their original checked bodies through lowering.
use super::*;

impl Compiler<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn pure_provider_program(
        &mut self,
        module: &str,
        span: Span,
        key: Key,
        meaning: Option<Key>,
        basis: Ty,
        codomain: Ty,
        effect: Effect,
        body: &AcceptedProgram,
        bindings: &Bindings,
    ) -> Result<Operation, CompileError> {
        let expected = meaning.map(|key| &self.meanings[&key].matrix);
        let evidence = crate::frontend::pure::check(
            &self.kernel,
            body.raw(),
            &contract_basis(&basis),
            &contract_basis(&codomain),
            expected,
            &mut self.exact_work,
        )
        .map_err(|e| self.op_error(module, span, e))?;
        let evidence = Arc::new(evidence);
        let specification = match meaning {
            Some(id) => self.meanings[&id].pure.clone().ok_or_else(|| {
                self.error(
                    module,
                    span,
                    ErrorCode::Contract,
                    "rectangular Meaning lacks its original native equation",
                )
            })?,
            None => evidence.clone(),
        };
        let names = (
            self.source.resolution.path(key),
            meaning.map_or_else(
                || self.source.resolution.path(key),
                |id| self.source.resolution.path(id),
            ),
        );
        let roots: Vec<_> = [Some(key), meaning].into_iter().flatten().collect();
        let sources = self.retained_sources(module, span, &roots, bindings, &[body.raw()])?;
        let equation = crate::interchange::pure_leaf::SourcePureEquation::bind(
            evidence.clone(),
            specification,
            names,
            Arc::clone(&sources),
        )
        .map_err(|e| self.error(module, span, ErrorCode::Contract, e.to_string()))?;
        let equation = Arc::new(equation);
        let origin = Arc::new(PureOrigin {
            definition: key,
            table: Arc::clone(&self.source.lexical[&key]),
            meaning,
            equation: Arc::clone(&equation),
        });
        self.pure_equations.push(equation);
        let inverse = if effect == Effect::Unitary {
            let raw = evidence.program().raw().clone();
            Some(Arc::new(
                FunctionEvidence::check_retained_with_kernel(
                    &self.kernel,
                    contract_basis(&basis),
                    raw.clone(),
                    raw,
                    RetainedIdentity::interned(
                        self.source.resolution.path(key),
                        self.source.resolution.path(key),
                        sources,
                    ),
                    &mut self.exact_work,
                )
                .map_err(|e| self.op_error(module, span, e.error))?,
            ))
        } else {
            None
        };
        let access = [
            true,
            inverse.is_some(),
            inverse.is_some() && basis == codomain,
        ];
        let operation = Operation {
            basis,
            codomain,
            access,
            effect,
            meaning: Some(evidence.meaning().clone()),
            node: Arc::new(Node::Pure(PureProvider {
                origin: Some(origin),
                leaf: evidence,
                inverse,
            })),
            nodes: 1,
            depth: 1,
        };
        self.charge(module, span, operation.copy_size())?;
        Ok(operation)
    }
}

impl Operation {
    pub(in crate::frontend::compile) fn needs_raw(&self) -> bool {
        if self.basis != self.codomain {
            return true;
        }
        match self.node.as_ref() {
            Node::Pure(_) => true,
            Node::Then(a, b) | Node::Tensor(a, b) | Node::Conjugate(a, b) => {
                a.needs_raw() || b.needs_raw()
            }
            Node::Inverse(a) | Node::Controlled(a) | Node::Repeat(_, a) | Node::Requested(_, a) => {
                a.needs_raw()
            }
            Node::Provider(_) => false,
        }
    }
    pub(in crate::frontend::compile) fn raw(
        &self,
        module: &str,
        span: Span,
        access: Access,
        compiler: &mut Compiler<'_>,
    ) -> Result<crate::interchange::pure_leaf::CheckedPureLeaf, CompileError> {
        self.require(module, span, access, compiler)?;
        if let Node::Requested(_, operation) = self.node.as_ref() {
            return operation.raw(module, span, access, compiler);
        }
        let (basis, codomain) = match access {
            Access::Apply => (self.basis.clone(), self.codomain.clone()),
            Access::Adjoint => (self.codomain.clone(), self.basis.clone()),
            Access::Controlled => (
                Ty::pair(Ty::bit(), self.basis.clone()),
                Ty::pair(Ty::bit(), self.codomain.clone()),
            ),
        };
        let expected = self.meaning.as_ref().expect("concrete provider meaning");
        let expected = match access {
            Access::Apply => expected.clone(),
            Access::Adjoint => expected
                .adjoint(&mut compiler.exact_work)
                .map_err(|e| compiler.op_error(module, span, e.into()))?,
            Access::Controlled => control_matrix(expected, &mut compiler.exact_work)
                .map_err(|e| compiler.op_error(module, span, e))?,
        };
        let raw = match (self.node.as_ref(), access) {
            (Node::Pure(provider), Access::Apply) => provider.leaf.program().raw().clone(),
            (Node::Then(a, b) | Node::Tensor(a, b), Access::Apply) if self.needs_raw() => {
                let a = a.raw(module, span, access, compiler)?;
                let b = b.raw(module, span, access, compiler)?;
                crate::frontend::pure::combine(
                    &a,
                    &b,
                    matches!(self.node.as_ref(), Node::Tensor(..)),
                    &mut compiler.exact_work,
                )
                .map_err(|e| compiler.op_error(module, span, e))?
            }
            _ => {
                let steps = self
                    .materialize(access)
                    .map_err(|e| compiler.op_error(module, span, e))?;
                let bits = basis.basis_bits().expect("basis");
                RawProgram {
                    quantum_inputs: vec![QuantumPort {
                        token: TokenId(0),
                        wires: (0..bits as u32).map(WireId).collect(),
                        shape: BasisShape { bits: bits as u8 },
                    }],
                    classical_inputs: vec![],
                    operations: vec![RawOp::ApplyUnitary {
                        input: TokenId(0),
                        output: TokenId(1),
                        steps,
                    }],
                    quantum_outputs: vec![TokenId(1)],
                    classical_outputs: vec![],
                    declared_effect: Effect::Unitary,
                }
            }
        };
        crate::frontend::pure::check(
            &compiler.kernel,
            &raw,
            &contract_basis(&basis),
            &contract_basis(&codomain),
            Some(&expected),
            &mut compiler.exact_work,
        )
        .map_err(|e| compiler.op_error(module, span, e))
    }
}
