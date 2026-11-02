//! Describe the retained original operation tree for the paired native request.
//! Each child edge is copied in postorder. No capability, matrix, inferred
//! effect or success receipt is encoded; the native original reader derives it.
// Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
use super::*;
use crate::interchange::qmatch::{Description, OperationNode, OperationSubject, OriginalBody};

struct Instance<'a> {
    module: String,
    function: String,
    bases: Vec<(String, Vec<crate::interchange::carrier::Atom>)>,
    naturals: Vec<(String, u32)>,
    operations: Vec<(String, &'a Operation)>,
}

enum Finish<'a> {
    Provider(Instance<'a>, &'a Operation, &'a Arc<ProviderOrigin>),
    Formal(Instance<'a>, u32),
    Inverse,
    Then,
    Tensor,
    Controlled,
    Power(u16),
    Conjugate,
    Requested(Key),
}

enum Task<'a> {
    Enter(&'a Operation, usize),
    Leave(Finish<'a>, usize),
}

impl Compiler<'_> {
    fn source_description_instance<'a>(
        &mut self,
        definition: Key,
        instance: Option<&'a super::super::instances::ClosedInstance>,
        table: &Arc<crate::frontend::resolve::locals::Table>,
        module: &str,
        span: Span,
    ) -> Result<Instance<'a>, CompileError> {
        if !Arc::ptr_eq(table, &self.source.lexical[&definition])
            || instance.is_some_and(|instance| instance.definition != definition)
        {
            return Err(self.error(
                module,
                span,
                ErrorCode::InvalidIr,
                "operation description lost its original declaration instance",
            ));
        }
        let declaration = self.declarations[&definition];
        if !declaration.static_params.is_empty() && instance.is_none() {
            return Err(self.error(
                module,
                span,
                ErrorCode::Unsupported,
                "operation description requires every original static actual",
            ));
        }
        let name = &self.source.resolution.declaration(definition).name;
        self.charge(
            module,
            span,
            name.0.len() + name.1.len() + declaration.static_params.len() + 4,
        )?;
        let name = self.source.resolution.declaration(definition).name.clone();
        let mut result = Instance {
            module: name.0,
            function: name.1,
            bases: Vec::new(),
            naturals: Vec::new(),
            operations: Vec::new(),
        };
        for (ordinal, parameter) in declaration.static_params.iter().enumerate() {
            let formal = &self.source.interfaces[&definition].statics[ordinal];
            self.charge(
                module,
                span,
                formal.key.name.len() + parameter.name.text.len() + 4,
            )?;
            let key = self.source.interfaces[&definition].statics[ordinal]
                .key
                .clone();
            let Some(instance) = instance else {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "nonempty original formals have no retained actual instance",
                ));
            };
            match &parameter.kind {
                StaticParamKind::Basis => {
                    let basis = instance.interface.bases.get(&key).ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "original Basis actual is missing",
                        )
                    })?;
                    let atoms = if basis.basis_bits().is_some() {
                        self.charge(module, span, 2 * basis.tree_size().nodes + 1)?;
                        let mut pending = vec![basis];
                        let mut atoms = Vec::new();
                        while let Some(basis) = pending.pop() {
                            use crate::interchange::carrier::Atom;
                            atoms.push(match &basis.kind {
                                Kind::Unit => Atom::Unit,
                                Kind::Bit => Atom::Bit,
                                Kind::Bits(width) => Atom::Bits(*width),
                                Kind::Tuple(fields) => {
                                    pending.extend(fields.iter().rev());
                                    if fields.len() == 2 {
                                        Atom::Pair
                                    } else {
                                        Atom::Tuple(fields.len() as u32)
                                    }
                                }
                                _ => unreachable!("the original closed Basis is built in"),
                            });
                        }
                        atoms
                    } else {
                        self.carrier_description(module, span, basis)?
                    };
                    result.bases.push((parameter.name.text.clone(), atoms));
                }
                StaticParamKind::Natural => {
                    let value = *instance.interface.naturals.get(&key).ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "original Nat actual is missing",
                        )
                    })?;
                    result.naturals.push((parameter.name.text.clone(), value));
                }
                StaticParamKind::Operation { .. } => {
                    let operation = instance.operations.get(&key).ok_or_else(|| {
                        self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "original Op actual is missing",
                        )
                    })?;
                    result
                        .operations
                        .push((parameter.name.text.clone(), operation));
                }
            }
        }
        if let Some(instance) = instance {
            if result.bases.len() != instance.interface.bases.len()
                || result.naturals.len() != instance.interface.naturals.len()
                || result.operations.len() != instance.operations.len()
            {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::InvalidIr,
                    "operation description has foreign or unbound static actuals",
                ));
            }
        }
        Ok(result)
    }

    pub(in crate::frontend::compile) fn qmatch_operation_application(
        &mut self,
        operation: &Operation,
        access: Access,
        module: &str,
        span: Span,
    ) -> Result<OperationSubject, CompileError> {
        let mut subject = self.qmatch_operation_subject(operation, module, span)?;
        if access != Access::Apply {
            if subject.description.nodes.len() >= MAX_TREE_NODES || operation.depth >= MAX_DEPTH {
                return Err(self.error(
                    module,
                    span,
                    ErrorCode::Limit,
                    "transformed original operation exceeds the existing tree profile",
                ));
            }
            self.charge(module, span, 4)?;
            let child = subject.description.root;
            subject.description.root = subject.description.nodes.len() as u32;
            subject.description.nodes.push(match access {
                Access::Adjoint => OperationNode::Inverse(child),
                Access::Controlled => OperationNode::Controlled(child),
                Access::Apply => unreachable!(),
            });
        }
        Ok(subject)
    }

    /// This is proposal generation from the same retained lowering objects.
    /// The complete native body/access/Meaning gate remains mandatory, including
    /// unused original actuals and children beneath a zero power.
    pub(in crate::frontend::compile) fn qmatch_operation_subject(
        &mut self,
        operation: &Operation,
        module: &str,
        span: Span,
    ) -> Result<OperationSubject, CompileError> {
        let mut pending = vec![Task::Enter(operation, 0)];
        let mut stack = Vec::new();
        let mut nodes = Vec::new();
        let mut bodies = Vec::new();
        let mut entered = 0usize;
        while let Some(task) = pending.pop() {
            self.charge(module, span, 8)?;
            match task {
                Task::Enter(operation, depth) => {
                    entered += 1;
                    if entered > MAX_TREE_NODES || depth >= MAX_DEPTH {
                        return Err(self.error(
                            module,
                            span,
                            ErrorCode::Limit,
                            "original operation description exceeds the existing tree profile",
                        ));
                    }
                    // A lexical formal denotes its full original supplying
                    // instance, not the convenient underlying provider node.
                    if let Some(formal) = &operation.source_formal {
                        let Some(instance) = formal.instance.as_deref() else {
                            return Err(self.error(
                                module,
                                span,
                                ErrorCode::Unsupported,
                                "dormant Op references have no concrete original instance",
                            ));
                        };
                        let shape = self.source_description_instance(
                            formal.definition,
                            Some(instance),
                            &formal.table,
                            module,
                            span,
                        )?;
                        if !matches!(
                            self.declarations[&formal.definition]
                                .static_params
                                .get(formal.ordinal)
                                .map(|parameter| &parameter.kind),
                            Some(StaticParamKind::Operation { .. })
                        ) {
                            return Err(self.error(
                                module,
                                span,
                                ErrorCode::InvalidIr,
                                "Op reference lost its original mixed formal ordinal",
                            ));
                        }
                        let count = shape.operations.len();
                        let children = shape
                            .operations
                            .iter()
                            .map(|(_, operation)| *operation)
                            .collect::<Vec<_>>();
                        pending.push(Task::Leave(
                            Finish::Formal(shape, formal.ordinal as u32),
                            count,
                        ));
                        for child in children.into_iter().rev() {
                            pending.push(Task::Enter(child, depth + 1));
                        }
                        continue;
                    }
                    match operation.node.as_ref() {
                        Node::Provider(_) | Node::Pure(_) => {
                            let origin = operation.source_origin.as_ref().ok_or_else(|| {
                                self.error(
                                    module,
                                    span,
                                    ErrorCode::InvalidIr,
                                    "provider description lacks its actual original body",
                                )
                            })?;
                            let shape = self.source_description_instance(
                                origin.definition,
                                origin.instance.as_deref(),
                                &origin.table,
                                module,
                                span,
                            )?;
                            let count = shape.operations.len();
                            let children = shape
                                .operations
                                .iter()
                                .map(|(_, operation)| *operation)
                                .collect::<Vec<_>>();
                            pending.push(Task::Leave(
                                Finish::Provider(shape, operation, origin),
                                count,
                            ));
                            for child in children.into_iter().rev() {
                                pending.push(Task::Enter(child, depth + 1));
                            }
                        }
                        Node::Inverse(child)
                        | Node::Controlled(child)
                        | Node::Repeat(_, child)
                        | Node::Requested(_, child) => {
                            let finish = match operation.node.as_ref() {
                                Node::Inverse(_) => Finish::Inverse,
                                Node::Controlled(_) => Finish::Controlled,
                                Node::Repeat(count, _) => Finish::Power(*count),
                                Node::Requested(meaning, _) => Finish::Requested(*meaning),
                                _ => unreachable!(),
                            };
                            pending.push(Task::Leave(finish, 1));
                            pending.push(Task::Enter(child, depth + 1));
                        }
                        Node::Then(left, right)
                        | Node::Tensor(left, right)
                        | Node::Conjugate(left, right) => {
                            let finish = match operation.node.as_ref() {
                                Node::Then(..) => Finish::Then,
                                Node::Tensor(..) => Finish::Tensor,
                                _ => Finish::Conjugate,
                            };
                            pending.push(Task::Leave(finish, 2));
                            pending.push(Task::Enter(right, depth + 1));
                            pending.push(Task::Enter(left, depth + 1));
                        }
                    }
                }
                Task::Leave(finish, count) => {
                    if stack.len() < count || nodes.len() >= MAX_TREE_NODES {
                        return Err(self.error(
                            module,
                            span,
                            ErrorCode::InvalidIr,
                            "incomplete original operation description traversal",
                        ));
                    }
                    let children = stack.split_off(stack.len() - count);
                    let mut requested = None;
                    let node = match finish {
                        Finish::Provider(shape, operation, origin) => {
                            let context =
                                origin.body.source_context().cloned().ok_or_else(|| {
                                    self.error(
                                        module,
                                        span,
                                        ErrorCode::InvalidIr,
                                        "provider body has no original lowering coordinates",
                                    )
                                })?;
                            self.charge(
                                module,
                                span,
                                8 + total_size(
                                    origin
                                        .body
                                        .output_ports()
                                        .iter()
                                        .map(|port| port.wires.len() + 3),
                                ),
                            )?;
                            bodies.push(match operation.node.as_ref() {
                                Node::Provider(evidence) => OriginalBody::Function {
                                    evidence: Arc::clone(evidence),
                                    context,
                                },
                                Node::Pure(_) => OriginalBody::Pure {
                                    program: origin.body.clone(),
                                    context,
                                },
                                _ => unreachable!(),
                            });
                            requested = origin.meaning;
                            OperationNode::Provider {
                                module: shape.module,
                                function: shape.function,
                                bases: shape.bases,
                                naturals: shape.naturals,
                                operations: shape
                                    .operations
                                    .into_iter()
                                    .map(|(name, _)| name)
                                    .zip(children)
                                    .collect(),
                            }
                        }
                        Finish::Formal(shape, ordinal) => OperationNode::Formal {
                            module: shape.module,
                            function: shape.function,
                            bases: shape.bases,
                            naturals: shape.naturals,
                            operations: shape
                                .operations
                                .into_iter()
                                .map(|(name, _)| name)
                                .zip(children)
                                .collect(),
                            ordinal,
                        },
                        Finish::Inverse => OperationNode::Inverse(children[0]),
                        Finish::Then => OperationNode::Then(children[0], children[1]),
                        Finish::Tensor => OperationNode::Tensor(children[0], children[1]),
                        Finish::Controlled => OperationNode::Controlled(children[0]),
                        Finish::Power(count) => OperationNode::Power {
                            child: children[0],
                            count: u32::from(count),
                        },
                        Finish::Conjugate => OperationNode::Conjugate {
                            outer: children[0],
                            middle: children[1],
                        },
                        Finish::Requested(meaning) => {
                            let name = &self.source.resolution.declaration(meaning).name;
                            self.charge(module, span, name.0.len() + name.1.len() + 2)?;
                            let name = self.source.resolution.declaration(meaning).name.clone();
                            OperationNode::Requested {
                                child: children[0],
                                module: name.0,
                                function: name.1,
                            }
                        }
                    };
                    let mut index = nodes.len() as u32;
                    nodes.push(node);
                    if let Some(meaning) = requested {
                        if nodes.len() >= MAX_TREE_NODES {
                            return Err(self.error(
                                module,
                                span,
                                ErrorCode::Limit,
                                "original checked operation exceeds the existing tree profile",
                            ));
                        }
                        let name = &self.source.resolution.declaration(meaning).name;
                        self.charge(module, span, name.0.len() + name.1.len() + 4)?;
                        let name = self.source.resolution.declaration(meaning).name.clone();
                        nodes.push(OperationNode::Requested {
                            child: index,
                            module: name.0,
                            function: name.1,
                        });
                        index += 1;
                    }
                    stack.push(index);
                }
            }
        }
        let [root] = stack.as_slice() else {
            return Err(self.error(
                module,
                span,
                ErrorCode::InvalidIr,
                "operation description has multiple roots",
            ));
        };
        Ok(OperationSubject {
            description: Description { nodes, root: *root },
            bodies,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::project::{ModuleOrigin, ProjectEdition, SourceModule};

    #[cfg_attr(
        not(qleisli_native_tests),
        ignore = "native-kernel gate: requires QLEISLI_KERNEL"
    )]
    #[test]
    fn direct_formal_call_retains_unused_duplicate_suppliers_and_mixed_ordinal() {
        let source = "unitary fn phase(q:Q<Unit>)->Q<Unit>{global_phase_eighth(q)}\n\
            unitary fn run[const n:Nat,const U:Op<Unit>,const V:Op<Unit>](q:Q<Unit>)->Q<Unit>\
            requires Applicable(U){U(q)}\n\
            pub unitary fn main(q:Q<Unit>)->Q<Unit>{run[3,phase,phase](q)}";
        let project = Project {
            edition_context: ProjectEdition::Explicit(crate::edition::Edition::E2026),
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
        };
        let mut compiler = crate::frontend::compile::snapshot_tests::compiler(&project);
        let main = compiler.source.resolution.qualified("main::main").unwrap();
        let body = crate::frontend::compile::lower::lower_function(&mut compiler, &main).unwrap();
        let context = body.source_context().unwrap();
        let (position, run) = &context.calls[0];
        assert_eq!((position.start, position.count), (0, 1));
        let (position, application) = &run.calls[0];
        assert_eq!((position.start, position.count), (0, 1));
        assert!(
            application.positions.is_empty()
                && application.selections.is_empty()
                && application.calls.is_empty()
                && application.branches.is_empty()
        );
        let actual = application.operation.as_ref().unwrap();
        assert_eq!(actual.bodies.len(), 2);
        assert_eq!(actual.description.root, 2);
        assert!(
            matches!(&actual.description.nodes[2], OperationNode::Formal {
            module, function, naturals, operations, ordinal: 1, ..
        } if module == "main" && function == "run" && naturals == &[("n".into(), 3)]
            && operations == &[("U".into(), 0), ("V".into(), 1)])
        );
        for index in [0, 1] {
            assert!(
                matches!(&actual.description.nodes[index], OperationNode::Provider {
                module, function, bases, naturals, operations
            } if module == "main" && function == "phase"
                && bases.is_empty() && naturals.is_empty() && operations.is_empty())
            );
        }
        // Equal retained evidence never erases the unused V occurrence.
        assert!(matches!((&actual.bodies[0], &actual.bodies[1]),
            (OriginalBody::Function { evidence: left, .. }, OriginalBody::Function { evidence: right, .. })
                if Arc::ptr_eq(left, right)));
    }
}
