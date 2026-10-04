//! Shared declaration identities and graph operations for untrusted source.
//!
//! IDs belong only to one immutable source collection. They are not persistent
//! evidence identities, and resolving a name proves no type/ownership property.
//! Lexical bindings and the existing checking profiles remain separate.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{FnKind, Module, Span};

pub(super) mod locals;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ModuleId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct DefId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct PrimitiveId {
    pub module: &'static str,
    pub name: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Target {
    Declaration(DefId),
    Primitive(PrimitiveId),
}

/// Transitional acceptance differences, explicitly recorded in #41/#65/#32.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Profile {
    Finite,
    Sized,
}

#[derive(Clone, Debug)]
pub(super) struct Declaration {
    pub module: ModuleId,
    pub name: (String, String),
    pub ast_index: usize,
    pub public: bool,
    pub kind: FnKind,
}

#[derive(Clone, Debug)]
struct ModuleNames {
    name: String,
    declarations: BTreeMap<String, DefId>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct Scope {
    pub imports: BTreeMap<String, Target>,
    pub edges: Vec<(ModuleId, Span)>,
}

#[derive(Clone, Debug)]
pub(super) struct Resolution {
    modules: Vec<ModuleNames>,
    names: BTreeMap<String, ModuleId>,
    declarations: Vec<Declaration>,
    scopes: BTreeMap<ModuleId, Scope>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum FailureKind {
    InvalidPath,
    MissingModule(String),
    MissingName { module: String, name: String },
    UnknownPrimitive { module: String, name: String },
    Private(String),
    Collision(String),
    Duplicate(String),
    DuplicateImport(String),
}

#[derive(Clone, Debug)]
pub(super) struct Failure {
    pub module: String,
    pub span: Span,
    pub kind: FailureKind,
}

impl Resolution {
    pub fn new<'a>(
        modules: impl IntoIterator<Item = (&'a str, &'a Module)>,
    ) -> Result<Self, Failure> {
        let modules: BTreeMap<_, _> = modules.into_iter().collect();
        let mut result = Self {
            modules: Vec::new(),
            names: BTreeMap::new(),
            declarations: Vec::new(),
            scopes: BTreeMap::new(),
        };
        for (name, ast) in modules {
            let module = ModuleId(result.modules.len());
            let mut names = BTreeMap::new();
            // Diagnose the second declaration in source order before sorting.
            for (index, decl) in ast.decls.iter().enumerate() {
                if names.insert(decl.name.text.clone(), index).is_some() {
                    return Err(Failure {
                        module: name.into(),
                        span: decl.name.span,
                        kind: FailureKind::Duplicate(decl.name.text.clone()),
                    });
                }
            }
            let mut declarations = BTreeMap::new();
            for (decl_name, ast_index) in names {
                let decl = &ast.decls[ast_index];
                let id = DefId(result.declarations.len());
                result.declarations.push(Declaration {
                    module,
                    name: (name.into(), decl_name.clone()),
                    ast_index,
                    public: decl.public,
                    kind: decl.kind,
                });
                declarations.insert(decl_name, id);
            }
            result.names.insert(name.into(), module);
            result.modules.push(ModuleNames {
                name: name.into(),
                declarations,
            });
        }
        Ok(result)
    }

    pub fn module(&self, name: &str) -> Option<ModuleId> {
        self.names.get(name).copied()
    }
    pub fn module_name(&self, id: ModuleId) -> &str {
        &self.modules[id.0].name
    }
    pub fn declaration(&self, id: DefId) -> &Declaration {
        &self.declarations[id.0]
    }
    pub fn declarations(&self) -> impl Iterator<Item = (DefId, &Declaration)> {
        self.declarations
            .iter()
            .enumerate()
            .map(|(i, d)| (DefId(i), d))
    }
    pub fn modules(&self) -> impl Iterator<Item = ModuleId> + '_ {
        (0..self.modules.len()).map(ModuleId)
    }
    pub fn local(&self, module: ModuleId, name: &str) -> Option<DefId> {
        self.modules[module.0].declarations.get(name).copied()
    }
    pub fn path(&self, id: DefId) -> String {
        let (module, name) = &self.declaration(id).name;
        format!("{module}::{name}")
    }
    pub fn target_path(&self, target: Target) -> String {
        match target {
            Target::Declaration(id) => self.path(id),
            Target::Primitive(id) => format!("{}::{}", id.module, id.name),
        }
    }
    pub fn qualified(&self, path: &str) -> Result<DefId, FailureKind> {
        let (module, name) = path.rsplit_once("::").ok_or(FailureKind::InvalidPath)?;
        let owner = self
            .module(module)
            .ok_or_else(|| FailureKind::MissingModule(module.into()))?;
        self.local(owner, name)
            .ok_or_else(|| FailureKind::MissingName {
                module: module.into(),
                name: name.into(),
            })
    }
    /// An absent requester is a host entry selection, with no module privilege.
    pub fn visible(&self, id: DefId, requester: Option<ModuleId>) -> bool {
        let declaration = self.declaration(id);
        declaration.public || requester == Some(declaration.module)
    }
    pub fn scope(&self, module: ModuleId) -> &Scope {
        &self.scopes[&module]
    }
    pub fn set_scope(&mut self, module: ModuleId, scope: Scope) {
        self.scopes.insert(module, scope);
    }
    pub fn lookup(&self, module: ModuleId, name: &str) -> Option<Target> {
        self.local(module, name)
            .map(Target::Declaration)
            .or_else(|| {
                self.scopes
                    .get(&module)
                    .and_then(|scope| scope.imports.get(name).copied())
            })
    }

    pub fn imports(
        &self,
        caller: ModuleId,
        ast: &Module,
        profile: Profile,
    ) -> Result<Scope, Failure> {
        let mut scope = Scope::default();
        for usage in &ast.uses {
            let failure = |kind, span| Failure {
                module: self.module_name(caller).into(),
                span,
                kind,
            };
            if usage.path.len() < 2 {
                return Err(failure(FailureKind::InvalidPath, usage.span));
            }
            let last = usage.path.last().expect("validated import path");
            let module = usage.path[..usage.path.len() - 1]
                .iter()
                .map(|s| s.text.as_str())
                .collect::<Vec<_>>()
                .join("::");
            let path = format!("{module}::{}", last.text);
            let target = if let Some(primitive) = primitive(&path, profile) {
                Target::Primitive(primitive)
            } else {
                if profile == Profile::Finite
                    && matches!(module.as_str(), "std::quantum" | "std::observe")
                {
                    return Err(failure(
                        FailureKind::UnknownPrimitive {
                            module,
                            name: last.text.clone(),
                        },
                        last.span,
                    ));
                }
                let id = self.qualified(&path).map_err(|kind| {
                    let span = if profile == Profile::Finite
                        && matches!(kind, FailureKind::MissingName { .. })
                    {
                        last.span
                    } else {
                        usage.span
                    };
                    failure(kind, span)
                })?;
                let requester = (profile == Profile::Sized).then_some(caller);
                if !self.visible(id, requester) {
                    return Err(failure(
                        FailureKind::Private(path),
                        if profile == Profile::Finite {
                            last.span
                        } else {
                            usage.span
                        },
                    ));
                }
                scope.edges.push((self.declaration(id).module, usage.span));
                Target::Declaration(id)
            };
            let local = self.local(caller, &last.text).map(Target::Declaration);
            let collides = local.is_some() && !(profile == Profile::Sized && local == Some(target));
            if collides || scope.imports.contains_key(&last.text) {
                return Err(failure(
                    if collides {
                        FailureKind::Collision(last.text.clone())
                    } else {
                        FailureKind::DuplicateImport(last.text.clone())
                    },
                    if profile == Profile::Finite {
                        last.span
                    } else {
                        usage.span
                    },
                ));
            }
            scope.imports.insert(last.text.clone(), target);
        }
        Ok(scope)
    }
}

fn primitive(path: &str, profile: Profile) -> Option<PrimitiveId> {
    match profile {
        Profile::Finite => super::core::PRIMITIVES
            .iter()
            .find(|p| {
                path.strip_prefix(p.module)
                    .and_then(|s| s.strip_prefix("::"))
                    == Some(p.name)
            })
            .map(|p| PrimitiveId {
                module: p.module,
                name: p.name,
            }),
        Profile::Sized => super::sized::primitive_path(path).map(|path| {
            let (module, name) = path.rsplit_once("::").expect("sealed qualified name");
            PrimitiveId { module, name }
        }),
    }
}

/// Iterative DFS, preserving root/edge order and the exact closing edge location.
pub(super) fn cycle<N: Copy + Ord>(
    nodes: impl IntoIterator<Item = N>,
    edges: &BTreeMap<N, Vec<(N, Span)>>,
    allow_self: bool,
) -> Option<(N, Span, Vec<N>)> {
    let mut marks = BTreeMap::<N, u8>::new();
    let mut stack = Vec::<(N, usize)>::new();
    for node in nodes {
        if marks.get(&node) == Some(&2) {
            continue;
        }
        marks.insert(node, 1);
        stack.push((node, 0));
        while let Some((node, next)) = stack.last_mut() {
            let Some(&(target, span)) = edges.get(node).and_then(|e| e.get(*next)) else {
                marks.insert(*node, 2);
                stack.pop();
                continue;
            };
            *next += 1;
            if allow_self && target == *node {
                continue;
            }
            match marks.get(&target) {
                Some(1) => {
                    let owner = *node;
                    let start = stack
                        .iter()
                        .position(|(n, _)| *n == target)
                        .expect("active node");
                    let mut path: Vec<_> = stack[start..].iter().map(|(n, _)| *n).collect();
                    path.push(target);
                    return Some((owner, span, path));
                }
                Some(2) => continue,
                _ => {
                    marks.insert(target, 1);
                    stack.push((target, 0));
                }
            }
        }
    }
    None
}

/// Canonically ordered Kahn traversal; return the first remaining declaration.
pub(super) fn order<N: Copy + Ord>(mut pending: BTreeMap<N, BTreeSet<N>>) -> Result<Vec<N>, N> {
    let mut users = BTreeMap::<N, Vec<N>>::new();
    for (node, dependencies) in &pending {
        for target in dependencies {
            users.entry(*target).or_default().push(*node);
        }
    }
    let mut ready: BTreeSet<_> = pending
        .iter()
        .filter(|(_, deps)| deps.is_empty())
        .map(|(n, _)| *n)
        .collect();
    let mut result = Vec::new();
    while let Some(node) = ready.pop_first() {
        result.push(node);
        for user in users.get(&node).into_iter().flatten() {
            let dependencies = pending.get_mut(user).expect("known caller");
            dependencies.remove(&node);
            if dependencies.is_empty() {
                ready.insert(*user);
            }
        }
        pending.remove(&node);
    }
    match pending.first_key_value() {
        Some((node, _)) => Err(*node),
        None => Ok(result),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{ast::UseDecl, parser::parse_module};

    #[test]
    fn all_declarations_have_canonical_collection_local_identities() {
        let a =
            parse_module("pub unitary fn z(q:Q<Bit>)->Q<Bit>{q} unitary fn a(q:Q<Bit>)->Q<Bit>{q}")
                .unwrap();
        let b = parse_module("pub unitary fn a(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let first = Resolution::new([("b", &b), ("a", &a)]).unwrap();
        let second = Resolution::new([("a", &a), ("b", &b)]).unwrap();
        let paths: Vec<_> = first.declarations().map(|(id, _)| first.path(id)).collect();
        assert_eq!(paths, ["a::a", "a::z", "b::a"]);
        for path in paths {
            assert_eq!(first.qualified(&path), second.qualified(&path));
        }
        let private = first.qualified("a::a").unwrap();
        assert!(first.visible(private, first.module("a")));
        assert!(!first.visible(private, first.module("b")));
        assert!(!first.visible(private, None));
        assert_ne!(private, first.qualified("b::a").unwrap());
        assert_eq!(first.declaration(private).ast_index, 1);
    }

    #[test]
    fn constructed_empty_import_is_a_located_error() {
        let span = Span::new(9, 12);
        let ast = Module {
            uses: vec![UseDecl { path: vec![], span }],
            decls: vec![],
            span,
        };
        let table = Resolution::new([("a", &ast)]).unwrap();
        for profile in [Profile::Finite, Profile::Sized] {
            let error = table
                .imports(table.module("a").unwrap(), &ast, profile)
                .unwrap_err();
            assert_eq!(error.kind, FailureKind::InvalidPath);
            assert_eq!(error.span, span);
        }
        assert_eq!(table.lookup(table.module("a").unwrap(), "missing"), None);
    }

    #[test]
    fn sealed_identity_does_not_expand_either_primitive_profile() {
        let ast = parse_module("use std::registers::empty; pub unitary fn f()->(){()}").unwrap();
        let table = Resolution::new([("a", &ast)]).unwrap();
        let module = table.module("a").unwrap();
        assert!(matches!(
            table
                .imports(module, &ast, Profile::Finite)
                .unwrap_err()
                .kind,
            FailureKind::MissingModule(_)
        ));
        assert!(matches!(
            table.imports(module, &ast, Profile::Sized).unwrap().imports["empty"],
            Target::Primitive(_)
        ));
        let ast =
            parse_module("use std::quantum::z; pub unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        assert!(table.imports(module, &ast, Profile::Finite).is_ok());
        assert!(matches!(
            table
                .imports(module, &ast, Profile::Sized)
                .unwrap_err()
                .kind,
            FailureKind::MissingModule(_)
        ));
    }
}
