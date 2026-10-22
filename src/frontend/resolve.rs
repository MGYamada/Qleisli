//! Shared declaration identities and graph operations for untrusted source.
//!
//! IDs belong only to one immutable source collection. They are not persistent
//! evidence identities, and resolving a name proves no type/ownership property.
//! Lexical bindings and concrete adapter eligibility remain separate.

use std::collections::{BTreeMap, BTreeSet};

use super::ast::{FnKind, Module, Span};

mod exports;
pub(super) mod locals;
mod nominal;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ModuleId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct DefId(usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct TypeId(usize);

pub(super) use super::primitive::PrimitiveId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Target {
    Declaration(DefId),
    Primitive(PrimitiveId),
    Type(TypeId),
}

#[derive(Clone, Debug)]
pub(super) struct Declaration {
    pub module: ModuleId,
    pub name: (String, String),
    pub ast_index: usize,
    pub public: bool,
    pub kind: FnKind,
}

/// Original nominal declaration identity inside one retained source collection.
/// It is neither a function nor a persistent evidence/cache identifier.
#[derive(Clone, Debug)]
pub(super) struct TypeDeclaration {
    pub module: ModuleId,
    pub name: (String, String),
    pub ast_index: usize,
    pub public: bool,
}

#[derive(Clone, Debug)]
struct ModuleNames {
    name: String,
    declarations: BTreeMap<String, Target>,
    exports: BTreeMap<String, ExportBinding>,
    no_implicit_prelude: bool,
}

#[derive(Clone, Copy, Debug)]
struct ExportBinding {
    target: Target,
    /// Next source module in this exact public path. Retain resolver inputs
    /// without copying an entire transitive chain into every cached alias.
    next: ModuleId,
}

#[derive(Clone, Debug, Default)]
pub(super) struct Scope {
    pub imports: BTreeMap<String, Target>,
    import_modules: BTreeMap<String, ModuleId>,
    pub edges: Vec<(ModuleId, Span)>,
}

#[derive(Clone, Debug)]
pub(super) struct Resolution {
    modules: Vec<ModuleNames>,
    names: BTreeMap<String, ModuleId>,
    declarations: Vec<Declaration>,
    types: Vec<TypeDeclaration>,
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
    ExportCycle(String),
    PreludePrimitive(String),
    NotFunction(String),
    EmptyEnum(String),
    DuplicateMember { owner: String, member: String },
}

#[derive(Clone, Debug)]
pub(super) struct Failure {
    pub module: String,
    pub span: Span,
    pub kind: FailureKind,
}

pub(super) fn retired_public_name_hint(module: &str, name: &str) -> Option<&'static str> {
    match (module, name) {
        ("std::gate", "permute_axes") => Some(
            "; help: import `std::structure::permute_axes`; physical SWAP remains `std::gate::swap`",
        ),
        _ => super::primitive::retired_name_hint(module, name),
    }
}

impl Resolution {
    pub fn new<'a>(
        modules: impl IntoIterator<Item = (&'a str, &'a Module)>,
    ) -> Result<Self, Failure> {
        Self::new_budgeted(modules, |_, _| Ok(()))
    }

    /// Register the complete originals, charging visits and retained storage
    /// before sorting, copying names or inserting collection-local identities.
    pub fn new_budgeted<'a, E: From<Failure>>(
        modules: impl IntoIterator<Item = (&'a str, &'a Module)>,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Self, E> {
        let mut ordered = BTreeMap::new();
        for (name, ast) in modules {
            charge(ast.span, 1)?;
            if !ordered.contains_key(name) {
                charge(ast.span, 1)?;
            }
            ordered.insert(name, ast);
        }
        let mut result = Self {
            modules: Vec::new(),
            names: BTreeMap::new(),
            declarations: Vec::new(),
            types: Vec::new(),
            scopes: BTreeMap::new(),
        };
        for (&name, &ast) in &ordered {
            charge(ast.span, 1)?;
            let module = ModuleId(result.modules.len());
            let mut names = BTreeMap::new();
            // Diagnose the second declaration in source order before sorting.
            let mut functions = ast.decls.iter().enumerate().peekable();
            let mut types = ast.type_decls.iter().enumerate().peekable();
            while functions.peek().is_some() || types.peek().is_some() {
                let is_type = types.peek().is_some_and(|(_, ty)| {
                    functions
                        .peek()
                        .is_none_or(|(_, fun)| ty.span.start < fun.span.start)
                });
                let (index, ident) = if is_type {
                    let (index, decl) = types.next().expect("peeked type declaration");
                    (index, &decl.name)
                } else {
                    let (index, decl) = functions.next().expect("peeked function declaration");
                    (index, &decl.name)
                };
                charge(ident.span, 1)?;
                if names.contains_key(&ident.text) {
                    charge(ident.span, name.len() + ident.text.len() + 1)?;
                    return Err(E::from(Failure {
                        module: name.into(),
                        span: ident.span,
                        kind: FailureKind::Duplicate(ident.text.clone()),
                    }));
                }
                charge(ident.span, ident.text.len() + 1)?;
                if is_type {
                    nominal::check_members(name, &ast.type_decls[index], &mut charge)?;
                }
                names.insert(ident.text.clone(), (index, is_type));
            }
            let mut declarations = BTreeMap::new();
            for (decl_name, (ast_index, is_type)) in names {
                if is_type {
                    let decl = &ast.type_decls[ast_index];
                    let id = TypeId(result.types.len());
                    charge(decl.name.span, name.len() + decl_name.len() + 2)?;
                    result.types.push(TypeDeclaration {
                        module,
                        name: (name.into(), decl_name.clone()),
                        ast_index,
                        public: decl.public,
                    });
                    declarations.insert(decl_name, Target::Type(id));
                    continue;
                }
                let decl = &ast.decls[ast_index];
                let id = DefId(result.declarations.len());
                charge(decl.name.span, name.len() + decl_name.len() + 2)?;
                result.declarations.push(Declaration {
                    module,
                    name: (name.into(), decl_name.clone()),
                    ast_index,
                    public: decl.public,
                    kind: decl.kind,
                });
                declarations.insert(decl_name, Target::Declaration(id));
            }
            charge(
                ast.span,
                name.len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(2))
                    .unwrap_or(usize::MAX),
            )?;
            charge(ast.span, 2)?;
            result.names.insert(name.into(), module);
            result.modules.push(ModuleNames {
                name: name.into(),
                declarations,
                exports: BTreeMap::new(),
                no_implicit_prelude: ast.no_implicit_prelude,
            });
        }
        exports::prepare(&mut result, &ordered, &mut charge)?;
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
    pub fn type_declaration(&self, id: TypeId) -> &TypeDeclaration {
        &self.types[id.0]
    }
    pub fn try_type_declaration(&self, id: TypeId) -> Option<&TypeDeclaration> {
        self.types.get(id.0)
    }
    pub fn target_module(&self, target: Target) -> Option<ModuleId> {
        match target {
            Target::Declaration(id) => Some(self.declaration(id).module),
            Target::Type(id) => Some(self.type_declaration(id).module),
            Target::Primitive(_) => None,
        }
    }
    pub fn target_visible(&self, target: Target, requester: Option<ModuleId>) -> bool {
        match target {
            Target::Declaration(id) => self.visible(id, requester),
            Target::Type(id) => {
                let declaration = self.type_declaration(id);
                declaration.public || requester == Some(declaration.module)
            }
            Target::Primitive(_) => false,
        }
    }
    /// Fallible original identity lookup; never recover a declaration by name.
    pub fn try_declaration(&self, id: DefId) -> Option<&Declaration> {
        self.declarations.get(id.0)
    }
    pub fn declarations(&self) -> impl Iterator<Item = (DefId, &Declaration)> {
        self.declarations
            .iter()
            .enumerate()
            .map(|(i, d)| (DefId(i), d))
    }
    pub fn local(&self, module: ModuleId, name: &str) -> Option<DefId> {
        match self.local_target(module, name)? {
            Target::Declaration(id) => Some(id),
            _ => None,
        }
    }
    pub fn local_target(&self, module: ModuleId, name: &str) -> Option<Target> {
        self.modules[module.0].declarations.get(name).copied()
    }
    pub fn path(&self, id: DefId) -> String {
        let (module, name) = &self.declaration(id).name;
        format!("{module}::{name}")
    }
    pub fn qualified(&self, path: &str) -> Result<DefId, FailureKind> {
        match self.qualified_target(path)? {
            Target::Declaration(id) => Ok(id),
            _ => Err(FailureKind::NotFunction(path.into())),
        }
    }
    pub fn qualified_target(&self, path: &str) -> Result<Target, FailureKind> {
        let (module, name) = path.rsplit_once("::").ok_or(FailureKind::InvalidPath)?;
        let owner = self
            .module(module)
            .ok_or_else(|| FailureKind::MissingModule(module.into()))?;
        self.member(owner, name)
            .ok_or_else(|| FailureKind::MissingName {
                module: module.into(),
                name: name.into(),
            })
    }
    fn member(&self, module: ModuleId, name: &str) -> Option<Target> {
        self.local_target(module, name).or_else(|| {
            self.modules[module.0]
                .exports
                .get(name)
                .map(|binding| binding.target)
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
        if name.contains("::") {
            return self.lookup_visible(module, name).ok().flatten();
        }
        self.local_target(module, name)
            .or_else(|| {
                self.scopes
                    .get(&module)
                    .and_then(|scope| scope.imports.get(name).copied())
            })
            .or_else(|| {
                if self.modules[module.0].no_implicit_prelude {
                    return None;
                }
                let prelude = self.module("std::prelude")?;
                self.modules[prelude.0]
                    .exports
                    .get(name)
                    .map(|binding| binding.target)
            })
            .or_else(|| PrimitiveId::lookup_unbound(name).map(Target::Primitive))
    }

    /// Qualified references use the module namespace and original visibility,
    /// with no lexical, prelude or primitive fallback after a failed selection.
    pub fn lookup_visible(
        &self,
        caller: ModuleId,
        name: &str,
    ) -> Result<Option<Target>, FailureKind> {
        if let Some((module, item)) = name.rsplit_once("::") {
            if super::primitive::retired_name_hint(module, item).is_some() {
                return Err(FailureKind::UnknownPrimitive {
                    module: module.into(),
                    name: item.into(),
                });
            }
            let target = self.qualified_target(name)?;
            if !self.target_visible(target, Some(caller)) {
                return Err(FailureKind::Private(name.into()));
            }
            Ok(Some(target))
        } else {
            Ok(self.lookup(caller, name))
        }
    }

    /// Visit the exact source modules used to resolve one original global use.
    /// Canonical declaration identity does not erase an implicit opening or
    /// explicit reexport chain from the source/dependency snapshot.
    pub fn visit_name_sources<E>(
        &self,
        caller: ModuleId,
        name: &str,
        mut visit: impl FnMut(ModuleId) -> Result<(), E>,
    ) -> Result<(), E> {
        let (owner, item) = if let Some((module, item)) = name.rsplit_once("::") {
            (self.module(module), item)
        } else if self.local_target(caller, name).is_some() {
            (Some(caller), name)
        } else if let Some(owner) = self
            .scopes
            .get(&caller)
            .and_then(|s| s.import_modules.get(name))
        {
            (Some(*owner), name)
        } else if !self.modules[caller.0].no_implicit_prelude {
            (
                self.module("std::prelude")
                    .filter(|owner| self.modules[owner.0].exports.contains_key(name)),
                name,
            )
        } else {
            (None, name)
        };
        let Some(mut owner) = owner else {
            return Ok(());
        };
        loop {
            visit(owner)?;
            match self.modules[owner.0].exports.get(item) {
                Some(binding) => owner = binding.next,
                None => break,
            }
        }
        Ok(())
    }

    /// Source name resolution has one policy and one fixed typed primitive catalog.
    pub fn imports(&self, caller: ModuleId, ast: &Module) -> Result<Scope, Failure> {
        self.imports_budgeted(caller, ast, |_, _| Ok(()))
    }

    pub fn imports_budgeted<E: From<Failure>>(
        &self,
        caller: ModuleId,
        ast: &Module,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Scope, E> {
        let mut scope = Scope::default();
        for usage in &ast.uses {
            charge(usage.span, 1)?;
            let failure = |kind, span| {
                E::from(Failure {
                    module: self.module_name(caller).into(),
                    span,
                    kind,
                })
            };
            if usage.path.len() < 2 {
                charge(usage.span, self.module_name(caller).len() + 1)?;
                return Err(failure(FailureKind::InvalidPath, usage.span));
            }
            let last = usage.path.last().expect("validated import path");
            let mut length = 0usize;
            for token in &usage.path[..usage.path.len() - 1] {
                charge(token.span, 1)?;
                length = length
                    .checked_add(token.text.len())
                    .and_then(|n| n.checked_add(2))
                    .unwrap_or(usize::MAX);
            }
            // One module string, with no temporary vector of token references.
            charge(usage.span, length)?;
            let mut module = String::new();
            for token in &usage.path[..usage.path.len() - 1] {
                if !module.is_empty() {
                    module.push_str("::");
                }
                module.push_str(&token.text);
            }
            charge(
                last.span,
                module
                    .len()
                    .checked_add(last.text.len())
                    .and_then(|n| n.checked_add(2))
                    .unwrap_or(usize::MAX),
            )?;
            let path = format!("{module}::{}", last.text);
            // Every self-import collides with its same-module declaration,
            // including private declarations; direct private lookup stays legal.
            if module == self.module_name(caller) && self.local_target(caller, &last.text).is_some()
            {
                charge(
                    last.span,
                    self.module_name(caller)
                        .len()
                        .checked_add(last.text.len())
                        .and_then(|n| n.checked_add(1))
                        .unwrap_or(usize::MAX),
                )?;
                return Err(failure(
                    FailureKind::Collision(last.text.clone()),
                    last.span,
                ));
            }
            if super::primitive::retired_name_hint(&module, &last.text).is_some() {
                charge(
                    last.span,
                    self.module_name(caller)
                        .len()
                        .checked_add(last.text.len())
                        .and_then(|n| n.checked_add(1))
                        .unwrap_or(usize::MAX),
                )?;
                return Err(failure(
                    FailureKind::UnknownPrimitive {
                        module,
                        name: last.text.clone(),
                    },
                    last.span,
                ));
            }
            let Some(owner) = self.module(&module) else {
                charge(usage.span, self.module_name(caller).len() + 1)?;
                return Err(failure(FailureKind::MissingModule(module), usage.span));
            };
            let Some(id) = self.member(owner, &last.text) else {
                charge(
                    last.span,
                    self.module_name(caller).len() + last.text.len() + 1,
                )?;
                return Err(failure(
                    FailureKind::MissingName {
                        module,
                        name: last.text.clone(),
                    },
                    last.span,
                ));
            };
            if !self.target_visible(id, None) {
                charge(last.span, self.module_name(caller).len() + 1)?;
                return Err(failure(FailureKind::Private(path), last.span));
            }
            charge(usage.span, 1)?;
            scope.edges.push((
                self.target_module(id).expect("registered import target"),
                usage.span,
            ));
            let target = id;
            if self.local_target(caller, &last.text).is_some() {
                charge(
                    last.span,
                    self.module_name(caller)
                        .len()
                        .checked_add(last.text.len())
                        .and_then(|n| n.checked_add(1))
                        .unwrap_or(usize::MAX),
                )?;
                return Err(failure(
                    FailureKind::Collision(last.text.clone()),
                    last.span,
                ));
            }
            if scope.imports.contains_key(&last.text) {
                charge(
                    last.span,
                    self.module_name(caller)
                        .len()
                        .checked_add(last.text.len())
                        .and_then(|n| n.checked_add(1))
                        .unwrap_or(usize::MAX),
                )?;
                return Err(failure(
                    FailureKind::DuplicateImport(last.text.clone()),
                    last.span,
                ));
            }
            charge(
                last.span,
                last.text.len().saturating_mul(2).saturating_add(2),
            )?;
            scope.import_modules.insert(last.text.clone(), owner);
            scope.imports.insert(last.text.clone(), target);
        }
        Ok(scope)
    }

    pub fn set_scope_budgeted<E>(
        &mut self,
        module: ModuleId,
        scope: Scope,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<(), E> {
        if !self.scopes.contains_key(&module) {
            charge(Span::default(), 1)?;
        }
        self.scopes.insert(module, scope);
        Ok(())
    }
}

/// Iterative DFS, preserving root/edge order and the exact closing edge location.
pub(super) fn cycle_budgeted<N: Copy + Ord, E>(
    nodes: impl IntoIterator<Item = N>,
    edges: &BTreeMap<N, Vec<(N, Span)>>,
    allow_self: bool,
    mut charge: impl FnMut(Span, usize) -> Result<(), E>,
) -> Result<Option<(N, Span, Vec<N>)>, E> {
    let mut marks = BTreeMap::<N, u8>::new();
    let mut stack = Vec::<(N, usize)>::new();
    for node in nodes {
        charge(Span::default(), 1)?;
        if marks.get(&node) == Some(&2) {
            continue;
        }
        charge(Span::default(), 2)?;
        marks.insert(node, 1);
        stack.push((node, 0));
        while let Some((node, next)) = stack.last_mut() {
            let edge = edges.get(node).and_then(|e| e.get(*next)).copied();
            let span = edge.map_or(Span::default(), |(_, span)| span);
            charge(span, 1)?;
            let Some((target, span)) = edge else {
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
                    let mut start = None;
                    for (i, (n, _)) in stack.iter().enumerate() {
                        charge(span, 1)?;
                        if *n == target {
                            start = Some(i);
                            break;
                        }
                    }
                    let start = start.expect("active node");
                    charge(
                        span,
                        stack
                            .len()
                            .checked_sub(start)
                            .and_then(|n| n.checked_add(1))
                            .unwrap_or(usize::MAX),
                    )?;
                    let mut path: Vec<_> = stack[start..].iter().map(|(n, _)| *n).collect();
                    path.push(target);
                    return Ok(Some((owner, span, path)));
                }
                Some(2) => continue,
                _ => {
                    charge(span, 2)?;
                    marks.insert(target, 1);
                    stack.push((target, 0));
                }
            }
        }
    }
    Ok(None)
}

/// Canonically ordered Kahn traversal; return the first remaining declaration.
/// The outer failure is capacity; the inner failure is the unchanged first
/// remaining declaration. Ordering itself confers no source acceptance.
pub(super) fn order_budgeted<N: Copy + Ord, E>(
    mut pending: BTreeMap<N, BTreeSet<N>>,
    mut charge: impl FnMut(Span, usize) -> Result<(), E>,
) -> Result<Result<Vec<N>, N>, E> {
    let mut users = BTreeMap::<N, Vec<N>>::new();
    for (node, dependencies) in &pending {
        charge(Span::default(), 1)?;
        for target in dependencies {
            charge(Span::default(), 1)?;
            if !users.contains_key(target) {
                charge(Span::default(), 1)?;
            }
            charge(Span::default(), 1)?;
            users.entry(*target).or_default().push(*node);
        }
    }
    let mut ready = BTreeSet::new();
    for (node, deps) in &pending {
        charge(Span::default(), 1)?;
        if deps.is_empty() {
            charge(Span::default(), 1)?;
            ready.insert(*node);
        }
    }
    let mut result = Vec::new();
    while let Some(node) = ready.pop_first() {
        charge(Span::default(), 2)?;
        result.push(node);
        for user in users.get(&node).into_iter().flatten() {
            charge(Span::default(), 1)?;
            let dependencies = pending.get_mut(user).expect("known caller");
            dependencies.remove(&node);
            if dependencies.is_empty() {
                if !ready.contains(user) {
                    charge(Span::default(), 1)?;
                }
                ready.insert(*user);
            }
        }
        pending.remove(&node);
    }
    Ok(match pending.first_key_value() {
        Some((node, _)) => Err(*node),
        None => Ok(result),
    })
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
            no_implicit_prelude: false,
            type_decls: vec![],
            uses: vec![UseDecl {
                public: false,
                path: vec![],
                span,
            }],
            decls: vec![],
            span,
        };
        let table = Resolution::new([("a", &ast)]).unwrap();
        let error = table.imports(table.module("a").unwrap(), &ast).unwrap_err();
        assert_eq!(error.kind, FailureKind::InvalidPath);
        assert_eq!(error.span, span);
        assert_eq!(table.lookup(table.module("a").unwrap(), "missing"), None);
    }

    #[test]
    fn source_resolution_keeps_language_primitives_and_ordinary_imports_distinct() {
        let main =
            parse_module("use gates::x; pub unitary fn f(q:Q<Bit>)->Q<Bit>{h(x(q))}").unwrap();
        let gates = parse_module("pub unitary fn x(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let mut table = Resolution::new([("a", &main), ("gates", &gates)]).unwrap();
        let module = table.module("a").unwrap();
        let scope = table.imports(module, &main).unwrap();
        let imported = scope.imports["x"];
        assert!(matches!(imported, Target::Declaration(_)));
        table.set_scope(module, scope);
        assert_eq!(table.lookup(module, "x"), Some(imported));
        assert_eq!(
            table.lookup(module, "h"),
            Some(Target::Primitive(PrimitiveId::H))
        );
        let retired = parse_module("use std::quantum::h;").unwrap();
        assert!(matches!(
            table.imports(module, &retired).unwrap_err().kind,
            FailureKind::UnknownPrimitive { .. }
        ));
    }
}
