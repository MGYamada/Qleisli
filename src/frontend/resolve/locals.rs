//! Lexical identities from the one source AST; not ownership or type evidence.
//!
//! IDs are assigned in structural traversal order, independently of source
//! spans and allocation addresses. An Index borrows one immovable declaration:
//! its address map only locates AST occurrences during that borrow. Projections
//! retain the numeric IDs and Table, never this map. Dynamic binding/owner IDs
//! remain separate: one source binder can execute many times in a fold or call.

use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::sync::Arc;

use super::{DefId, Target};
use crate::frontend::ast::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct BinderId {
    definition: DefId,
    ordinal: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct UseSiteId {
    definition: DefId,
    ordinal: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct ScopeId {
    definition: DefId,
    ordinal: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum BindingKind {
    Runtime,
    Basis,
    StaticNatural,
    StaticBasis,
    StaticOperation,
    FoldIndex,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum ResolvedUse {
    Local(BinderId),
    Global(Target),
    Unresolved,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct BinderKey {
    pub name: String,
    pub id: BinderId,
}
impl std::fmt::Display for BinderKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct BinderInfo {
    pub key: BinderKey,
    pub shadowed: Option<BinderId>,
    pub span: Span,
    pub kind: BindingKind,
    pub scope: ScopeId,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct UseInfo {
    pub name: String,
    pub span: Span,
    pub scope: ScopeId,
    pub target: ResolvedUse,
    // A candidate only. Source checking still rejects non-callable local names.
    pub global: Option<Target>,
    // Compatibility candidate for the finite static-call diagnostic order.
    // A runtime shadow still resolves to Local(runtime) and must be rejected.
    pub static_parameter: Option<BinderId>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct Table {
    definition: DefId,
    binders: Vec<BinderInfo>,
    uses: Vec<UseInfo>,
    scopes: Vec<Option<ScopeId>>,
}
impl Table {
    pub fn binder(&self, id: BinderId) -> &BinderInfo {
        assert_eq!(
            id.definition, self.definition,
            "binder belongs to another declaration"
        );
        &self.binders[id.ordinal]
    }
    pub fn key(&self, id: BinderId) -> &BinderKey {
        &self.binder(id).key
    }
    pub fn usage(&self, id: UseSiteId) -> &UseInfo {
        assert_eq!(
            id.definition, self.definition,
            "use belongs to another declaration"
        );
        &self.uses[id.ordinal]
    }

    /// Post-rejection diagnostic lookup, never lexical resolution or evidence.
    /// A duplicate occurrence span is ambiguous even if its targets agree.
    pub(in crate::frontend) fn local_use_at_span<E>(
        &self,
        span: Span,
        mut charge: impl FnMut() -> Result<(), E>,
    ) -> Result<Option<BinderId>, E> {
        let mut found = None;
        for usage in &self.uses {
            charge()?;
            if usage.span == span {
                if found.is_some() {
                    return Ok(None);
                }
                found = Some(usage.target);
            }
        }
        Ok(match found {
            Some(ResolvedUse::Local(id)) => Some(id),
            _ => None,
        })
    }
}

/// A source-address lookup is valid only for this borrowed declaration. It is
/// deliberately not Clone: re-index cloned/moved syntax rather than copying it.
pub(in crate::frontend) struct Index<'ast> {
    pub table: Table,
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    natural_references: BTreeMap<usize, UseSiteId>,
    _syntax: PhantomData<&'ast Decl>,
}
impl<'ast> Index<'ast> {
    pub fn new_budgeted<E>(
        definition: DefId,
        declaration: &'ast Decl,
        global: impl Fn(&str) -> Option<Target>,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Self, E> {
        charge(declaration.span, 2)?;
        let mut builder = Builder {
            index: Self {
                table: Table {
                    definition,
                    binders: vec![],
                    uses: vec![],
                    scopes: vec![None],
                },
                bindings: BTreeMap::new(),
                references: BTreeMap::new(),
                natural_references: BTreeMap::new(),
                _syntax: PhantomData,
            },
            global,
            charge,
            origin: declaration.span,
            names: BTreeMap::new(),
            static_parameters: BTreeMap::new(),
            frames: vec![Frame {
                id: ScopeId {
                    definition,
                    ordinal: 0,
                },
                undo: vec![],
            }],
        };
        builder.declaration(declaration)?;
        Ok(builder.index)
    }
    /// Transfer the finite consumer's occurrence lookup, retaining the one
    /// authoritative Table and the natural addresses needed by source checking.
    pub fn take_occurrences(&mut self) -> Occurrences<'ast> {
        Occurrences {
            bindings: std::mem::take(&mut self.bindings),
            references: std::mem::take(&mut self.references),
            _syntax: PhantomData,
        }
    }
    pub fn binder(&self, name: &Ident) -> BinderId {
        self.bindings[&(std::ptr::from_ref(name) as usize)]
    }
    pub fn usage(&self, name: &Ident) -> UseSiteId {
        self.references[&(std::ptr::from_ref(name) as usize)]
    }
    pub fn natural_usage(&self, natural: &Natural) -> UseSiteId {
        self.natural_references[&(std::ptr::from_ref(natural) as usize)]
    }
    #[cfg(test)]
    pub fn resolve(&self, name: &Ident) -> ResolvedUse {
        self.table.usage(self.usage(name)).target
    }
}

/// Address-only lookup moves independently of the authoritative lexical Table.
pub(in crate::frontend) struct Occurrences<'ast> {
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    _syntax: PhantomData<&'ast Decl>,
}
#[derive(Default)]
pub(in crate::frontend) struct OccurrencesForest<'ast> {
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    _syntax: PhantomData<&'ast Decl>,
}
impl<'ast> OccurrencesForest<'ast> {
    pub fn insert_budgeted<E>(
        &mut self,
        occurrences: Occurrences<'ast>,
        span: Span,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<(), E> {
        // Insert moved keys individually: do not rebuild/copy the existing
        // aggregate tree as append may do. Precharge each incoming visit and
        // new address cell before consuming its original map iterator.
        let cells = occurrences
            .bindings
            .len()
            .checked_add(occurrences.references.len())
            .and_then(|n| n.checked_mul(2))
            .unwrap_or(usize::MAX);
        charge(span, cells)?;
        for (address, id) in occurrences.bindings {
            self.bindings.insert(address, id);
        }
        for (address, id) in occurrences.references {
            self.references.insert(address, id);
        }
        Ok(())
    }
}

/// Borrowed source occurrences share the single checked lexical Table allocation.
#[derive(Default)]
pub(in crate::frontend) struct Forest<'ast> {
    tables: BTreeMap<DefId, Arc<Table>>,
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    _syntax: PhantomData<&'ast Decl>,
}
impl<'ast> Forest<'ast> {
    pub fn from_occurrences(
        tables: BTreeMap<DefId, Arc<Table>>,
        occurrences: OccurrencesForest<'ast>,
    ) -> Self {
        Self {
            tables,
            bindings: occurrences.bindings,
            references: occurrences.references,
            _syntax: PhantomData,
        }
    }
    pub fn binder(&self, name: &Ident) -> BinderId {
        self.bindings[&(std::ptr::from_ref(name) as usize)]
    }
    pub fn info(&self, id: BinderId) -> &BinderInfo {
        self.tables[&id.definition].binder(id)
    }
    pub fn key(&self, id: BinderId) -> &BinderKey {
        self.tables[&id.definition].key(id)
    }
    pub fn usage(&self, name: &Ident) -> &UseInfo {
        let id = self.references[&(std::ptr::from_ref(name) as usize)];
        self.tables[&id.definition].usage(id)
    }
    pub fn local_key(&self, name: &Ident) -> Option<&BinderKey> {
        match self.usage(name).target {
            ResolvedUse::Local(id) => Some(self.key(id)),
            ResolvedUse::Global(_) | ResolvedUse::Unresolved => None,
        }
    }
}

struct Frame {
    id: ScopeId,
    undo: Vec<(String, Option<BinderId>)>,
}
struct Builder<'ast, F, C> {
    index: Index<'ast>,
    global: F,
    charge: C,
    origin: Span,
    names: BTreeMap<String, BinderId>,
    static_parameters: BTreeMap<String, BinderId>,
    frames: Vec<Frame>,
}
enum Task<'a> {
    Enter,
    EnterBasis,
    Leave,
    Reference(&'a Ident),
    Bind(&'a Ident, BindingKind),
    Pattern(&'a Pattern, BindingKind),
    Type(&'a Type),
    Natural(&'a Natural),
    Predicate(&'a Predicate),
    Operation(&'a StaticOp),
    Basis(&'a BasisExpr),
    Block(&'a Block),
    Expression(&'a Expr),
}
impl Task<'_> {
    fn span(&self, origin: Span) -> Span {
        match self {
            Self::Reference(n) | Self::Bind(n, _) => n.span,
            Self::Pattern(n, _) => n.span,
            Self::Type(n) => n.span,
            Self::Natural(n) => n.span,
            Self::Predicate(n) => n.left.span.cover(n.right.span),
            Self::Operation(n) => n.span,
            Self::Basis(n) => n.span,
            Self::Block(n) => n.span,
            Self::Expression(n) => n.span,
            Self::Enter | Self::EnterBasis | Self::Leave => origin,
        }
    }
    fn children<E>(
        &self,
        charge: &mut impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<usize, E> {
        Ok(match self {
            Self::Enter | Self::EnterBasis | Self::Leave | Self::Reference(_) | Self::Bind(..) => 0,
            Self::Pattern(p, _) => match &p.kind {
                PatternKind::Tuple(f) => f.len(),
                _ => 0,
            },
            Self::Type(t) => match &t.kind {
                TypeKind::Named(_) | TypeKind::Bits(_) | TypeKind::Q(_) => 1,
                TypeKind::Tuple(f) => f.len(),
                _ => 0,
            },
            Self::Natural(n) => match n.kind {
                NatKind::Add(..) | NatKind::Sub(..) | NatKind::Mul(..) => 2,
                _ => 0,
            },
            Self::Predicate(_) => 2,
            Self::Operation(n) => match &n.kind {
                StaticOpKind::Type(_)
                | StaticOpKind::Name(_)
                | StaticOpKind::Inverse(_)
                | StaticOpKind::Controlled(_)
                | StaticOpKind::Natural(_) => 1,
                StaticOpKind::Specialize { arguments, .. } => arguments.len().saturating_add(1),
                _ => 2,
            },
            Self::Basis(n) => match &n.kind {
                BasisExprKind::Name(_) | BasisExprKind::Not(_) => 1,
                BasisExprKind::Call { args, .. } => args.len().saturating_add(1),
                BasisExprKind::Tuple(f) => f.len(),
                BasisExprKind::Xor(..) | BasisExprKind::And(..) => 2,
                _ => 0,
            },
            Self::Block(b) => {
                let mut children = 2usize;
                for statement in &b.statements {
                    charge(statement.span, 1)?;
                    children = children.saturating_add(
                        if matches!(statement.kind, StmtKind::Let { .. }) {
                            2
                        } else {
                            1
                        },
                    );
                }
                children
            }
            Self::Expression(n) => match &n.kind {
                ExprKind::Name(_) | ExprKind::Not(_) => 1,
                ExprKind::Call {
                    args, static_args, ..
                } => args
                    .len()
                    .checked_add(static_args.len())
                    .and_then(|n| n.checked_add(1))
                    .unwrap_or(usize::MAX),
                ExprKind::Tuple(f) => f.len(),
                ExprKind::And(..)
                | ExprKind::Xor(..)
                | ExprKind::Adjoint { .. }
                | ExprKind::RepeatStatic { .. } => 2,
                ExprKind::If { .. }
                | ExprKind::StaticIf { .. }
                | ExprKind::ApplyContract { .. } => 3,
                ExprKind::StaticFold { .. } | ExprKind::CertifiedComputed { .. } => 8,
                ExprKind::CoherentLift { .. } => 5,
                ExprKind::WithComputed { .. } => 6,
                ExprKind::Controlled { args, .. } => args.len().saturating_add(1),
                ExprKind::QuantumIf { .. } => 4,
                ExprKind::Bit(_) | ExprKind::Unit => 0,
            },
        })
    }
}

impl<'ast, F, C, E> Builder<'ast, F, C>
where
    F: Fn(&str) -> Option<Target>,
    C: FnMut(Span, usize) -> Result<(), E>,
{
    fn scope(&self) -> ScopeId {
        self.frames.last().expect("root lexical scope").id
    }
    fn enter(&mut self) -> Result<(), E> {
        (self.charge)(self.origin, 2)?;
        let id = ScopeId {
            definition: self.index.table.definition,
            ordinal: self.index.table.scopes.len(),
        };
        self.index.table.scopes.push(Some(self.scope()));
        self.frames.push(Frame { id, undo: vec![] });
        Ok(())
    }
    fn enter_basis(&mut self) -> Result<(), E> {
        self.enter()?;
        // Coherent labels have a closed ordinary value environment. Preserve
        // static identities while hiding outer runtime and Basis-local names.
        // Move their keys into the existing undo frame instead of cloning maps.
        let mut outer = std::mem::take(&mut self.names);
        while !outer.is_empty() {
            (self.charge)(self.origin, 1)?;
            let (name, id) = outer.pop_first().expect("nonempty visible names");
            if matches!(
                self.index.table.binder(id).kind,
                BindingKind::Runtime | BindingKind::Basis
            ) {
                (self.charge)(self.origin, 2)?;
                self.frames
                    .last_mut()
                    .expect("entered Basis scope")
                    .undo
                    .push((name, Some(id)));
            } else {
                (self.charge)(self.origin, 1)?;
                self.names.insert(name, id);
            }
        }
        Ok(())
    }
    fn leave(&mut self) -> Result<(), E> {
        for (name, previous) in self
            .frames
            .pop()
            .expect("entered scope")
            .undo
            .into_iter()
            .rev()
        {
            (self.charge)(self.origin, 1)?;
            if let Some(id) = previous {
                if !self.names.contains_key(&name) {
                    (self.charge)(self.origin, 1)?;
                }
                self.names.insert(name, id);
            } else {
                self.names.remove(&name);
            }
        }
        Ok(())
    }
    fn bind(&mut self, name: &Ident, kind: BindingKind) -> Result<(), E> {
        (self.charge)(
            name.span,
            name.text
                .len()
                .checked_mul(3)
                .and_then(|n| n.checked_add(4))
                .unwrap_or(usize::MAX),
        )?;
        let id = BinderId {
            definition: self.index.table.definition,
            ordinal: self.index.table.binders.len(),
        };
        let previous = self.names.insert(name.text.clone(), id);
        if matches!(
            kind,
            BindingKind::StaticNatural | BindingKind::StaticBasis | BindingKind::StaticOperation
        ) {
            (self.charge)(name.span, name.text.len() + 1)?;
            self.static_parameters.insert(name.text.clone(), id);
        }
        self.index.table.binders.push(BinderInfo {
            key: BinderKey {
                name: name.text.clone(),
                id,
            },
            shadowed: previous,
            span: name.span,
            kind,
            scope: self.scope(),
        });
        self.index
            .bindings
            .insert(std::ptr::from_ref(name) as usize, id);
        self.frames
            .last_mut()
            .expect("root scope")
            .undo
            .push((name.text.clone(), previous));
        Ok(())
    }
    fn record_use(&mut self, name: &str, span: Span) -> Result<UseSiteId, E> {
        (self.charge)(span, name.len() + 1)?;
        let id = UseSiteId {
            definition: self.index.table.definition,
            ordinal: self.index.table.uses.len(),
        };
        let global = (self.global)(name);
        let target = self
            .names
            .get(name)
            .copied()
            .map(ResolvedUse::Local)
            .or_else(|| global.map(ResolvedUse::Global))
            .unwrap_or(ResolvedUse::Unresolved);
        self.index.table.uses.push(UseInfo {
            name: name.into(),
            span,
            scope: self.scope(),
            target,
            global,
            static_parameter: self.static_parameters.get(name).copied(),
        });
        Ok(id)
    }
    fn declaration(&mut self, declaration: &'ast Decl) -> Result<(), E> {
        (self.charge)(declaration.span, 1)?;
        // All static names precede their annotations, including forward sizes.
        for parameter in &declaration.static_params {
            self.bind(
                &parameter.name,
                match parameter.kind {
                    StaticParamKind::Natural => BindingKind::StaticNatural,
                    StaticParamKind::Basis => BindingKind::StaticBasis,
                    StaticParamKind::Operation { .. } => BindingKind::StaticOperation,
                },
            )?;
        }
        (self.charge)(declaration.span, 2)?;
        let mut tasks = vec![
            match &declaration.body {
                FnBody::Meaning { function, .. } => Task::Reference(function),
                FnBody::Basis(expression) => Task::Basis(expression),
                FnBody::Quantum(block) => Task::Block(block),
            },
            Task::Type(&declaration.return_type),
        ];
        let kind = if declaration.kind == FnKind::Basis {
            BindingKind::Basis
        } else {
            BindingKind::Runtime
        };
        for parameter in declaration.params.iter().rev() {
            (self.charge)(parameter.ty.span, 2)?;
            tasks.push(Task::Pattern(&parameter.pattern, kind));
            tasks.push(Task::Type(&parameter.ty));
        }
        for requirement in declaration.requires.iter().rev() {
            (self.charge)(declaration.span, 1)?;
            tasks.push(match requirement {
                Requirement::Access(access) => Task::Reference(&access.name),
                Requirement::Predicate(predicate) => Task::Predicate(predicate),
            });
        }
        for parameter in declaration.static_params.iter().rev() {
            if let StaticParamKind::Operation { basis, meaning } = &parameter.kind {
                if let Some(meaning) = meaning {
                    (self.charge)(meaning.span, 1)?;
                    tasks.push(Task::Reference(meaning));
                }
                (self.charge)(basis.span, 1)?;
                tasks.push(Task::Type(basis));
            }
        }
        // No recursive calls or whole-environment copies. Each source node and
        // scope undo entry is visited a bounded number of times, even for an
        // externally constructed AST that did not pass through the parser.
        while let Some(task) = tasks.pop() {
            let span = task.span(self.origin);
            (self.charge)(span, 1)?;
            let children = task.children(&mut self.charge)?;
            (self.charge)(span, children)?;
            match task {
                Task::Enter => self.enter()?,
                Task::EnterBasis => self.enter_basis()?,
                Task::Leave => self.leave()?,
                Task::Reference(name) => {
                    let id = self.record_use(&name.text, name.span)?;
                    (self.charge)(name.span, 1)?;
                    self.index
                        .references
                        .insert(std::ptr::from_ref(name) as usize, id);
                }
                Task::Bind(name, kind) => self.bind(name, kind)?,
                Task::Pattern(pattern, kind) => match &pattern.kind {
                    PatternKind::Name(name) => self.bind(name, kind)?,
                    PatternKind::Tuple(fields) => {
                        tasks.extend(fields.iter().rev().map(|p| Task::Pattern(p, kind)))
                    }
                    PatternKind::Wildcard => {}
                },
                Task::Type(ty) => match &ty.kind {
                    TypeKind::Named(name) => tasks.push(Task::Reference(name)),
                    TypeKind::Bits(n) => tasks.push(Task::Natural(n)),
                    TypeKind::Tuple(fields) => tasks.extend(fields.iter().rev().map(Task::Type)),
                    TypeKind::Q(inner) => tasks.push(Task::Type(inner)),
                    TypeKind::Unit | TypeKind::Bit => {}
                },
                Task::Natural(natural) => match &natural.kind {
                    NatKind::Name(name) => {
                        let id = self.record_use(name, natural.span)?;
                        (self.charge)(natural.span, 1)?;
                        self.index
                            .natural_references
                            .insert(std::ptr::from_ref(natural) as usize, id);
                    }
                    NatKind::Add(a, b) | NatKind::Sub(a, b) | NatKind::Mul(a, b) => {
                        tasks.extend([Task::Natural(b), Task::Natural(a)])
                    }
                    NatKind::Number(_) => {}
                },
                Task::Predicate(predicate) => tasks.extend([
                    Task::Natural(&predicate.right),
                    Task::Natural(&predicate.left),
                ]),
                Task::Operation(operation) => match &operation.kind {
                    StaticOpKind::Type(ty) => tasks.push(Task::Type(ty)),
                    StaticOpKind::Name(name) => tasks.push(Task::Reference(name)),
                    StaticOpKind::Bind {
                        implementation,
                        meaning,
                    } => tasks.extend([Task::Reference(meaning), Task::Reference(implementation)]),
                    StaticOpKind::Inverse(inner) | StaticOpKind::Controlled(inner) => {
                        tasks.push(Task::Operation(inner))
                    }
                    StaticOpKind::Then(a, b)
                    | StaticOpKind::Tensor(a, b)
                    | StaticOpKind::Conjugate(a, b) => {
                        tasks.extend([Task::Operation(b), Task::Operation(a)])
                    }
                    StaticOpKind::Repeat(count, inner) => {
                        let (Count::Natural(n) | Count::Power(n)) = count;
                        tasks.extend([Task::Operation(inner), Task::Natural(n)]);
                    }
                    StaticOpKind::Natural(n) => tasks.push(Task::Natural(n)),
                    StaticOpKind::Specialize { name, arguments } => {
                        tasks.extend(arguments.iter().rev().map(Task::Operation));
                        tasks.push(Task::Reference(name));
                    }
                },
                Task::Basis(expression) => match &expression.kind {
                    BasisExprKind::Name(name) => tasks.push(Task::Reference(name)),
                    BasisExprKind::Call { callee, args } => {
                        tasks.extend(args.iter().rev().map(Task::Basis));
                        tasks.push(Task::Reference(callee));
                    }
                    BasisExprKind::Tuple(fields) => {
                        tasks.extend(fields.iter().rev().map(Task::Basis))
                    }
                    BasisExprKind::Not(inner) => tasks.push(Task::Basis(inner)),
                    BasisExprKind::Xor(a, b) | BasisExprKind::And(a, b) => {
                        tasks.extend([Task::Basis(b), Task::Basis(a)])
                    }
                    BasisExprKind::Bit(_) | BasisExprKind::Unit => {}
                },
                Task::Block(block) => {
                    self.enter()?;
                    tasks.extend([Task::Leave, Task::Expression(&block.result)]);
                    for statement in block.statements.iter().rev() {
                        match &statement.kind {
                            StmtKind::Let { pattern, value } => tasks.extend([
                                Task::Pattern(pattern, BindingKind::Runtime),
                                Task::Expression(value),
                            ]),
                            StmtKind::Expr(expression) => tasks.push(Task::Expression(expression)),
                        }
                    }
                }
                Task::Expression(expression) => match &expression.kind {
                    ExprKind::Name(name) => tasks.push(Task::Reference(name)),
                    ExprKind::Call {
                        callee,
                        static_args,
                        args,
                    } => {
                        tasks.extend(args.iter().rev().map(Task::Expression));
                        tasks.extend(static_args.iter().rev().map(Task::Operation));
                        tasks.push(Task::Reference(callee));
                    }
                    ExprKind::Tuple(fields) => {
                        tasks.extend(fields.iter().rev().map(Task::Expression))
                    }
                    ExprKind::Not(inner) => tasks.push(Task::Expression(inner)),
                    ExprKind::And(a, b) | ExprKind::Xor(a, b) => {
                        tasks.extend([Task::Expression(b), Task::Expression(a)])
                    }
                    ExprKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => tasks.extend([
                        Task::Block(else_branch),
                        Task::Block(then_branch),
                        Task::Expression(condition),
                    ]),
                    ExprKind::StaticIf {
                        predicate,
                        then_branch,
                        else_branch,
                    } => tasks.extend([
                        Task::Block(else_branch),
                        Task::Block(then_branch),
                        Task::Predicate(predicate),
                    ]),
                    ExprKind::StaticFold {
                        index,
                        start,
                        end,
                        carry,
                        initial,
                        body,
                    } => tasks.extend([
                        Task::Leave,
                        Task::Block(body),
                        Task::Pattern(carry, BindingKind::Runtime),
                        Task::Bind(index, BindingKind::FoldIndex),
                        Task::Enter,
                        Task::Expression(initial),
                        Task::Natural(end),
                        Task::Natural(start),
                    ]),
                    ExprKind::CoherentLift {
                        binder,
                        input,
                        basis,
                    } => tasks.extend([
                        Task::Leave,
                        Task::Basis(basis),
                        Task::Pattern(binder, BindingKind::Basis),
                        Task::EnterBasis,
                        Task::Expression(input),
                    ]),
                    ExprKind::WithComputed {
                        source,
                        function,
                        binder,
                        body,
                    } => tasks.extend([
                        Task::Leave,
                        Task::Block(body),
                        Task::Bind(binder, BindingKind::Runtime),
                        Task::Enter,
                        Task::Reference(function),
                        Task::Expression(source),
                    ]),
                    ExprKind::CertifiedComputed {
                        source,
                        function,
                        logical,
                        data_binder,
                        ancilla_binder,
                        body,
                    } => tasks.extend([
                        Task::Leave,
                        Task::Block(body),
                        Task::Bind(ancilla_binder, BindingKind::Runtime),
                        Task::Bind(data_binder, BindingKind::Runtime),
                        Task::Enter,
                        Task::Reference(logical),
                        Task::Reference(function),
                        Task::Expression(source),
                    ]),
                    ExprKind::ApplyContract {
                        implementation,
                        specification,
                        input,
                    } => tasks.extend([
                        Task::Expression(input),
                        Task::Reference(specification),
                        Task::Reference(implementation),
                    ]),
                    ExprKind::Adjoint { operation, input } => {
                        tasks.extend([Task::Expression(input), Task::Operation(operation)])
                    }
                    ExprKind::Controlled { operation, args } => {
                        tasks.extend(args.iter().rev().map(Task::Expression));
                        tasks.push(Task::Operation(operation));
                    }
                    ExprKind::RepeatStatic {
                        function, input, ..
                    } => tasks.extend([Task::Expression(input), Task::Reference(function)]),
                    ExprKind::QuantumIf {
                        control,
                        target,
                        zero,
                        one,
                    } => tasks.extend([
                        Task::Reference(one),
                        Task::Reference(zero),
                        Task::Expression(target),
                        Task::Expression(control),
                    ]),
                    ExprKind::Bit(_) | ExprKind::Unit => {}
                },
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::parser::parse_module;

    fn index<'ast>(
        definition: DefId,
        declaration: &'ast Decl,
        global: impl Fn(&str) -> Option<Target>,
    ) -> Index<'ast> {
        Index::new_budgeted(definition, declaration, global, |_, _| {
            Ok::<_, std::convert::Infallible>(())
        })
        .unwrap_or_else(|never| match never {})
    }

    fn name(pattern: &Pattern) -> &Ident {
        let PatternKind::Name(name) = &pattern.kind else {
            panic!("name pattern")
        };
        name
    }
    fn expression_name(expression: &Expr) -> &Ident {
        let ExprKind::Name(name) = &expression.kind else {
            panic!("name expression")
        };
        name
    }

    #[test]
    fn equal_spans_do_not_merge_initializer_and_rebinding_identities() {
        let mut module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{let q=q;q}").unwrap();
        let decl = &mut module.decls[0];
        let PatternKind::Name(parameter) = &mut decl.params[0].pattern.kind else {
            panic!()
        };
        parameter.span = Span::default();
        let FnBody::Quantum(body) = &mut decl.body else {
            panic!()
        };
        let StmtKind::Let { pattern, value } = &mut body.statements[0].kind else {
            panic!()
        };
        let PatternKind::Name(binder) = &mut pattern.kind else {
            panic!()
        };
        binder.span = Span::default();
        let ExprKind::Name(initializer) = &mut value.kind else {
            panic!()
        };
        initializer.span = Span::default();
        let ExprKind::Name(result) = &mut body.result.kind else {
            panic!()
        };
        result.span = Span::default();
        let index = index(DefId(0), decl, |_| None);
        let FnBody::Quantum(body) = &decl.body else {
            panic!()
        };
        let StmtKind::Let { pattern, value } = &body.statements[0].kind else {
            panic!()
        };
        let original = index.binder(name(&decl.params[0].pattern));
        let rebound = index.binder(name(pattern));
        assert_ne!(original, rebound);
        assert_eq!(index.table.binder(rebound).shadowed, Some(original));
        assert_eq!(
            index.resolve(expression_name(value)),
            ResolvedUse::Local(original)
        );
        assert_eq!(
            index.resolve(expression_name(&body.result)),
            ResolvedUse::Local(rebound)
        );
    }

    #[test]
    fn cloned_and_relocated_syntax_keeps_structural_ids_but_rebuilds_lookup() {
        let original =
            parse_module("use std::quantum::h;unitary fn f(q:Q<Bit>)->Q<Bit>{let q=h(q);q}")
                .unwrap();
        let cloned = original.clone();
        let target = Target::Declaration(DefId(9));
        let a = index(DefId(0), &original.decls[0], |n| {
            (n == "h").then_some(target)
        });
        let b = index(DefId(0), &cloned.decls[0], |n| (n == "h").then_some(target));
        assert_eq!(a.table, b.table);
        assert!(
            a.references
                .keys()
                .all(|key| !b.references.contains_key(key))
        );
        let owned = b.table.clone();
        drop(b);
        drop(cloned);
        assert_eq!(a.table, owned);
        let other = index(DefId(1), &original.decls[0], |_| None);
        assert_ne!(
            a.binder(name(&original.decls[0].params[0].pattern)),
            other.binder(name(&original.decls[0].params[0].pattern))
        );
    }

    #[test]
    fn later_static_naturals_and_global_candidates_keep_the_same_local_identity() {
        let module = parse_module("unitary fn f[static U:Op<Bits<n>>,static n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires Apply(U){U(q)}").unwrap();
        let decl = &module.decls[0];
        let unresolved = index(DefId(0), decl, |_| None);
        let resolved = index(DefId(0), decl, |_| Some(Target::Declaration(DefId(3))));
        let StaticParamKind::Operation { basis, .. } = &decl.static_params[0].kind else {
            panic!()
        };
        let TypeKind::Bits(natural) = &basis.kind else {
            panic!()
        };
        let parameter = unresolved.binder(&decl.static_params[1].name);
        let site = unresolved.natural_usage(natural);
        assert_eq!(
            unresolved.table.usage(site).target,
            ResolvedUse::Local(parameter)
        );
        assert_eq!(resolved.binder(&decl.static_params[1].name), parameter);
        assert_eq!(resolved.natural_usage(natural), site);
        assert_eq!(
            resolved.table.usage(site).target,
            ResolvedUse::Local(parameter)
        );
    }

    #[test]
    fn static_candidate_does_not_replace_the_runtime_shadow_identity() {
        let module = parse_module(
            "unitary fn f[static U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Apply(U){let U=q;U(q)}",
        )
        .unwrap();
        let declaration = &module.decls[0];
        let index = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!()
        };
        let StmtKind::Let { pattern, .. } = &body.statements[0].kind else {
            panic!()
        };
        let ExprKind::Call { callee, .. } = &body.result.kind else {
            panic!()
        };
        let usage = index.table.usage(index.usage(callee));
        assert_eq!(
            usage.target,
            ResolvedUse::Local(index.binder(name(pattern)))
        );
        assert_eq!(
            usage.static_parameter,
            Some(index.binder(&declaration.static_params[0].name))
        );
        assert_ne!(
            usage.target,
            ResolvedUse::Local(usage.static_parameter.unwrap())
        );
    }

    #[test]
    fn constructed_deep_syntax_and_sibling_scopes_do_not_alias_bindings() {
        let mut module =
            parse_module("unitary fn f(x:Bit)->Bit{let y=if 1 {let x=x;x}else{let x=x;x};x}")
                .unwrap();
        let decl = &mut module.decls[0];
        let FnBody::Quantum(body) = &mut decl.body else {
            panic!()
        };
        // A modest manually constructed depth beyond the parser boundary:
        // indexing does not recursively traverse or recursively clone syntax.
        for _ in 0..96 {
            let old = std::mem::replace(
                &mut body.result,
                Box::new(Expr {
                    kind: ExprKind::Unit,
                    span: Span::default(),
                }),
            );
            *body.result = Expr {
                kind: ExprKind::Not(old),
                span: Span::default(),
            };
        }
        let index = index(DefId(0), decl, |_| None);
        let original = index.binder(name(&decl.params[0].pattern));
        let targets: Vec<_> = index
            .table
            .uses
            .iter()
            .filter(|usage| usage.name == "x")
            .map(|usage| usage.target)
            .collect();
        assert_eq!(targets.len(), 5);
        assert_eq!(targets[0], ResolvedUse::Local(original));
        assert_eq!(targets[2], ResolvedUse::Local(original));
        assert_eq!(targets[4], ResolvedUse::Local(original));
        assert_ne!(targets[1], targets[3]);
        assert_ne!(targets[1], ResolvedUse::Local(original));
    }
}
