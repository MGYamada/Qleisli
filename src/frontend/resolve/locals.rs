//! Lexical identities from the one source AST; not ownership or type evidence.
//!
//! IDs are assigned in structural traversal order, independently of source
//! spans and allocation addresses. An Index borrows one immovable declaration:
//! its address map only locates AST occurrences during that borrow. Projections
//! retain the numeric IDs and Table. The finite adapter can move the original
//! borrowed occurrences after common checking; it cannot reconstruct a pointer
//! from an address. Dynamic binding/owner IDs remain separate: one source binder
//! can execute many times in a fold or call.

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
impl BinderId {
    pub fn definition(self) -> DefId {
        self.definition
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct UseSiteId {
    definition: DefId,
    ordinal: usize,
}
impl UseSiteId {
    pub fn definition(self) -> DefId {
        self.definition
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct ScopeId {
    definition: DefId,
    ordinal: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) enum NodeKind {
    Expr,
    StaticOp,
    Natural,
    Type,
    Block,
    BasisExpr,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::frontend) struct NodeId {
    definition: DefId,
    ordinal: usize,
    kind: NodeKind,
}
impl NodeId {
    pub fn definition(self) -> DefId {
        self.definition
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct NodeInfo {
    pub span: Span,
    pub kind: NodeKind,
}

/// Borrowed syntax for original plan association. References stay in the Index
/// through common validation, then can move with its occurrences while the same
/// original Project AST is borrowed. They are not semantic evidence or part of
/// the immutable checked program.
#[derive(Clone, Copy)]
pub(in crate::frontend) enum OriginalNode<'ast> {
    Expression(&'ast Expr),
    Operation(&'ast StaticOp),
    Natural(&'ast Natural),
    Type(&'ast Type),
    Block(&'ast Block),
    Basis(&'ast BasisExpr),
}
impl OriginalNode<'_> {
    fn address(self) -> usize {
        match self {
            Self::Expression(n) => std::ptr::from_ref(n) as usize,
            Self::Operation(n) => std::ptr::from_ref(n) as usize,
            Self::Natural(n) => std::ptr::from_ref(n) as usize,
            Self::Type(n) => std::ptr::from_ref(n) as usize,
            Self::Block(n) => std::ptr::from_ref(n) as usize,
            Self::Basis(n) => std::ptr::from_ref(n) as usize,
        }
    }
    pub fn kind(self) -> NodeKind {
        match self {
            Self::Expression(_) => NodeKind::Expr,
            Self::Operation(_) => NodeKind::StaticOp,
            Self::Natural(_) => NodeKind::Natural,
            Self::Type(_) => NodeKind::Type,
            Self::Block(_) => NodeKind::Block,
            Self::Basis(_) => NodeKind::BasisExpr,
        }
    }
    pub fn span(self) -> Span {
        match self {
            Self::Expression(n) => n.span,
            Self::Operation(n) => n.span,
            Self::Natural(n) => n.span,
            Self::Type(n) => n.span,
            Self::Block(n) => n.span,
            Self::Basis(n) => n.span,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::frontend) enum OriginalRegion {
    Predicate { node: NodeId, truth: bool },
    Fold { node: NodeId },
}
struct RegionLink {
    region: OriginalRegion,
    parent: Option<usize>,
}
/// A borrowed inner-to-outer chain from the original structural walk. No
/// captured plan supplies its links or controls which ancestors are visited.
pub(in crate::frontend) struct OriginalRegions<'a> {
    links: &'a [RegionLink],
    next: Option<usize>,
}
impl Iterator for OriginalRegions<'_> {
    type Item = Result<OriginalRegion, ()>;
    fn next(&mut self) -> Option<Self::Item> {
        let ordinal = self.next.take()?;
        let Some(link) = self.links.get(ordinal) else {
            return Some(Err(()));
        };
        // Parents are earlier arena entries. Refuse malformed private metadata
        // rather than silently truncate the chain or permit a cyclic walk.
        if link.parent.is_some_and(|parent| parent >= ordinal) {
            return Some(Err(()));
        }
        self.next = link.parent;
        Some(Ok(link.region))
    }
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

/// A private association between one original Index and its retained Table.
/// Value equality deliberately preserves structural Table equality; only the
/// borrowed reverse lookup compares Arc identity. This is neither cryptographic
/// authentication nor semantic evidence, and never determines numeric IDs.
#[derive(Debug, PartialEq, Eq)]
struct OriginalAssociation;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::frontend) struct Table {
    definition: DefId,
    binders: Vec<BinderInfo>,
    uses: Vec<UseInfo>,
    scopes: Vec<Option<ScopeId>>,
    nodes: Vec<NodeInfo>,
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "original syntax association for the dormant adapter"
        )
    )]
    association: Arc<OriginalAssociation>,
}
impl Table {
    /// Original resolved occurrences, including references in inactive branches.
    /// Callers must bound traversal; diagnostic candidates are not resolution.
    pub(in crate::frontend) fn resolved_uses(&self) -> &[UseInfo] {
        &self.uses
    }

    /// Fallible lookup for retained metadata, including IDs from another index.
    pub fn try_binder(&self, id: BinderId) -> Option<&BinderInfo> {
        if id.definition != self.definition {
            return None;
        }
        self.binders.get(id.ordinal)
    }

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
    /// Fallible lookup for retained metadata, including IDs from another index.
    pub fn try_usage(&self, id: UseSiteId) -> Option<&UseInfo> {
        if id.definition != self.definition {
            return None;
        }
        self.uses.get(id.ordinal)
    }

    pub fn usage(&self, id: UseSiteId) -> &UseInfo {
        assert_eq!(
            id.definition, self.definition,
            "use belongs to another declaration"
        );
        &self.uses[id.ordinal]
    }
    pub fn node(&self, id: NodeId) -> &NodeInfo {
        assert_eq!(
            id.definition, self.definition,
            "node belongs to another declaration"
        );
        let node = &self.nodes[id.ordinal];
        assert_eq!(id.kind, node.kind, "node has another syntax kind");
        node
    }
    pub fn try_node(&self, id: NodeId) -> Option<&NodeInfo> {
        if id.definition != self.definition {
            return None;
        }
        let node = self.nodes.get(id.ordinal)?;
        (id.kind == node.kind).then_some(node)
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
    nodes: BTreeMap<(NodeKind, usize), NodeId>,
    originals: Vec<OriginalNode<'ast>>,
    original_association: Option<Arc<OriginalAssociation>>,
    region_heads: Vec<Option<usize>>,
    region_links: Vec<RegionLink>,
    _syntax: PhantomData<&'ast Decl>,
}
impl<'ast> Index<'ast> {
    pub fn new_budgeted<E>(
        definition: DefId,
        declaration: &'ast Decl,
        global: impl Fn(&str) -> Option<Target>,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Self, E> {
        // Root scope/frame storage, token heap and both retained token handles
        // are charged before allocation. The move-side handle is not cloned at
        // occurrence transfer; the checked Table keeps the other handle.
        charge(declaration.span, 5)?;
        let association = Arc::new(OriginalAssociation);
        let mut builder = Builder {
            index: Self {
                table: Table {
                    definition,
                    binders: vec![],
                    uses: vec![],
                    scopes: vec![None],
                    nodes: vec![],
                    association: Arc::clone(&association),
                },
                bindings: BTreeMap::new(),
                references: BTreeMap::new(),
                natural_references: BTreeMap::new(),
                nodes: BTreeMap::new(),
                originals: Vec::new(),
                original_association: Some(association),
                region_heads: Vec::new(),
                region_links: Vec::new(),
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
            region: None,
        };
        builder.declaration(declaration)?;
        Ok(builder.index)
    }
    /// Transfer occurrence lookups after source checking has finished using
    /// this Index. The authoritative Table remains with the source judgment.
    pub fn take_occurrences(&mut self) -> Occurrences<'ast> {
        Occurrences {
            definition: self.table.definition,
            association: self.original_association.take(),
            originals: std::mem::take(&mut self.originals),
            bindings: std::mem::take(&mut self.bindings),
            references: std::mem::take(&mut self.references),
            natural_references: std::mem::take(&mut self.natural_references),
            nodes: std::mem::take(&mut self.nodes),
            _syntax: PhantomData,
        }
    }
    /// Fallible association for retained plans, before occurrence transfer.
    /// Numeric IDs from a different owner/kind/ordinal are never indexed.
    pub fn original_node(&self, id: NodeId) -> Option<OriginalNode<'ast>> {
        let info = self.table.try_node(id)?;
        let original = *self.originals.get(id.ordinal)?;
        (id.kind == info.kind && original.kind() == id.kind).then_some(original)
    }
    pub fn original_nodes(&self) -> &[OriginalNode<'ast>] {
        &self.originals
    }
    pub fn enclosing_regions(&self, node: NodeId) -> Option<OriginalRegions<'_>> {
        self.original_node(node)?;
        Some(OriginalRegions {
            links: &self.region_links,
            next: *self.region_heads.get(node.ordinal)?,
        })
    }
    pub fn binder(&self, name: &Ident) -> BinderId {
        self.bindings[&(std::ptr::from_ref(name) as usize)]
    }
    /// Fallible original occurrence lookup; callers charge their lookup work.
    pub fn try_binder(&self, name: &Ident) -> Option<BinderId> {
        let id = *self.bindings.get(&(std::ptr::from_ref(name) as usize))?;
        self.table.try_binder(id)?;
        Some(id)
    }
    pub fn usage(&self, name: &Ident) -> UseSiteId {
        self.references[&(std::ptr::from_ref(name) as usize)]
    }
    /// Fallible original occurrence lookup; callers charge their lookup work.
    /// Foreign or transferred syntax has no address entry in this Index.
    pub fn try_usage(&self, name: &Ident) -> Option<UseSiteId> {
        let id = *self.references.get(&(std::ptr::from_ref(name) as usize))?;
        self.table.try_usage(id)?;
        Some(id)
    }
    #[cfg(test)]
    pub fn reference_site(&self, name: &Ident) -> UseSiteId {
        self.usage(name)
    }
    pub fn natural_usage(&self, natural: &Natural) -> UseSiteId {
        self.natural_references[&(std::ptr::from_ref(natural) as usize)]
    }
    /// Fallible original occurrence lookup; callers charge their lookup work.
    pub fn try_natural_usage(&self, natural: &Natural) -> Option<UseSiteId> {
        let id = *self
            .natural_references
            .get(&(std::ptr::from_ref(natural) as usize))?;
        self.table.try_usage(id)?;
        Some(id)
    }
    #[cfg(test)]
    pub fn natural_site(&self, natural: &Natural) -> UseSiteId {
        self.natural_usage(natural)
    }
    fn node_id(&self, kind: NodeKind, address: usize) -> NodeId {
        let id = self.nodes[&(kind, address)];
        self.table.node(id);
        id
    }
    fn try_node_id(&self, kind: NodeKind, address: usize) -> Option<NodeId> {
        let id = *self.nodes.get(&(kind, address))?;
        if id.kind != kind {
            return None;
        }
        self.table.try_node(id)?;
        Some(id)
    }
    pub fn node_id_expr(&self, node: &Expr) -> NodeId {
        self.node_id(NodeKind::Expr, std::ptr::from_ref(node) as usize)
    }
    pub fn node_id_static_op(&self, node: &StaticOp) -> NodeId {
        self.node_id(NodeKind::StaticOp, std::ptr::from_ref(node) as usize)
    }
    pub fn node_id_natural(&self, node: &Natural) -> NodeId {
        self.node_id(NodeKind::Natural, std::ptr::from_ref(node) as usize)
    }
    /// Fallible original occurrence lookup; callers charge their lookup work.
    pub fn try_node_id_natural(&self, node: &Natural) -> Option<NodeId> {
        self.try_node_id(NodeKind::Natural, std::ptr::from_ref(node) as usize)
    }
    pub fn node_id_ty(&self, node: &Type) -> NodeId {
        self.node_id(NodeKind::Type, std::ptr::from_ref(node) as usize)
    }
    /// Fallible original occurrence lookup; callers charge their lookup work.
    pub fn try_node_id_ty(&self, node: &Type) -> Option<NodeId> {
        self.try_node_id(NodeKind::Type, std::ptr::from_ref(node) as usize)
    }
    #[cfg(test)]
    pub fn node_id_block(&self, node: &Block) -> NodeId {
        self.node_id(NodeKind::Block, std::ptr::from_ref(node) as usize)
    }
    #[cfg(test)]
    pub fn node_id_basis_expr(&self, node: &BasisExpr) -> NodeId {
        self.node_id(NodeKind::BasisExpr, std::ptr::from_ref(node) as usize)
    }
    #[cfg(test)]
    pub fn resolve(&self, name: &Ident) -> ResolvedUse {
        self.table.usage(self.usage(name)).target
    }
}

/// Original borrowed occurrences move independently of the authoritative
/// lexical Table, retaining their private association with that judgment.
pub(in crate::frontend) struct Occurrences<'ast> {
    definition: DefId,
    association: Option<Arc<OriginalAssociation>>,
    originals: Vec<OriginalNode<'ast>>,
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    natural_references: BTreeMap<usize, UseSiteId>,
    nodes: BTreeMap<(NodeKind, usize), NodeId>,
    _syntax: PhantomData<&'ast Decl>,
}

struct OriginalDeclaration<'ast> {
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "retained original association for the dormant adapter"
        )
    )]
    association: Option<Arc<OriginalAssociation>>,
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "retained original syntax for the dormant adapter")
    )]
    originals: Vec<OriginalNode<'ast>>,
    ambiguous: bool,
}

#[derive(Default)]
pub(in crate::frontend) struct OccurrencesForest<'ast> {
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    natural_references: BTreeMap<usize, UseSiteId>,
    nodes: BTreeMap<(NodeKind, usize), NodeId>,
    originals: BTreeMap<DefId, OriginalDeclaration<'ast>>,
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
        let moved_cells = occurrences
            .bindings
            .len()
            .checked_add(occurrences.references.len())
            .and_then(|n| n.checked_add(occurrences.natural_references.len()))
            .and_then(|n| n.checked_add(occurrences.nodes.len()))
            .and_then(|n| n.checked_mul(2))
            .unwrap_or(usize::MAX);
        // Each original visit and forward association check, then the owner
        // lookup/map cell and retained Vec/token headers. The existing Vec and
        // its AST borrows move intact; no second node vector is allocated.
        let original_cells = occurrences
            .originals
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(4))
            .unwrap_or(usize::MAX);
        let cells = moved_cells.saturating_add(original_cells);
        charge(span, cells)?;
        let mut ambiguous = occurrences.association.is_none()
            || occurrences.originals.len() != occurrences.nodes.len();
        for (ordinal, original) in occurrences.originals.iter().enumerate() {
            let id = NodeId {
                definition: occurrences.definition,
                ordinal,
                kind: original.kind(),
            };
            if occurrences.nodes.get(&(id.kind, original.address())) != Some(&id) {
                ambiguous = true;
            }
        }
        match self.originals.entry(occurrences.definition) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(OriginalDeclaration {
                    association: occurrences.association,
                    originals: occurrences.originals,
                    ambiguous,
                });
            }
            std::collections::btree_map::Entry::Occupied(mut entry) => {
                // Preserve the first association, but neither original can be
                // selected after an ambiguous duplicate owner was supplied.
                entry.get_mut().ambiguous = true;
            }
        }
        for (address, id) in occurrences.bindings {
            self.bindings.insert(address, id);
        }
        for (address, id) in occurrences.references {
            self.references.insert(address, id);
        }
        for (address, id) in occurrences.natural_references {
            self.natural_references.insert(address, id);
        }
        for (address, id) in occurrences.nodes {
            self.nodes.insert(address, id);
        }
        Ok(())
    }
}

/// Source-address lookup remains tied to the original borrowed syntax. Checked
/// lexical Tables stay with their original whole-program judgment.
#[derive(Default)]
pub(in crate::frontend) struct Forest<'ast> {
    bindings: BTreeMap<usize, BinderId>,
    references: BTreeMap<usize, UseSiteId>,
    // MSRV and current rustc differ on whether reads from unused adapter
    // methods satisfy dead-code checking of these fields and shared helpers.
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "retained for the next original-plan adapter")
    )]
    natural_references: BTreeMap<usize, UseSiteId>,
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "retained for the next original-plan adapter")
    )]
    nodes: BTreeMap<(NodeKind, usize), NodeId>,
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "original syntax borrows for the dormant adapter")
    )]
    originals: BTreeMap<DefId, OriginalDeclaration<'ast>>,
    _syntax: PhantomData<&'ast Decl>,
}
impl<'ast> Forest<'ast> {
    pub fn from_occurrences(occurrences: OccurrencesForest<'ast>) -> Self {
        Self {
            bindings: occurrences.bindings,
            references: occurrences.references,
            natural_references: occurrences.natural_references,
            nodes: occurrences.nodes,
            originals: occurrences.originals,
            _syntax: PhantomData,
        }
    }
    pub fn lookup<'view>(
        &'view self,
        tables: &'view BTreeMap<DefId, Arc<Table>>,
    ) -> Lookup<'view, 'ast> {
        Lookup {
            occurrences: self,
            tables,
        }
    }
}

/// A temporary view borrows the original checked Tables without copying their
/// map or Arc handles. Returned records borrow those Tables, not this view.
pub(in crate::frontend) struct Lookup<'view, 'ast> {
    occurrences: &'view Forest<'ast>,
    tables: &'view BTreeMap<DefId, Arc<Table>>,
}
impl<'view, 'ast> Lookup<'view, 'ast> {
    /// Borrow the actual original node after checking its judgment association.
    /// Every lookup/comparison is charged first. Addresses are obtained only
    /// from safe references and compared to the original forward map; they are
    /// never converted back into pointers or used as semantic evidence.
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "original syntax borrow for the dormant adapter")
    )]
    pub fn original_node_budgeted<E>(
        &self,
        id: NodeId,
        mut charge: impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<Option<OriginalNode<'ast>>, E> {
        charge(Span::default(), 1)?;
        let Some(table) = self.tables.get(&id.definition) else {
            return Ok(None);
        };
        charge(Span::default(), 1)?;
        let Some(info) = table.try_node(id) else {
            return Ok(None);
        };
        charge(info.span, 1)?;
        let Some(declaration) = self.occurrences.originals.get(&id.definition) else {
            return Ok(None);
        };
        charge(info.span, 1)?;
        let Some(association) = &declaration.association else {
            return Ok(None);
        };
        if declaration.ambiguous || !Arc::ptr_eq(association, &table.association) {
            return Ok(None);
        }
        charge(info.span, 1)?;
        let Some(original) = declaration.originals.get(id.ordinal).copied() else {
            return Ok(None);
        };
        charge(info.span, 1)?;
        if original.kind() != id.kind || original.span() != info.span {
            return Ok(None);
        }
        charge(info.span, 1)?;
        if self.occurrences.nodes.get(&(id.kind, original.address())) != Some(&id) {
            return Ok(None);
        }
        Ok(Some(original))
    }
    pub fn binder(&self, name: &Ident) -> BinderId {
        self.occurrences.bindings[&(std::ptr::from_ref(name) as usize)]
    }
    pub fn info(&self, id: BinderId) -> &'view BinderInfo {
        self.tables[&id.definition].binder(id)
    }
    pub fn key(&self, id: BinderId) -> &'view BinderKey {
        self.tables[&id.definition].key(id)
    }
    pub fn usage(&self, name: &Ident) -> &'view UseInfo {
        let id = self.reference_site(name);
        self.tables[&id.definition].usage(id)
    }
    pub fn reference_site(&self, name: &Ident) -> UseSiteId {
        self.occurrences.references[&(std::ptr::from_ref(name) as usize)]
    }
    /// Fallible original occurrence lookup; callers charge the bounded lookups.
    pub fn try_reference_site(&self, name: &Ident) -> Option<UseSiteId> {
        let id = *self
            .occurrences
            .references
            .get(&(std::ptr::from_ref(name) as usize))?;
        let table = self.associated_table(id.definition)?;
        table.try_usage(id)?;
        Some(id)
    }
    fn associated_table(&self, definition: DefId) -> Option<&'view Table> {
        let table = self.tables.get(&definition)?;
        let declaration = self.occurrences.originals.get(&definition)?;
        let association = declaration.association.as_ref()?;
        if declaration.ambiguous || !Arc::ptr_eq(association, &table.association) {
            return None;
        }
        Some(table)
    }
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "original natural lookup for the next plan adapter"
        )
    )]
    pub fn natural_usage(&self, natural: &Natural) -> &'view UseInfo {
        let id = self.natural_site(natural);
        self.tables[&id.definition].usage(id)
    }
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "original natural lookup for the next plan adapter"
        )
    )]
    pub fn natural_site(&self, natural: &Natural) -> UseSiteId {
        self.occurrences.natural_references[&(std::ptr::from_ref(natural) as usize)]
    }
    #[cfg_attr(
        not(test),
        allow(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    fn node_id(&self, kind: NodeKind, address: usize) -> NodeId {
        let id = self.occurrences.nodes[&(kind, address)];
        self.tables[&id.definition].node(id);
        id
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_expr(&self, node: &Expr) -> NodeId {
        self.node_id(NodeKind::Expr, std::ptr::from_ref(node) as usize)
    }
    /// Foreign same-shaped syntax has no original address association.
    pub fn try_node_id_expr(&self, node: &Expr) -> Option<NodeId> {
        let id = *self
            .occurrences
            .nodes
            .get(&(NodeKind::Expr, std::ptr::from_ref(node) as usize))?;
        if id.kind != NodeKind::Expr {
            return None;
        }
        self.associated_table(id.definition)?.try_node(id)?;
        Some(id)
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_static_op(&self, node: &StaticOp) -> NodeId {
        self.node_id(NodeKind::StaticOp, std::ptr::from_ref(node) as usize)
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_natural(&self, node: &Natural) -> NodeId {
        self.node_id(NodeKind::Natural, std::ptr::from_ref(node) as usize)
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_ty(&self, node: &Type) -> NodeId {
        self.node_id(NodeKind::Type, std::ptr::from_ref(node) as usize)
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_block(&self, node: &Block) -> NodeId {
        self.node_id(NodeKind::Block, std::ptr::from_ref(node) as usize)
    }
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "original node lookup for the next plan adapter")
    )]
    pub fn node_id_basis_expr(&self, node: &BasisExpr) -> NodeId {
        self.node_id(NodeKind::BasisExpr, std::ptr::from_ref(node) as usize)
    }
    pub fn local_key(&self, name: &Ident) -> Option<&'view BinderKey> {
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
    region: Option<usize>,
}
enum Task<'a> {
    Enter,
    EnterBasis,
    Leave,
    Region(&'a Expr, Option<bool>),
    LeaveRegion,
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
impl<'ast> Task<'ast> {
    fn original(&self) -> Option<OriginalNode<'ast>> {
        Some(match self {
            Self::Expression(node) => OriginalNode::Expression(node),
            Self::Operation(node) => OriginalNode::Operation(node),
            Self::Natural(node) => OriginalNode::Natural(node),
            Self::Type(node) => OriginalNode::Type(node),
            Self::Block(node) => OriginalNode::Block(node),
            Self::Basis(node) => OriginalNode::Basis(node),
            _ => return None,
        })
    }
    fn node(&self) -> Option<(NodeKind, usize)> {
        Some(match self {
            Self::Expression(node) => (NodeKind::Expr, std::ptr::from_ref(*node) as usize),
            Self::Operation(node) => (NodeKind::StaticOp, std::ptr::from_ref(*node) as usize),
            Self::Natural(node) => (NodeKind::Natural, std::ptr::from_ref(*node) as usize),
            Self::Type(node) => (NodeKind::Type, std::ptr::from_ref(*node) as usize),
            Self::Block(node) => (NodeKind::Block, std::ptr::from_ref(*node) as usize),
            Self::Basis(node) => (NodeKind::BasisExpr, std::ptr::from_ref(*node) as usize),
            Self::Enter
            | Self::EnterBasis
            | Self::Leave
            | Self::Region(..)
            | Self::LeaveRegion
            | Self::Reference(_)
            | Self::Bind(..)
            | Self::Pattern(..)
            | Self::Predicate(_) => return None,
        })
    }
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
            Self::Region(n, _) => n.span,
            Self::Enter | Self::EnterBasis | Self::Leave | Self::LeaveRegion => origin,
        }
    }
    fn children<E>(
        &self,
        charge: &mut impl FnMut(Span, usize) -> Result<(), E>,
    ) -> Result<usize, E> {
        Ok(match self {
            Self::Enter
            | Self::EnterBasis
            | Self::Leave
            | Self::Region(..)
            | Self::LeaveRegion
            | Self::Reference(_)
            | Self::Bind(..) => 0,
            Self::Pattern(p, _) => match &p.kind {
                PatternKind::Tuple(f) => f.len(),
                _ => 0,
            },
            Self::Type(t) => match &t.kind {
                TypeKind::Named(_) | TypeKind::Bits(_) | TypeKind::Q(_) => 1,
                TypeKind::Tuple(f) => f.len(),
                _ => 0,
            },
            Self::Natural(n) => match &n.kind {
                NatKind::Call { arguments, .. } => arguments.len() + 1,
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
                        if matches!(
                            statement.kind,
                            StmtKind::Let { .. }
                                | StmtKind::MutableLet { .. }
                                | StmtKind::Assign { .. }
                                | StmtKind::StaticLet { .. }
                        ) {
                            2
                        } else {
                            1
                        },
                    );
                }
                children
            }
            Self::Expression(n) => match &n.kind {
                ExprKind::UnsupportedClosure(closure) => closure.parameters.len().saturating_add(3),
                ExprKind::Name(_) | ExprKind::Not(_) => 1,
                ExprKind::Call {
                    args, static_args, ..
                } => args
                    .len()
                    .checked_add(static_args.len())
                    .and_then(|n| n.checked_add(1))
                    .unwrap_or(usize::MAX),
                ExprKind::AccessCall {
                    args, static_args, ..
                } => args
                    .len()
                    .saturating_add(static_args.len())
                    .saturating_add(
                        args.iter()
                            .map(|arg| {
                                arg.selection
                                    .as_ref()
                                    .map_or(0, |selection| selection.naturals().count())
                            })
                            .sum::<usize>(),
                    )
                    .saturating_add(1),
                ExprKind::Tuple(f) => f.len(),
                ExprKind::And(..)
                | ExprKind::Xor(..)
                | ExprKind::ApplyStatic { .. }
                | ExprKind::Adjoint { .. }
                | ExprKind::RepeatStatic { .. } => 2,
                ExprKind::If { .. } | ExprKind::ApplyContract { .. } => 3,
                ExprKind::StaticIf { .. } => 7,
                ExprKind::StaticFold { .. } => 10,
                ExprKind::CertifiedComputed { .. } => 8,
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
    fn enter_region(&mut self, expression: &'ast Expr, truth: Option<bool>) -> Result<(), E> {
        (self.charge)(expression.span, 1)?;
        let node = self.index.node_id_expr(expression);
        let region = match truth {
            Some(truth) => OriginalRegion::Predicate { node, truth },
            None => OriginalRegion::Fold { node },
        };
        let next = self.index.region_links.len();
        self.index.region_links.push(RegionLink {
            region,
            parent: self.region,
        });
        self.region = Some(next);
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
    fn record_node(
        &mut self,
        kind: NodeKind,
        address: usize,
        original: OriginalNode<'ast>,
        span: Span,
    ) -> Result<(), E> {
        // Metadata, address lookup, borrowed syntax and its original region
        // head are charged before allocation. An address never determines ID.
        (self.charge)(span, 4)?;
        let id = NodeId {
            definition: self.index.table.definition,
            ordinal: self.index.table.nodes.len(),
            kind,
        };
        self.index.table.nodes.push(NodeInfo { span, kind });
        self.index.nodes.insert((kind, address), id);
        self.index.originals.push(original);
        self.index.region_heads.push(self.region);
        Ok(())
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
        let mut tasks = vec![match &declaration.body {
            FnBody::Natural(n) => Task::Natural(n),
            FnBody::Meaning { function, .. } | FnBody::MeaningReference { function } => {
                Task::Reference(function)
            }
            FnBody::MeaningCompose { second, .. } => Task::Reference(second),
            FnBody::MeaningTensor { right, .. } => Task::Reference(right),
            FnBody::Basis(expression) => Task::Basis(expression),
            FnBody::Quantum(block) => Task::Block(block),
        }];
        if let FnBody::MeaningCompose { first, .. } | FnBody::MeaningTensor { left: first, .. } =
            &declaration.body
        {
            (self.charge)(first.span, 1)?;
            tasks.push(Task::Reference(first));
        }
        if declaration.kind != FnKind::Static {
            tasks.push(Task::Type(&declaration.return_type));
        }
        if let Some(domain) = &declaration.meaning_domain {
            (self.charge)(domain.span, 1)?;
            tasks.push(Task::Type(domain));
        }
        let kind = if declaration.kind == FnKind::Classical {
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
            if let StaticParamKind::Operation {
                basis,
                codomain,
                meaning,
            } = &parameter.kind
            {
                if let Some(meaning) = meaning {
                    (self.charge)(meaning.span, 1)?;
                    tasks.push(Task::Reference(meaning));
                }
                if let Some(codomain) = codomain {
                    (self.charge)(codomain.span, 1)?;
                    tasks.push(Task::Type(codomain));
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
            if let Some((kind, address)) = task.node() {
                self.record_node(
                    kind,
                    address,
                    task.original().expect("indexed syntax"),
                    span,
                )?;
            }
            match task {
                Task::Enter => self.enter()?,
                Task::EnterBasis => self.enter_basis()?,
                Task::Leave => self.leave()?,
                Task::Region(expression, truth) => {
                    self.enter_region(expression, truth)?;
                }
                Task::LeaveRegion => {
                    let current = self.region.expect("entered original static region");
                    self.region = self.index.region_links[current].parent;
                }
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
                    NatKind::Call { callee, arguments } => {
                        tasks.extend(arguments.iter().rev().map(Task::Natural));
                        tasks.push(Task::Reference(callee));
                    }
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
                            StmtKind::StaticLet { name, value } => tasks.extend([
                                Task::Bind(name, BindingKind::StaticNatural),
                                Task::Natural(value),
                            ]),
                            StmtKind::Let { pattern, value }
                            | StmtKind::MutableLet { pattern, value, .. } => tasks.extend([
                                Task::Pattern(pattern, BindingKind::Runtime),
                                Task::Expression(value),
                            ]),
                            StmtKind::Assign { target, value } => {
                                tasks.extend([Task::Expression(value), Task::Reference(target)])
                            }
                            StmtKind::Expr(expression) => tasks.push(Task::Expression(expression)),
                        }
                    }
                }
                Task::Expression(expression) => match &expression.kind {
                    ExprKind::UnsupportedClosure(closure) => {
                        tasks.extend([Task::Leave, Task::Block(&closure.body)]);
                        tasks.extend(
                            closure
                                .parameters
                                .iter()
                                .rev()
                                .map(|p| Task::Pattern(p, BindingKind::Runtime)),
                        );
                        tasks.push(Task::Enter);
                    }
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
                    ExprKind::AccessCall {
                        callee,
                        static_args,
                        args,
                    } => {
                        tasks.extend(args.iter().rev().map(|arg| Task::Expression(&arg.value)));
                        for arg in args.iter().rev() {
                            if let Some(selection) = &arg.selection {
                                tasks.extend(selection.naturals().map(Task::Natural));
                            }
                        }
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
                        Task::LeaveRegion,
                        Task::Block(else_branch),
                        Task::Region(expression, Some(false)),
                        Task::LeaveRegion,
                        Task::Block(then_branch),
                        Task::Region(expression, Some(true)),
                        Task::Predicate(predicate),
                    ]),
                    ExprKind::StaticFold {
                        index,
                        start,
                        end,
                        carry,
                        initial,
                        body,
                        ..
                    } => tasks.extend([
                        Task::Leave,
                        Task::LeaveRegion,
                        Task::Block(body),
                        Task::Region(expression, None),
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
                    ExprKind::ApplyStatic { operation, input }
                    | ExprKind::Adjoint { operation, input } => {
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

    fn index(
        definition: DefId,
        declaration: &Decl,
        global: impl Fn(&str) -> Option<Target>,
    ) -> Index<'_> {
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

    fn original_node<'ast>(lookup: &Lookup<'_, 'ast>, id: NodeId) -> Option<OriginalNode<'ast>> {
        lookup
            .original_node_budgeted(id, |_, _| Ok::<_, std::convert::Infallible>(()))
            .unwrap_or_else(|never| match never {})
    }

    #[test]
    fn fallible_original_getters_refuse_foreign_and_transferred_syntax() {
        let module =
            parse_module("unitary fn f[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}").unwrap();
        let declaration = &module.decls[0];
        let relocated = declaration.clone();
        let mut original = index(DefId(0), declaration, |_| None);
        fn get_nodes(declaration: &Decl) -> (&Type, &Natural, &Ident) {
            let FnBody::Quantum(body) = &declaration.body else {
                panic!("quantum body");
            };
            let TypeKind::Q(basis) = &declaration.params[0].ty.kind else {
                panic!("quantum parameter");
            };
            let TypeKind::Bits(natural) = &basis.kind else {
                panic!("sized basis");
            };
            (
                &declaration.params[0].ty,
                natural,
                expression_name(&body.result),
            )
        }
        let (ty, natural, reference) = get_nodes(declaration);
        let (foreign_ty, foreign_natural, foreign_reference) = get_nodes(&relocated);
        assert_eq!(original.try_node_id_ty(ty), Some(original.node_id_ty(ty)));
        assert_eq!(
            original.try_node_id_natural(natural),
            Some(original.node_id_natural(natural))
        );
        assert_eq!(
            original.try_natural_usage(natural),
            Some(original.natural_usage(natural))
        );
        assert_eq!(
            original.try_usage(reference),
            Some(original.usage(reference))
        );
        let binder = &declaration.static_params[0].name;
        assert_eq!(original.try_binder(binder), Some(original.binder(binder)));
        assert_eq!(original.try_node_id_ty(foreign_ty), None);
        assert_eq!(original.try_node_id_natural(foreign_natural), None);
        assert_eq!(original.try_natural_usage(foreign_natural), None);
        assert_eq!(original.try_usage(foreign_reference), None);
        assert_eq!(original.try_binder(&relocated.static_params[0].name), None);
        let _occurrences = original.take_occurrences();
        assert_eq!(original.try_node_id_ty(ty), None);
        assert_eq!(original.try_node_id_natural(natural), None);
        assert_eq!(original.try_natural_usage(natural), None);
        assert_eq!(original.try_usage(reference), None);
        assert_eq!(original.try_binder(binder), None);
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
    fn fallible_binder_and_use_lookup_reject_foreign_owner_and_ordinal() {
        let small = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let large = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{let a=q;let b=a;b}").unwrap();
        let original = index(DefId(7), &small.decls[0], |_| None);
        let same_owner = index(DefId(7), &large.decls[0], |_| None);
        let other_owner = index(DefId(8), &small.decls[0], |_| None);
        let FnBody::Quantum(small_body) = &small.decls[0].body else {
            panic!("quantum body");
        };
        let FnBody::Quantum(large_body) = &large.decls[0].body else {
            panic!("quantum body");
        };
        let StmtKind::Let { pattern, .. } = &large_body.statements[1].kind else {
            panic!("second local binding");
        };
        let valid_binder = original.binder(name(&small.decls[0].params[0].pattern));
        let valid_use = original.usage(expression_name(&small_body.result));
        assert!(std::ptr::eq(
            original.table.try_binder(valid_binder).unwrap(),
            original.table.binder(valid_binder)
        ));
        assert!(std::ptr::eq(
            original.table.try_usage(valid_use).unwrap(),
            original.table.usage(valid_use)
        ));

        // These are legitimate IDs from a different original collection, not
        // fabricated fields. Matching DefId alone cannot make ordinals valid.
        let foreign_binder = same_owner.binder(name(pattern));
        let foreign_use = same_owner.usage(expression_name(&large_body.result));
        assert_eq!(foreign_binder.definition(), valid_binder.definition());
        assert_eq!(foreign_use.definition(), valid_use.definition());
        assert!(foreign_binder.ordinal >= original.table.binders.len());
        assert!(foreign_use.ordinal >= original.table.uses.len());
        assert!(original.table.try_binder(foreign_binder).is_none());
        assert!(original.table.try_usage(foreign_use).is_none());

        let foreign_binder = other_owner.binder(name(&small.decls[0].params[0].pattern));
        let foreign_use = other_owner.usage(expression_name(&small_body.result));
        assert_eq!(foreign_binder.ordinal, valid_binder.ordinal);
        assert_eq!(foreign_use.ordinal, valid_use.ordinal);
        assert!(original.table.try_binder(foreign_binder).is_none());
        assert!(original.table.try_usage(foreign_use).is_none());
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
        assert!(a.nodes.keys().all(|key| !b.nodes.contains_key(key)));
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
    fn syntax_nodes_keep_distinct_structural_ids_when_spans_match() {
        let mut module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{let q=q;q}").unwrap();
        let declaration = &mut module.decls[0];
        let FnBody::Quantum(body) = &mut declaration.body else {
            panic!()
        };
        let StmtKind::Let { value, .. } = &mut body.statements[0].kind else {
            panic!()
        };
        value.span = Span::default();
        body.result.span = Span::default();
        let relocated = declaration.clone();
        let original = index(DefId(7), declaration, |_| None);
        let copied = index(DefId(7), &relocated, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!()
        };
        let StmtKind::Let { value, .. } = &body.statements[0].kind else {
            panic!()
        };
        let first = original.node_id_expr(value);
        let second = original.node_id_expr(&body.result);
        assert_ne!(first, second);
        assert_eq!(original.table.node(first), original.table.node(second));
        assert_eq!(original.table, copied.table);
        let Some(OriginalNode::Expression(retained)) = original.original_node(first) else {
            panic!("original borrowed expression");
        };
        assert!(std::ptr::eq(retained, value));
        assert!(
            copied
                .original_node(NodeId {
                    definition: DefId(8),
                    ..first
                })
                .is_none()
        );
        assert!(
            original
                .original_node(NodeId {
                    kind: NodeKind::Natural,
                    ..first
                })
                .is_none()
        );
        assert!(
            original
                .original_node(NodeId {
                    ordinal: usize::MAX,
                    ..first
                })
                .is_none()
        );
        assert!(
            original
                .nodes
                .keys()
                .all(|key| !copied.nodes.contains_key(key))
        );
        assert_eq!(original.node_id_block(body).kind, NodeKind::Block);
        assert_eq!(
            original.node_id_ty(&declaration.return_type).kind,
            NodeKind::Type
        );

        let mut foreign = first;
        foreign.definition = DefId(8);
        assert!(std::panic::catch_unwind(|| original.table.node(foreign)).is_err());
        let mut wrong_kind = first;
        wrong_kind.kind = NodeKind::Natural;
        assert!(std::panic::catch_unwind(|| original.table.node(wrong_kind)).is_err());
    }

    #[test]
    fn original_node_cell_is_charged_before_any_parallel_collection_changes() {
        let module = parse_module("static fn one()->Nat{1}").unwrap();
        let declaration = &module.decls[0];
        let FnBody::Natural(natural) = &declaration.body else {
            panic!("natural body");
        };
        let original = index(DefId(0), declaration, |_| None);
        let before = (
            original.table.nodes.len(),
            original.nodes.len(),
            original.originals.len(),
            original.region_heads.len(),
        );
        let mut builder = Builder {
            index: original,
            global: |_: &str| None,
            charge: |_, cells| {
                assert_eq!(cells, 4, "metadata, address, borrowed node and region head");
                Err(())
            },
            origin: declaration.span,
            names: BTreeMap::new(),
            static_parameters: BTreeMap::new(),
            frames: Vec::new(),
            region: None,
        };
        assert!(
            builder
                .record_node(
                    NodeKind::Natural,
                    std::ptr::from_ref(natural) as usize,
                    OriginalNode::Natural(natural),
                    natural.span,
                )
                .is_err()
        );
        assert_eq!(
            before,
            (
                builder.index.table.nodes.len(),
                builder.index.nodes.len(),
                builder.index.originals.len(),
                builder.index.region_heads.len()
            )
        );
    }

    #[test]
    fn original_regions_include_inactive_empty_arms_and_zero_fold_body_only() {
        let module = parse_module(
            "unitary fn f(q:Q<Bit>)->Q<Bit>{
                 if static 0==1 {qfor static i in 0..0 carry r=q {yield r;}}else{q}
             }
             unitary fn empty()->Unit{if static 0==1 {}else{}}",
        )
        .unwrap();
        let declaration = &module.decls[0];
        let original = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            unreachable!()
        };
        let ExprKind::StaticIf {
            then_branch,
            else_branch,
            ..
        } = &body.result.kind
        else {
            unreachable!()
        };
        let conditional = original.node_id_expr(&body.result);
        let ExprKind::StaticFold {
            start,
            initial,
            body: fold_body,
            ..
        } = &then_branch.result.kind
        else {
            unreachable!()
        };
        let fold = original.node_id_expr(&then_branch.result);
        let chain = |node| {
            original
                .enclosing_regions(node)
                .unwrap()
                .map(|region| region.unwrap())
                .collect::<Vec<_>>()
        };
        assert!(chain(conditional).is_empty());
        assert_eq!(
            chain(fold),
            vec![OriginalRegion::Predicate {
                node: conditional,
                truth: true
            }]
        );
        assert_eq!(chain(original.node_id_natural(start)), chain(fold));
        assert_eq!(chain(original.node_id_expr(initial)), chain(fold));
        assert_eq!(
            chain(original.node_id_expr(&fold_body.result)),
            vec![
                OriginalRegion::Fold { node: fold },
                OriginalRegion::Predicate {
                    node: conditional,
                    truth: true
                },
            ]
        );
        assert_eq!(
            chain(original.node_id_expr(&else_branch.result)),
            vec![OriginalRegion::Predicate {
                node: conditional,
                truth: false
            }]
        );

        let empty = &module.decls[1];
        let mut original = index(DefId(1), empty, |_| None);
        let FnBody::Quantum(body) = &empty.body else {
            unreachable!()
        };
        let ExprKind::StaticIf {
            then_branch,
            else_branch,
            ..
        } = &body.result.kind
        else {
            unreachable!()
        };
        let conditional = original.node_id_expr(&body.result);
        for (block, truth) in [(then_branch, true), (else_branch, false)] {
            assert!(block.implicit_result);
            assert_eq!(
                original
                    .enclosing_regions(original.node_id_expr(&block.result))
                    .unwrap()
                    .map(|region| region.unwrap())
                    .collect::<Vec<_>>(),
                vec![OriginalRegion::Predicate {
                    node: conditional,
                    truth
                }]
            );
        }
        original.region_links[0].parent = Some(0);
        assert!(
            original
                .enclosing_regions(original.node_id_expr(&then_branch.result))
                .unwrap()
                .next()
                .unwrap()
                .is_err()
        );
    }

    #[test]
    fn original_region_link_is_charged_before_head_or_arena_changes() {
        let module = parse_module("unitary fn f()->Unit{if static 0==1 {}else{}}").unwrap();
        let declaration = &module.decls[0];
        let FnBody::Quantum(body) = &declaration.body else {
            unreachable!()
        };
        let original = index(DefId(0), declaration, |_| None);
        let before = original.region_links.len();
        let mut builder = Builder {
            index: original,
            global: |_: &str| None,
            charge: |_, cells| {
                assert_eq!(cells, 1);
                Err(())
            },
            origin: declaration.span,
            names: BTreeMap::new(),
            static_parameters: BTreeMap::new(),
            frames: Vec::new(),
            region: None,
        };
        assert!(builder.enter_region(&body.result, Some(true)).is_err());
        assert_eq!(builder.index.region_links.len(), before);
        assert!(builder.region.is_none());
    }

    #[test]
    fn every_static_and_basis_node_kind_has_an_original_occurrence() {
        let module = parse_module(
            "unitary fn f[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{let q=g[type(Bits<n+0>)](q);basis q as b {b}}",
        )
        .unwrap();
        let declaration = &module.decls[0];
        let mut original = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!()
        };
        let StmtKind::Let { value, .. } = &body.statements[0].kind else {
            panic!()
        };
        let ExprKind::Call {
            callee,
            static_args,
            ..
        } = &value.kind
        else {
            panic!()
        };
        let operation = &static_args[0];
        let StaticOpKind::Type(ty) = &operation.kind else {
            panic!()
        };
        let TypeKind::Bits(natural) = &ty.kind else {
            panic!()
        };
        let ExprKind::CoherentLift { basis, .. } = &body.result.kind else {
            panic!()
        };
        assert_eq!(original.reference_site(callee), original.usage(callee));
        let operation_node = original.node_id_static_op(operation);
        let basis_node = original.node_id_basis_expr(basis);
        assert_eq!(operation_node.kind, NodeKind::StaticOp);
        assert_eq!(original.node_id_ty(ty).kind, NodeKind::Type);
        assert_eq!(original.node_id_natural(natural).kind, NodeKind::Natural);
        assert_eq!(basis_node.kind, NodeKind::BasisExpr);
        let relocated = declaration.clone();
        let copied = index(DefId(0), &relocated, |_| None);
        assert_eq!(original.table, copied.table);
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, std::convert::Infallible>(())
            })
            .unwrap_or_else(|never| match never {});
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        let lookup = forest.lookup(&tables);
        assert_eq!(lookup.node_id_static_op(operation), operation_node);
        assert_eq!(lookup.node_id_basis_expr(basis), basis_node);
        let Some(OriginalNode::Operation(retained_operation)) =
            original_node(&lookup, operation_node)
        else {
            panic!("original static operation");
        };
        let Some(OriginalNode::Basis(retained_basis)) = original_node(&lookup, basis_node) else {
            panic!("original basis expression");
        };
        assert!(std::ptr::eq(retained_operation, operation));
        assert!(std::ptr::eq(retained_basis, basis));
    }

    #[test]
    fn later_static_naturals_and_global_candidates_keep_the_same_local_identity() {
        let module = parse_module("unitary fn f[const U:Op<Bits<n>>,const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>> requires Applicable(U){U(q)}").unwrap();
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
    fn forest_lookup_borrows_original_tables_and_preserves_natural_occurrences() {
        let module =
            parse_module("unitary fn f[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}").unwrap();
        let decl = &module.decls[0];
        let mut original = index(DefId(0), decl, |_| None);
        let parameter = name(&decl.params[0].pattern);
        let binder = original.binder(parameter);
        let FnBody::Quantum(body) = &decl.body else {
            panic!()
        };
        let result = expression_name(&body.result);
        let result_site = original.usage(result);
        let TypeKind::Q(basis) = &decl.params[0].ty.kind else {
            panic!()
        };
        let TypeKind::Bits(natural) = &basis.kind else {
            panic!()
        };
        let natural_site = original.natural_usage(natural);
        assert_eq!(original.natural_site(natural), natural_site);
        assert_eq!(natural_site.definition(), DefId(0));
        let natural_node = original.node_id_natural(natural);
        assert_eq!(natural_node.definition(), DefId(0));
        let result_node = original.node_id_expr(&body.result);
        let block_node = original.node_id_block(body);
        let parameter_type_node = original.node_id_ty(&decl.params[0].ty);
        let original_storage = original.originals.as_ptr();
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), decl.span, |_, _| {
                Ok::<_, std::convert::Infallible>(())
            })
            .unwrap_or_else(|never| match never {});
        // Transfer happens only after common source checking. All occurrence
        // maps move; the one authoritative Table remains with its judgment.
        assert!(original.natural_references.is_empty());
        assert!(original.nodes.is_empty());
        assert!(original.originals.is_empty());
        assert!(original.original_association.is_none());
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        assert_eq!(
            forest.originals[&DefId(0)].originals.as_ptr(),
            original_storage
        );
        let table = &tables[&DefId(0)];
        assert_eq!(Arc::strong_count(table), 1);
        let lookup = forest.lookup(&tables);
        assert_eq!(lookup.binder(parameter), binder);
        assert!(std::ptr::eq(lookup.info(binder), table.binder(binder)));
        assert!(std::ptr::eq(lookup.key(binder), table.key(binder)));
        assert!(std::ptr::eq(lookup.usage(result), table.usage(result_site)));
        assert!(std::ptr::eq(
            lookup.natural_usage(natural),
            table.usage(natural_site)
        ));
        assert_eq!(lookup.reference_site(result), result_site);
        assert_eq!(lookup.natural_site(natural), natural_site);
        assert_eq!(lookup.node_id_natural(natural), natural_node);
        assert_eq!(lookup.node_id_expr(&body.result), result_node);
        assert_eq!(lookup.node_id_block(body), block_node);
        assert_eq!(lookup.node_id_ty(&decl.params[0].ty), parameter_type_node);
        assert_eq!(lookup.local_key(result), Some(table.key(binder)));
        assert_eq!(Arc::strong_count(table), 1);
        let Some(OriginalNode::Expression(retained_result)) = original_node(&lookup, result_node)
        else {
            panic!("original expression");
        };
        let Some(OriginalNode::Natural(retained_natural)) = original_node(&lookup, natural_node)
        else {
            panic!("original natural");
        };
        let Some(OriginalNode::Type(retained_type)) = original_node(&lookup, parameter_type_node)
        else {
            panic!("original type");
        };
        let Some(OriginalNode::Block(retained_block)) = original_node(&lookup, block_node) else {
            panic!("original block");
        };
        assert!(std::ptr::eq(retained_result, body.result.as_ref()));
        assert!(std::ptr::eq(retained_natural, natural));
        assert!(std::ptr::eq(retained_type, &decl.params[0].ty));
        assert!(std::ptr::eq(retained_block, body));
    }

    #[test]
    fn all_moved_occurrence_cells_are_charged_before_the_merge() {
        let module =
            parse_module("unitary fn f[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{q}").unwrap();
        let declaration = &module.decls[0];
        let mut original = index(DefId(0), declaration, |_| None);
        let occurrences = original.take_occurrences();
        let expected = 2
            * (occurrences.bindings.len()
                + occurrences.references.len()
                + occurrences.natural_references.len()
                + occurrences.nodes.len())
            + 2 * occurrences.originals.len()
            + 4;
        let mut forest = OccurrencesForest::default();
        assert_eq!(
            forest.insert_budgeted(occurrences, declaration.span, |_, cells| {
                assert_eq!(cells, expected);
                Err(())
            }),
            Err(())
        );
        assert!(forest.bindings.is_empty());
        assert!(forest.references.is_empty());
        assert!(forest.natural_references.is_empty());
        assert!(forest.nodes.is_empty());
        assert!(forest.originals.is_empty());
    }

    #[test]
    fn original_lookup_rejects_foreign_kind_ordinal_and_reindexed_equal_table() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let declaration = &module.decls[0];
        let relocated = declaration.clone();
        let larger = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{let a=q;let b=a;b}").unwrap();
        let mut original = index(DefId(7), declaration, |_| None);
        let other = index(DefId(7), &relocated, |_| None);
        let larger_index = index(DefId(7), &larger.decls[0], |_| None);
        let FnBody::Quantum(larger_body) = &larger.decls[0].body else {
            panic!("larger quantum body");
        };
        let larger_node = larger_index.node_id_expr(&larger_body.result);
        assert_eq!(original.table, other.table);
        assert!(!Arc::ptr_eq(
            &original.table.association,
            &other.table.association
        ));
        let FnBody::Quantum(body) = &declaration.body else {
            panic!("quantum body");
        };
        let node = original.node_id_expr(&body.result);
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        let tables = BTreeMap::from([(DefId(7), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        let lookup = forest.lookup(&tables);
        assert!(original_node(&lookup, node).is_some());
        for invalid in [
            NodeId {
                definition: DefId(8),
                ..node
            },
            NodeId {
                kind: NodeKind::Natural,
                ..node
            },
            NodeId {
                ordinal: usize::MAX,
                ..node
            },
            NodeId {
                ordinal: tables[&DefId(7)].nodes.len(),
                ..node
            },
            larger_node,
        ] {
            assert!(original_node(&lookup, invalid).is_none());
        }
        let unrelated_tables = BTreeMap::from([(DefId(7), Arc::new(other.table))]);
        assert!(original_node(&forest.lookup(&unrelated_tables), node).is_none());
    }

    #[test]
    fn original_lookup_refuses_mismatched_table_and_forward_association() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let declaration = &module.decls[0];
        let mut original = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!("quantum body");
        };
        let node = original.node_id_expr(&body.result);
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        let mut changed = original.table.clone();
        changed.nodes[node.ordinal].span = Span::default();
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let changed_tables = BTreeMap::from([(DefId(0), Arc::new(changed))]);
        let mut forest = Forest::from_occurrences(occurrences);
        assert!(original_node(&forest.lookup(&changed_tables), node).is_none());
        assert!(original_node(&forest.lookup(&tables), node).is_some());
        forest
            .nodes
            .remove(&(node.kind, std::ptr::from_ref(body.result.as_ref()) as usize));
        assert!(original_node(&forest.lookup(&tables), node).is_none());
    }

    #[test]
    fn duplicate_original_owner_is_ambiguous_without_overwriting_first_borrow() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let declaration = &module.decls[0];
        let relocated = declaration.clone();
        let mut original = index(DefId(0), declaration, |_| None);
        let mut duplicate = index(DefId(0), &relocated, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!("quantum body");
        };
        let node = original.node_id_expr(&body.result);
        let storage = original.originals.as_ptr();
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        occurrences
            .insert_budgeted(duplicate.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        let retained = &occurrences.originals[&DefId(0)];
        assert!(retained.ambiguous);
        assert_eq!(retained.originals.as_ptr(), storage);
        assert!(Arc::ptr_eq(
            retained.association.as_ref().unwrap(),
            &original.table.association
        ));
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        assert!(original_node(&forest.lookup(&tables), node).is_none());
    }

    #[test]
    fn failed_duplicate_merge_preserves_the_original_association() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let declaration = &module.decls[0];
        let mut original = index(DefId(0), declaration, |_| None);
        let mut duplicate = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!("quantum body");
        };
        let node = original.node_id_expr(&body.result);
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        assert_eq!(
            occurrences.insert_budgeted(
                duplicate.take_occurrences(),
                declaration.span,
                |_, _| Err(())
            ),
            Err(())
        );
        assert!(!occurrences.originals[&DefId(0)].ambiguous);
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        assert!(original_node(&forest.lookup(&tables), node).is_some());
    }

    #[test]
    fn reverse_lookup_charges_each_access_and_propagates_budget_failure() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let declaration = &module.decls[0];
        let mut original = index(DefId(0), declaration, |_| None);
        let FnBody::Quantum(body) = &declaration.body else {
            panic!("quantum body");
        };
        let node = original.node_id_expr(&body.result);
        let mut occurrences = OccurrencesForest::default();
        occurrences
            .insert_budgeted(original.take_occurrences(), declaration.span, |_, _| {
                Ok::<_, ()>(())
            })
            .unwrap();
        let tables = BTreeMap::from([(DefId(0), Arc::new(original.table))]);
        let forest = Forest::from_occurrences(occurrences);
        let lookup = forest.lookup(&tables);
        for allowance in 0..7 {
            let mut visits = 0;
            let result = lookup.original_node_budgeted(node, |_, cells| {
                assert_eq!(cells, 1);
                visits += 1;
                if visits > allowance { Err(()) } else { Ok(()) }
            });
            assert!(matches!(result, Err(())));
            assert_eq!(visits, allowance + 1);
        }
        let mut visits = 0;
        assert!(
            lookup
                .original_node_budgeted(node, |_, cells| {
                    visits += cells;
                    Ok::<_, ()>(())
                })
                .unwrap()
                .is_some()
        );
        assert_eq!(visits, 7);
    }

    #[test]
    fn initial_association_is_charged_before_original_traversal() {
        let module = parse_module("unitary fn f(q:Q<Bit>)->Q<Bit>{q}").unwrap();
        let mut charges = 0;
        let result = Index::new_budgeted(
            DefId(0),
            &module.decls[0],
            |_| {
                panic!("must not resolve before the initial reservation");
            },
            |span, cells| {
                charges += 1;
                assert_eq!(span, module.decls[0].span);
                assert_eq!(cells, 5);
                Err(())
            },
        );
        assert!(matches!(result, Err(())));
        assert_eq!(charges, 1);
    }

    #[test]
    fn static_candidate_does_not_replace_the_runtime_shadow_identity() {
        let module = parse_module(
            "unitary fn f[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){let U=q;U(q)}",
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
