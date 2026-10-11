# Private interface plan

This is implementation preparation under [#32](contract.md), not an alternate
language specification. Production source has not been changed for this unit.

1. Change the private projected module from one `Function` to all supported
   functions in source order. Keep a total one-to-one correspondence with common
   `Module.decls`; do not filter unsupported declarations or silently select an
   entry. Empty modules remain rejected.
2. Extract the existing per-declaration projection into one shared function
   taking `&source::Decl` and optional borrowed `locals::Index`. The initial
   module preflight and later indexed projection must both use those exact
   profile rules. All original syntax/spans remain in the common AST; there is
   no source reparse or alternative parser.
3. Construct one common `Index` per resolved `DefId`, borrowing exactly
   `syntax[module].decls[declaration.ast_index]`. Retain only numeric IDs and the
   owned `Arc<Table>` in each projected function. Store the projected function
   at that `ast_index`. `DefId` ordering is name based and is not a source-array
   index; `ParsedProgram::definition(id)` must explicitly use the declaration's
   module and `ast_index`.
4. Resolve imports once per module at the current post-profile boundary. Bind
   the same module-level global candidates into every function's own lexical
   table, then generically check every declaration in source order. Keep local
   binder targets independent of this global binding. Preserve module order and
   existing single-function failure order; attach failures to the actual
   function's source span and module.
5. Record call/provider graph edges by the caller and callee `DefId`. Existing
   signature specialization substitutes caller expressions into the callee's
   `BinderKey`s; this must continue across sibling declarations. Only
   `callee == current_definition` may use the existing decreasing-recursion
   rule. After all bodies are checked, reject every remaining mutual cycle,
   including cycles passing through provider references. Generic zero-count or
   unreachable code must still contribute checked references and obligations.
6. Keep concrete elaboration and specialization caches keyed by actual
   definition identity plus current static bindings. Each frame uses the table
   belonging to its selected function. Repeated execution keeps fresh dynamic
   owner/value identities, independent of lexical binder identity. Public host
   maps continue to accept names at the API boundary and resolve them explicitly.
7. Keep `Resolution::visible` as the authority for host/external visibility:
   same-module private siblings and providers retain existing module privilege;
   external imports and host entries require public declarations. Import
   collisions, duplicate declarations and unsupported aliases are not relaxed.

Expected edited production areas after authorization are sized `ast`, the
projection, `ParsedProgram` indexing and the generic program traversal. Existing
resolution, lexical-ID, specialization, cache and lowering interfaces should be
reused; inspect their callers before concluding that no additional adjustment is
needed. Add bounded tests and separate before/after records. No Lean acceptance
rule, native gate, release claim or guarantee ledger change belongs in this unit.
