### Next common frontend unit: all checked declarations in a sized module

This ordinary implementation unit follows the reviewed lexical-identity integration; it does not begin while that shared AST/resolver transition remains unvalidated. It implements the approved single-language plan under edition 2026. Existing finite source already permits ordinary sibling declarations; the sized projection's one-function-per-module rejection is an adapter restriction to remove.

**Contract.** Retain every supported ordinary function declaration in source order through the same sized profile projection. Resolve each function using its shared `DefId` and source `ast_index`, not an ordinal assumed to equal the AST position. Imports remain module scoped; each function retains its own lexical table. Same-module private sibling calls and forward references are allowed. External imports and host entry selection retain their existing public-visibility requirements, and existing same-module provider visibility remains explicit. All declarations, including unused siblings, undergo generic source checking before preparation succeeds. This is not a claim that every unexecuted specialization has received native acceptance.

The shared declaration graph must keep distinct definitions from different modules even when their names match. Existing structurally decreasing natural self-recursion remains permitted only for the identical definition. Reject mutual cycles, including sibling cycles and cycles through static providers; do not introduce general mutual recursion. Empty modules and other unsupported declaration/type/effect profiles remain rejected. This unit adds no import-renaming grammar, public CLI signature, new capacity, or new guarantee.

**First source study.** Ten small original programs were frozen before observing fae0e6a: private forward sibling, public sibling provider, identical names in separate modules, imported terminal bindings with private wrappers, unused bad function, mutual siblings, duplicate siblings, external private import, an unsupported `as` rename, and an import colliding with a sibling. The first four pass the existing finite source checker and fail the sized adapter at its second-declaration restriction. The `as` example remains a parse rejection. Preserve these actual sources and diagnostics alongside the implementation.

**Completion checks.**
- Preserve existing single-function diagnostics, retained proposal bytes and native outcomes.
- Exercise forward/backward sibling calls, public sibling host entries, cloned parsed programs, and independently identified same-name providers/cache entries on small systems.
- Reject unused ill-typed or ownership-invalid bodies, invalid static branches and zero-iteration fold bodies during generic checking.
- Reject private external imports, private host entries, duplicate declarations and import collisions at their source locations.
- Reject sibling/provider mutual cycles; retain decreasing self-recursion and reject nondecreasing recursion or accidental recursion by unqualified-name coincidence.
- Compare equivalent split-module and same-module programs against independent small complex-amplitude expectations, including phase and axis order. Their source/artifact identities differ, so equal proposal bytes are not the required migration oracle.

Lowering remains untrusted and every actual proposal still passes its existing independent Lean gate. No source-preservation proof, wider QS/PR/RS discharge, issue completion or release readiness follows merely from this adapter convergence.
