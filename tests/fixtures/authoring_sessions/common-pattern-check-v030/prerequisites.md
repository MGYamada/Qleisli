# Local candidate: common declaration/pattern prerequisite

**Status: non-normative first-source study, prepared before checks.** This
applies current contracts; it does not adopt syntax, new checking rules or a
common checker implementation.

The current Reference defines ordinary name/wildcard/exact tuple patterns,
one typed pattern per runtime argument, declaration-wide unique parameter
names, Unit matching, no implicit splitting of Q<Tuple>, and linear ownership
even for zero-width Q<Unit>/Q<Bits<0>>. Source evaluation order and existing
profile restrictions remain explicit. See
[exact types and patterns](../../../../docs/src/reference/type-model.md) and
[declarations/current profiles](../../../../docs/src/reference/source-text.md).

The prospective common-AST helper may share declaration-name and exact pattern
traversal only while retaining every original declaration, static premise,
source span/type tree and logical owner. It must preserve each caller's first
diagnostic and existing capacity/unsupported checks. A common helper may not
admit a type unsupported by a backend, promote an annotation into body effect,
skip unused functions, select an alternate acceptance path or reuse stale
facts after public Project mutation.

These eight first cases fix the desired observations:

| Case | Existing obligation to observe |
| --- | --- |
| nested-runtime-parameter | One exact nested argument contains two live owners and ordinary Unit; returning both preserves the tree/calling convention. |
| duplicate-runtime-parameter | Duplicate names reject across the complete parameter list, independently of which occurrence the body uses. |
| legal-rebinding | Evaluate h(q) before binding the new q; consuming the former owner permits replacement. |
| hidden-live-owner | Replacing q with p must not erase the original live q or imply cleanup. |
| duplicate-join-input | The second q cannot reuse the owner consumed by the first argument; no cloning follows from join. |
| quantum-unit-wildcard | Physical width zero does not permit wildcard disposal of Q<Unit>. |
| empty-register-wildcard | Q<Bits<0>> also retains a logical owner; record earlier finite profile rejection honestly. |
| unused-invalid-sibling | Never calling the private invalid function does not exempt its body from checking. |

The two controls are intended ordinary source, not promises of backend
eligibility or functional proofs. Deliberate rejection cases remain separate
counterexamples, not failed source repairs. Native-valid IR alone does not
establish preservation of the original source, and untrusted proposal bytes
grant no execution handle. Full generic/type/effect/pattern checker convergence,
canonical QFT/library exposure and the original Issue criteria remain required.

Before changing production checking, retain exact current source/CLI/native
identities and all real results. A later authorized replay must append new
records rather than rewrite these original sources or observations. No
epsilon/phase relaxation, implicit owner disposal, native primitive, dependency
or edition change is proposed.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
