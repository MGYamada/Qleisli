# Independent read-only runtime-binding review

Reviewer: `/root/isometry_cli_tests`, in the parent's current development task.
Status: ordinary technical review; no human adoption, proof or execution claim.

No actionable source mismatch was found in the frozen implementation against
[contract-v2.md](contract-v2.md). This review read the complete retained
[HEAD patch](implementation.patch), the new private pattern helper directly,
both binding adapters, their actual call sites and the unchanged type/value
invariants. The patch covers the four tracked paths; the fifth new production
path, `src/frontend/pattern.rs`, is read directly and covered by the retained
[five-source map](implementation-inputs.json).

The retained patch SHA-256 is
`ab00e79781e3f68136c1c5017843384657279715433d27b9c33da774a89c9672`.
Read-only hashing verified that all five current production files match that
map, and that the retained patch matches its recorded digest. This identifies
the reviewed bytes; it is not compiled-source or complete-runtime attestation.

## Checked behavior and invariants

- The shared helper calls the actual binding consumers, with no pattern
  certificate, preflight substitute, added AST variant, parser rule, public API
  or semantic acceptance path.
- Wildcard uses the former consumer's exact linearity query. Finite names and
  wildcards do not allocate a rebuilt type tree. A logical `Q<Unit>` or
  `Q<Bits<0>>` remains linear; physical zero width supplies no discard exemption.
- Duplicate spelling enters the same existing name set before the name hook,
  so the previous duplicate error wins. Finite runtime parameters share their
  existing set; each let gets its former fresh set. Sized declaration-wide
  duplicate traversal is unchanged, with a fresh set per actual pattern.
- `pattern_fields` still requires ordinary Unit for an empty pattern and exact
  immediate ordinary tuple arity for a nonempty one. No product flattening,
  implicit owner split, tuple/Bits conversion or argument-list spreading occurs.
- Each child is bound before the next. Earlier private scope mutations before
  a later rejection match the original algorithms; no partially checked
  preparation, proposal or accepted handle is thereby returned.
- Finite payload type construction and `into_fields` use the existing Value
  representation. Its exact type/field count invariant makes the existing zip
  traversal safe: Pair has two fields; Tuple moves its original field vector;
  no valid quantum payload can pass ordinary tuple shape and then be dropped.
  Sized type shape borrows the original Type and then moves its original tuple
  vector; no cloned field tree or additional leaf buffer is introduced.
- Finite wildcard/duplicate/shape/live-shadow error code, text and spans match
  the retained removed code, including the explicit quantum split help. Sized
  preserves its own error categories/spans and calls unchanged `bind_name`.
  That function retains boundedness, retained-cell capacity, static shadow,
  live-owner shadow, checked fresh identity, prior-key removal and insertion
  in their former order.
- Actual parameter, let and fold call sites keep type/work checks and RHS
  evaluation before binding. Lexical BinderKey and dynamic owner identities,
  caller register/frame accounting and consumed-local resolution are unchanged.
  Fold values still enter only through explicit carry; no outer quantum capture
  or reused source identity is added.
- Concrete sized elaboration and finite basis-pattern binding remain unchanged
  independent stages. This unit does not claim they migrated to the helper.

## Evidence and limits

The existing before-source session and its v2 correction were read, not rerun.
In particular, the finite invalid-unused-sibling case can make an earlier
native checker call before rejecting the complete preparation; the selected
source route rejects that case before native checking. Neither route publishes
a checked preparation/proposal after the invalid declaration. Native checking
is not program runtime execution, and the contract does not falsely promise
zero native calls for every rejection.

This reviewer ran no Cargo/Lean build, tests, qleisli CLI, native checker or
after-source replay. Compilation and actual before/after diagnostic, invocation
count and byte comparisons remain the parent's separate validation duties.
No maximum case was generated and no source/record metadata was rewritten;
this file is an additive review record only. Source inspection plus hashes
does not prove source preservation, full common declaration checking, canonical
std/QFT exposure, quantitative resource certification or release readiness.

QS/PR/RS/EXACT pending obligations and both scoped ordinary QLV1 guarantees
retain their adopted scopes and premises. This technical review performs no
constitutional act and earns no #32/#317 completion credit.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
