# Supplement: nested primitive diagnostic provenance

This read-only supplement reviews the new changes after `review-final-03.md`.
That earlier review is preserved with SHA-256
`a5930b7869a8b823d500d440e9423e40c755bc773cbc092861a72fcf6047d8d6`.
Its absence of a source-review finding was not a claim of passing tests.

The retained `validation/msrv-repaired-targets-03.stdout.txt` records an actual
failure of `tuple_diagnostics_do_not_blame_returned_or_destructured_bindings`:
the diagnostic began at 195 instead of the expected 205. This reviewer read
that output and the unchanged test source; the reviewer did not execute it.
The inner `h(...)` call is also the outer `measure_z(...)` argument expression,
so an inner error already located at its call span satisfied the outer
decorator's previous span-equality condition and was relocated again.

No remaining actionable defect was found in the new provenance repair or
the accompanying CI command registration. Only this new review record was
written. No product/test source edits, tests, builds, native calls or workflow
operations were performed by this reviewer. Live or completed integration
runs require their own recorded results; this document asserts none.

## Provenance repair

`primitive_argument_located` is a private field on the private common
`SourceError`. All constructors, the sized-error conversion and both direct
budget-error literals initialize it to false. The fixed-primitive decorator
sets it only after receiving an already rejected type error at the argument
span and deciding that the argument requires quantum ownership. It sets the
marker before choosing the primitive call or actual tuple-binding location.
Outer fixed-primitive decorators skip already marked failures, preserving the
inner call location even when that location is exactly their argument span.

The marker does not participate in lexical resolution, type equality,
ownership, semantic evidence or a successful result. Public finite and sized
error conversions consume the existing category/module/span/message fields;
the private marker is not a public diagnostic field. `in_module` and ordinary
error propagation preserve it while common checking is active.

The original `self.expr(expr, scope, Some(ty))` call remains intact. Expected
type context, expression evaluation and linear moves, argument order and
successful-path budget charges therefore remain on the original path. The
repair does not substitute unconstrained expression checking followed by a
separate type comparison. No new error-path resolver or semantic acceptance
fallback is introduced.

The existing `review_v026` test checks three forms of the actual nested
failure and forbids false blame of returned or destructured bindings. The
existing canonical type diagnostic test remains unchanged. Their sources are
bound below; runtime success is a separate fact for the integrating agent.

The unchanged normalization and Linear formatting changes received another
consistency read. This reviewer authored those changes earlier, so this is
not an independent-author review of those two files. The integrator's separate
read and any validation must remain distinct from this supplement.

## CI registration

The existing `sized-corpus` group now runs the bounded local-resolution script
before the existing `test_sized_corpus.py --small` command. The original corpus
command remains present. The new script has 16 test methods and exercises
parser/producer guards without graph generation or native acceptance.

The CI runner already executes every command in order, stops on a nonzero
exit, and requires the complete command list in coverage verification. Its
code is unchanged. The coverage regression requires the new first command,
retains the historical command digest by excluding only that exact addition,
and updates the total from 90 to 91 commands while preserving 67 groups. The
CI README records the same counts. This inspection does not claim that the
parser tests, coverage tests or native comparison group have passed.

## Exact reviewed identities

SHA-256 of the bytes read for this supplement:

| File | SHA-256 |
| --- | --- |
| `src/frontend/check.rs` | `f0060cecd778ff199ada98d24776244427c0309f4637004ac46a21dff0f9b6e5` |
| `src/frontend/check/body/operations.rs` | `6d6faa315e9b7839be68df81b68371918ccd721b8d3053fd3f2f3e12215809c4` |
| `src/frontend/sized/check.rs` | `238ffb9c786351885b13ac78980a70bcaceaaf1c94a1248b9b379ade1433728b` |
| `src/frontend/check/normalize.rs` | `bd8dfc2f928bee5415a232d4b220b03e2200cc88ebf27886aaaa850291a8c68f` |
| `src/frontend/sized/linear.rs` | `98a0d14d0052e2281cc4c4b07e41f92c933ff836eb43cb0eda285cc07a66874e` |
| `tests/review_v026.rs` | `2a18e9550cdcd1de3e7ece95c6594fd70bbb96c3c8c09b86c790c5923975faee` |
| `tests/repair_diagnostics.rs` | `b96cbeeed4df5d59508b3debc8be2e18e0bd65c0581ede9b32ebfe9528855c44` |
| `scripts/test_sized_local_resolution.py` | `76508e158b5a3462b138dcbefb99ba12c8d13c998fb63f8b7c633edf03d93576` |
| `.github/ci/native-comparisons.json` | `18ed49fe1ba30a76b84d0257e6cda7d6718477f6147be59ecc6bd0686870db95` |
| `.github/ci/README.md` | `5f07da07f3940c5e332f34af34027fe855e4c0681200b8239a46ec2d20f558c3` |
| `scripts/test_run_native_ci.py` | `7ed015a029c2420bf69ed4d41017e35d603dc1b37c81a66f91b9f1bd067e6f14` |
| `scripts/run_native_ci.py` | `b7bce20620768a3aa9f53f057c264e65b11fd6fb4717835ac5c9c3221c76637e` |
| `validation/msrv-repaired-targets-03.stdout.txt` | `209944f2d3435d02e341093ac98af6fa02a97689069e5b306c46570af33f9093` |

The constitutional continuity base remains
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. This ordinary diagnostic/CI review
creates no constitutional interpretation, admitted guarantee, proof discharge,
runtime correspondence or release approval. The pending broader obligations
and existing scoped guarantees retain their recorded status. Generic qft<N>
completion and #317 namespace migration remain outside this repair review.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
