# Documentation proposal self-review and clarification 02

**Local candidate only.** This is the original prose author's self-review, not
an independent specification review. Only additive proposal files were written;
active Reference sources and CHANGELOG remain unchanged. Apply this patch only
after the original `proposed.patch` and `proposal-clarification/clarification.patch`,
subject to root review and the actual implementation/validation barrier.

Four corrections are included (five replacement blocks across two chapters):

1. Narrow static-kind availability to preceding static parameters. Complete
   interface registration permits valid forward and backward sibling declaration
   references; a later static kind is not made available by that registration.
   The original declaration/binder identities and semantic error priority remain.
2. Distinguish loader accounting. `project.rs::load_anchored` applies its byte
   policy before `Source::bundled`; its directory-entry limits govern local
   filesystem discovery. `sized.rs::supplied_module_count` reserves four bundled
   slots before adapter map construction, and `parse_inputs` applies the 64 KiB
   per-module/1 MiB aggregate policy before bundled copying/parsing. The selected
   64-module ceiling is not imposed on the finite loader. Legacy finite bytes
   remain explicitly unbounded. Both chapter sentences are corrected.
3. Limit fresh finite facts to checking, compilation and checked-effect
   operations. Source-only documentation/rendering APIs do not receive semantic
   approval; mutable Project checking must still reconstruct original facts.
4. Remove the deleted `sized/check.rs::primitive_signature` citation. Current
   common primitive contracts are in `check/primitive.rs`; selected closed
   binding/substitution checks are in `sized/check.rs`, its concrete subset is
   in `sized/primitive.rs`, and materialization is the existing
   `sized/elaborate.rs::primitive`. This finding was separately reported by the
   core implementation author; it is corroborated here by actual source.

The remaining reviewed distinctions match the inspected implementation: one
common complete-original judgment; all four ordinary bundles; the shared 27-name
catalog without emitter support; exact owner/type-tree contracts; common 1M work
and 4096/depth64 per-value capacity, with selected-only 16384 retained scope
cells and separate finite/concrete limits; direct named runtime quantum groups
versus strict unary opaque Op/host-provider contracts; conservative access from
all actual Op arguments; and located pending obligations whose identity checks
do not discharge semantic equality or source preservation.

No validator, test, build, CLI, native or Lean execution was performed for this
clarification. The root's latest attempt was reported live during preparation;
no pending result is treated as success. Current source hashes below are a
bounded, incomplete inspection binding, not a full closure, test attestation or
proof. Source identity/native success is not a new guarantee, Guardian act,
QS/PR/RS/EXACT discharge, Issue completion, full CI or release approval. Both
admitted decoded-root guarantees retain their exact scopes. The protected
records were read; the supplied trusted base is
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. Root reported its startup continuity
guard passed; this task explicitly prohibited a new validator run.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
