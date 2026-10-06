# Final common original-AST source review

This is an additive technical review of the source identified by `inputs.json`.
No blocking defect was found in the reviewed scope. That finding is bounded
source inspection, not a proof of checker correctness or source preservation.

The reviewer did not implement `check.rs`, its six checker submodules or the
finite/selected consumer integration. The reviewer previously authored support
work in `resolve.rs`, `resolve/locals.rs` and `sized/linear.rs`, and authored
documentation and test migrations for this unit. Review of those support files
is self-review; this record does not present it as independent review. The prose
and test migrations are not an independent specification oracle.

## Scope and constitutional state

The seven checker files, `effects.rs` and `sized/check.rs` were read completely.
The review also read the complete finite checking/compilation flow and interface
conversion in `compile/mod.rs`, selected collection/projection/instantiation
routes in `sized.rs`, the fixed registry in `source.rs`, and relevant loader,
type, concrete-operation, native-lowering and elaboration sections. The latter
supporting reads are targeted; they are not a complete audit of all concrete
lowering, transport, simulation or native code. `inputs.json` names those files
and binds their complete bytes without implying that every bound file was read
line by line.

The reviewed ordinary contract is `contract-01.md`, together with the retained
provider-access and runtime-group clarifications. Historical candidate notices
remain historical; the ordinary before-code receipts are separate records.
This review neither adopts a constitutional interpretation nor admits a
guarantee. The repository originals retain QS-2026-01, PR-2026-01 and RS-2026-01
as broader pending obligations, EXACT-2026-01 as a pending binding supplement,
and exactly the two admitted ordinary QLV1 decoded-root ownership/scope
guarantees with their recorded exclusions. Source checker facts do not enlarge
those guarantees. The root reported the startup continuity check passing
against `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`; this read-only reviewer did
not rerun it or a Lean build/replay.

## Findings

1. `program_with` registers complete original interfaces/lexical identities,
   then checks every original declaration body in original declaration order.
   Private and unused functions, Basis/Meaning declarations, both branches and
   zero-count fold/repeat bodies remain in the judgment. Genuine dependency
   cycles are checked after body traversal; import-only cycles are not confused
   with those dependencies. Effect inference, assertion checks and original
   pending-binding integrity all precede the consumer callback. The callback
   receives typed interfaces, effects and original occurrence maps; the Tables
   move once into shared Arcs. It receives no pass flag or accepted handle.

2. Both loaders add all four fixed ordinary bundled sources before this
   judgment. Selected loading reserves their module slots and charges actual
   bytes before copying/parsing. Finite loading charges bundled source bytes
   under its own loader policy. There is no bundled-name exemption from body
   checking. Complete collection discovery/parsing still precedes source
   judgments; this is not a promise that an earlier body error outranks a later
   loader/parser error.

3. Original Index identities distinguish local runtime owners from static
   Nat/Basis/Op/fold-index names. Runtime shadowing of active static names and
   hiding a live owner reject; consumed-owner rebinding remains valid. Ownership
   checks retain zero-width quantum owners, complete ordered tuple trees and
   dynamic binding identities. Branch frames compare those identities and exact
   normalized types. Coherent label contexts exclude runtime captures. Basis,
   declared Meaning, computed predicates and qif receive actual source checks;
   none becomes a mathematical certificate from its spelling or annotation.

4. Effects are inferred from actual checked body operations and dependencies.
   Declared Unitary/Observe bounds are checked afterward. Each abstract Op starts
   without access; individual original requirements grant only the named path.
   Transparent generic provider masks conservatively include every actual Op,
   including unused arguments. Inverse needs Apply and Adjoint; control needs
   all three. Direct runtime transforms retain their nonempty ordered quantum
   group T, same input/output and checked Nat decrease for an identical-DefId
   self-call. Opaque/static/host providers retain one `Q<A> -> Q<A>` input.
   Existing replayable Controlled transformation handling was checked against
   the concrete operation path; it is not authority for an opaque external
   unitary assertion or a black-box control fallback.

5. Normalization preserves the original kind/type scan and solver error order.
   Accounting charges before bounded stack growth, key/type/context clones,
   symbolic arithmetic and solver storage. `close_type_budgeted` preflights the
   expanded Basis replacements with Q-transparent logical capacity, separately
   charges Q visits/pushes and actual clone nodes, and charges each normalized
   coefficient before concrete arithmetic. Concrete u32 Basis replacements
   contain no symbolic coefficient/key payload to copy. Per-value 4096/depth64,
   common 1M work and selected retained-scope capacities remain engineering
   limits of the same judgment algorithm, not quantitative RS certificates.
   This inspection is not a formal accounting proof or a maximum-case run.

6. Pending Injectivity, clean, provider, Meaning/function equality and transform
   obligations are bound to original declarations/interfaces/categories/spans.
   `validate_pending_bindings` checks that binding integrity; it does not prove
   matrix equality, all-input clean return or source correspondence. Finite
   consumers explicitly retain the pending distinction and still use actual
   finite tables, implementation/evidence gates and fresh native acceptance.
   Selected projection occurs only after source success, retains each original
   DefId and located eligibility error, and aborts on projection capacity errors.
   Closed instantiation consumes shared interfaces before requested projection.
   Its hierarchy/Raw lowering outputs remain untrusted proposals.

7. Finite operations on a caller-mutable `Project` rebuild the judgment from the
   current complete AST/import records. They do not reuse stale source facts.
   Profile checks precede kernel selection; lowering obtains `AcceptedProgram`
   through `accept_raw_with_budget`. No new unchecked acceptance bypass was
   found in these reviewed consumer routes. Independent native acceptance of
   output IR still does not prove that output preserves its source.

## Existing validation association and limits

The reviewer read the actual latest/MSRV attempt-09 result records, verified
their exact hashes and all 36 referenced stdout/stderr hash/size bindings, and
compared all 20 reviewed production/support source files with the actual MSRV
input map. Every comparison matched. The historical MSRV before/after map bytes
are identical. This is a review of existing records; their stored commands were
not executed by this reviewer.

Each toolchain record reports nine successful stages, 4 shared-type tests,
279 focused integration tests and 1 separately selected small native arithmetic
test passing. The focused suite retains 8 existing ignores and explicitly
filters the two named 3000-file import-depth stress tests. The separately selected
native test is one of the focused ignored tests, so those counts describe
performed stages, not distinct suite coverage or a claim that every ignored test
ran. The 760-member Rust input map is explicitly incomplete.

The 72-observation source capture is referenced by its frozen file-map identity;
its detailed before/after comparison is a separate review. No corpus maximum,
new CLI/native call, build, test, validator, Git/GitHub mutation or fixture
execution was performed for this review. The new packet contains hashes and
notes, not duplicate raw logs. Policy validation was still pending when this
review was completed.

General source semantics/preservation, generic-family correspondence, concrete
evidence completeness, decoder/native/runtime correspondence and QS/PR/RS
discharge remain separate duties. This review supplies no Issue completion,
release approval, full CI claim, new primitive authority or proof-status change.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
