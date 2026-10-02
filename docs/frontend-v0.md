# Source frontend, modules and finite IR

[Language](language-spec.md), [syntax](syntax-v0.md), [SC/FC](finite-contracts.md) normative; Rust production finite authority. Valid output IR proves no source preservation. [Trust partition](../TRUST_BOUNDARY.md) fixed.

## Entry points and project loading

check_project checks every declaration/library; compile_project additionally requires root main.qli/parameterless observe main/classical Unit-CBit-products/empty owner exit and freshly verifies IR. UTF-8 files define root-relative modules (foo differs from foo::bar); pub/use explicit, no prelude/reexport/globs/relative imports/cycles/external loader. std reserved. --qrate selects source.root under [edition2026](language-editions.md), no root Qargo. Retain OS path identity; declaration loading executes nothing. doc parses one file without semantic/evidence checks.

## Checks and lowering

Follow [language judgments](language-spec.md): exact arity/trees/effects, ordered single evaluation/moves/fresh IDs, caller/pending frames, isolated callees, total basis/injective lifts, complete simultaneous branch phis, both/zero bodies. Static forms emit checked ApplyUnitary; legacy/certified compute and functions retain independent obligations/evidence. Source snapshots alone are not preservation.

## Initial standard-library organization

Explicit basis xor2/and2; quantum init0/h/x/z/t/s/sdg/tdg/id/phase_eighth/cnot/toffoli/split/join; observe measure_z/reset/discard. Ordinary routines/transforms/arithmetic obey user checks/[ledger](stdlib-contracts.md). S/Sdg=diag(1,+/-i),Tdg=diag(1,zeta8^-1),id_A=I,phase_eighth_A=zeta8*I retain exact tree/Unit owner/no scratch. Existing T/empty/zero-axis monomial expansion adds no acceptance rule; scalar alias not legacy protected Z/T.

## Diagnostics and limits

CompileError category/path/span/Unicode coordinates: failed injection Ownership, parse/load Project, existing contract InvalidIr; actual body/call locations and exact mismatch row/column/coefficients/effects. One unstable prose error; [JSON contract](machine-interface-spec.md#diagnostics) separate. Width12/depth64/type-value4096/lowering1M/exact10M/128 sources/name4096bytes/aggregate identities1 MiB; no nested resets. macOS parent-descriptor openat/O_NOFOLLOW; Linux held /proc/self/fd, no follow-link fallback; other OS assumptions remain.

## Inputs and trust boundary

RawProgram untrusted; private VerifiedProgram only independent verify, rewrites reverify. Raw ordered width is not source tree. IDs/wires globally fresh; consume each owner once including empty/full exit. Positional QuantumPhi preserves correlations; classical inputs read before outputs. Verify every constructor/effect/gate/control/table/phase/context. No global verifier wire/instruction cap; table width12/branch depth64 incl empty. Protected raw uses broader than source Z/T; no borrowing/Release0/matrix/prose/tolerance seals. Safe privacy excludes external unsafe code.

## Reference execution

run_closed: no external/quantum outputs, classical output order/first quantum axis low. Unnormalized hidden histories sum probabilities/CP maps, never amplitudes; no cutoff/renormalization. f64 approximate. Certified aux-one/total>1e-12 or nonfinite alarms, scaled-ratio underflow protection/zero components exempt; alarm cannot certify cleanup.

Default axes16/hard20, components65,536, amplitude cells1,048,576, executed steps1M. Charge visits/circuits/protected/transitive contract work across components/selected branches; no partial/truncated output. Sampling [M1](machine-interface-spec.md), separate exact acceptance/source/device claims.

## Responsibilities and dependency direction

frontend parses/projects/checks/untrusted lowers; verify validates raw; contract exact evidence; interchange transport; sim numerical execution; host classical trials; stdlib ordinary source. Diagnostics/provenance cross boundaries explicitly, acceptance never depends on simulator output. Keep cohesive modules, public facade/contracts and focused independent tests; no convenience helper enlarges trust. [Formal scope](formal-core.md)/[migration](lean-kernel-migration.md) retain proof obligations.
