# VM-25 pure raw boundary

Status: **VM-25 straight-line pure checking complete**; the
[completion packet](completion/README.md) adds full independent complex raw
action, non-dense protected cleanup and complete retained attachment/capacity
binding. The descriptions below retain the earlier component boundary.
Production acceptance stays Rust. This is the next implementation boundary in
the [adopted migration](../../../docs/verification-migration-v0.2.md), following
VM-24's circuit/encoding equations. No production seal or public API is replaced.

## Moved code and input boundary

The Mathlib-free [raw checker](../../../lean-kernel/QleisliKernel/Raw/Structure.lean)
receives original ports, IDs, declared effects and operations. It reconstructs
live owners, persistent token/wire freshness, exact output coverage (including
Unit), register interfaces, injective lifts, circuit axes and protected uses.
It implements all eleven straight-line pure constructors: Init0, Gate, Cnot,
Toffoli, QuantumIf, Split, Join, LiftBasis, ApplyUnitary, CertifiedCompute and
ComputeUseUncompute. Classical inputs, deterministic classical operations and
branches remain VM-26 even when the quantum effect is pure.

The [finite reader](../../../lean-kernel/QleisliKernel/Raw/Finite.lean) starts
from these actual operations, not a producer-extracted circuit. It reconstructs
init/lift maps, gate/control circuits, output permutations and both compute
forms. Structural checking retains twelve-bit registers and has no global
dense-width restriction. Finite inspection uses the existing six-bit matrix
profile; it is separate from general structural validity and from production
acceptance. New semantic comparisons use at most three qubits. Metadata-only
reductions cover twelve-bit registers, two simultaneous twelve-bit owners and
oversized-event rejection before allocating a type tree or matrix. Protected
uses remain original data until the finite bounds are checked; source-label
expansion cannot precede that check.

Both computed forms reconstruct the full XOR compute/use/inverse-compute body
and check it against actual zero encodings before releasing auxiliary axes.
The three-argument form independently reconstructs its requested logical steps;
the restricted form derives logical steps from the original protected uses but
still independently validates the full physical equation. Protected Z/T,
negative controls, Unit phases and multiple auxiliary bits are retained.

Retained circuit calls receive original implementation/specification raw bodies
and complete signature trees. The checker reconstructs both bodies, compares
full matrices including phase and admits only the freshly checked prefix as
dependencies. Forward/self references, altered bodies and supplied flags or
matrix caches reject. Dependency height follows actual references, so independent
entries do not spuriously consume the depth bound. The
[completion layer](../../../lean-kernel/QleisliKernel/Raw/Function.lean) now checks
the complete FunctionIdentity/source and expanded-step contracts. This private
component envelope still does not replace production QIRF transport.

## Actual-definition proofs

[Kernel theorems](../../../lean-kernel/QleisliKernel/Raw/Structure.lean) prove
input/transition validity, global fresh insertion, complete final-owner coverage
and effect consistency along every actual executable dispatch. Accepted
reconstruction exposes the actual prepared trace, freshly evaluated events,
composition and Gram checks. Fresh evidence acceptance exposes both original
body runs and the complete empty-cache traversal; no Rust verifier/extractor
premise or producer success flag is used.

The [trace refinement continuation](trace/README.md) proves every actual dispatch
agrees with the independent [original-operation reader](../../../lean-kernel/QleisliKernel/Semantics/RawTrace.lean).
The proof includes original input ports, all eleven constructors, retained
compute/use data, controlled Unit phases and final output order. Reconstruction
consumes exactly this independently read trace; its input and output matrix
dimensions match the trace's original interface spaces.

The [complex bridge](../../../lean/Qleisli/Raw.lean) proves literal init/lift/
permutation/local-embedding coefficients, actual-event composition with arbitrary references,
joint norm preservation and phase-exact independent-request equality. Scoped
cleanup factors the freshly reconstructed physical body through its actual
logical map and zero encoding, including every dirty row and arbitrary reference
entanglement. Original-operation trace correspondence is proved separately from
the remaining general complex interpretation of every event.

The [completion proofs](completion/README.md) now cover general per-event complex
raw action, non-dense protected cleanup and complete function attachment/capacity
binding. Pure classical branches remain VM-26. The full Soundness milestone and
authority transfer are separate.

The reference [raw data](../../../lean-kernel/QleisliKernel/Semantics/Raw.lean)
imports no acceptance or transport. Existing literal complex finite references
remain unchanged; the independent trace reader also imports data only. Runtime source policy, compiled origin auditing (including
private/generated declarations), axiom checks and fresh replay are required.
The audit caught a generated partial helper for an initially written recursive
type builder; its actual implementation now uses an explicit total Nat recursor.

## Native checking and actual Rust source

Run `python3 scripts/test_lean_raw.py`. The
[current record](trace/native-validation.json) contains **121 native cases, 104 Rust
comparisons, 85 independent rational matrix checks and 180 independent
original-trace comparisons**. Every successful matrix
is compared entry by entry, including scalar phase, and independently checked
for its complete Gram identity. The oracle builds literal operator matrices;
compute scopes use full C/W/C matrices and inspect every dirty row before
projection. The independent required operator is sent explicitly; expected
decisions/oracle annotations and the other executable's results are excluded.
Negative cases cover dead/revived/aliased owners, omitted Unit owners,
effects, injectivity/order, controls, changed functions, dirty cleanup, unsupported
classical/observing inputs and producer caches/flags. Both forms' compatible
scope differences remain tested, including certified uses that change protected
labels or superpositions while returning scratch exactly to zero.

The six source cases compile the actual newly augmented corpus through the
unchanged Rust CLI. Original complete QIRF files are retained in `trace/source-ir/`;
source/compiler/artifact hashes and the derived pure prefixes are in
[current inputs](trace/native-inputs.json). A small untrusted adapter selects the original
straight-line prefix immediately before terminal measurement and lists its
residual owners. Lean then checks that prefix afresh. This is real producer
output checking, not whole observing-root acceptance or source preservation.

The source provenance pins the original corpus sources, bundled library and
manifests separately from the QIRF bytes. These selected QIRF files have empty
embedded-source metadata; the original source files retain their notices.
Katas translations remain MIT; Qualtran and PennyLane translations remain
Apache-2.0. The
[corpus notices](../../../corpus/NOTICE) and
[pinned upstream licenses](../../../corpus/upstream/quantum_katas/LICENSE)
remain required; this packet does not relicense the translated source or IR.

[Current registry/audit replay](trace/registry-validation.json) and
[trace checks](trace/validation.json) record performed commands and source
identities. The earlier [boundary checkpoint](boundary-validation.json) and
root-level reports retain their original source pins. Experimental aggregate work charges raw fields,
maps, whole-space checks and composition; it is not a change to Rust pricing.
The private [codec](../../../lean-kernel/Protocol/Raw.lean) retains original raw
field spellings but is not the complete QIRF decoder. VM-28/29 retain native
packaging, byte-level refinement, fail-closed production dual checking and
execution of the exact accepted artifact. VM-27 retains hierarchy/root closure;
external schemas remain disabled. No version was tagged or published here.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
