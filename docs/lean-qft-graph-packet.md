# Typed shared QFT circuit binding

Status: **implemented with actual-checker and Fourier/reference proofs**, 2026-09-29. This continues the
[actual QFT circuit proof](lean-qft-proof-packet.md) toward the adopted hierarchy;
it introduces no additional external artifact format or enabled schema ID.

The retained [desired shared source](../tests/fixtures/authoring_sessions/shared-qpe-v020/attempt-01/estimation.qli)
and [finite QFT round trip and semantic fault](../tests/fixtures/lean_qft/README.md)
remain the program-first evidence. The obligation is to bind the proven literal
gate pattern to actual typed shared dependencies, rather than accepting a detached
gate-list witness or the name of a source function.

## Internal checked projection

Use a bounded DAG of whole-register unitary circuit fragments. Every fragment
has explicit quantum input/output type trees and ordered axes, classical
input/output slots and effect. For this QFT projection the quantum interface is
exactly one `Bits(m)` owner with local axes `0..m-1`; classical slots are empty
and effect is unitary. Equal widths do not identify a tuple, nested tuple, Bit
or missing/extra zero-width owner with that interface. A call has explicit
complete input/output interfaces that must agree with its actual callee.

Bodies are an identity, a literal H/diagonal gate, ordered binary composition,
a shared call, or an explicit final data-axis permutation. The permutation is a physical
circuit action on the register's ordered basis bits, not a renaming of ownership
metadata. Do not use a pure `Layout.PortsMatch` renaming as evidence that a data
permutation was executed. A later external importer must establish this
projection from actual finite gates, dyadic/control nodes and checked swaps or
rewires, preserving all type and dependency identities. That importer must
retain the original control/target roles: a symmetric two-axis phase polynomial
alone does not establish those structural roles from the external nodes.

Evaluate each definition once. A bounded summary retains literal gates in
execution order and at most one terminal permutation. Reject a gate or another
permutation after that terminal operation. Calls retain the referenced summary;
composition checks the actual children and their full boundary. This restricted
projection suffices for the selected QFT template. It is not the general
hierarchy's normal form and must not expand arbitrary repetitions into words.

Cap each summary at 36 gates, the graph at 256 definitions, depth at 64 and
references at 4096. Conservatively charge concatenated gate entries and reject
before concatenation. Calls reuse their cached summaries without copying gates.
Reject forward, cyclic, missing and unreachable definitions. Independently
requested width determines the entire typed interface and positive QFT meaning.
The actual root summary must pass the proved matcher, including final reversal.

## Required evidence and experiment

Prove cached graph evaluation agrees with a separate literal operational graph
interpretation that does not read summaries. Then prove actual acceptance binds
the complete type/effect/port boundary and the Fourier theorem's exact gate word
and final permutation. The separate complex proof must transfer the Fourier
coefficient theorem through this accepted graph projection.

Generate native positive graphs at widths 1–8 with shared calls and ordered
composition. Pair them with type-correct changed dependencies, phase signs,
call maps, final permutations and order, plus malformed types, effects, axes,
cycles, dead nodes and limits. Check arbitrary fixed path choices independently
and retain the existing finite-source Fourier counterexample. Report stored
nodes, references, copied gates and path checks separately; verification dense
dimension stays zero. Record first Lean implementation and actual diagnostics.

This projection does not yet prove a transport decoder, the full external IR
projection, general gate graphs, source lowering or native compilation. The
external `qft-dyadic8/1` registry stays disabled until its complete manifest,
actual-IR binding and fresh-process mutation gates are implemented.

## Completed checking and proof boundary

The actual [runtime checker](../lean-kernel/QleisliKernel/QftGraph.lean) proves
`compose_sound`, `evalNode_sound` and `evaluateFrom_sound` against direct literal
path execution. `check_sound` binds that operational graph to the computed
summary and existing QFT matcher. `check_signature` establishes every accepted
definition's exact interface/effect; `check_action` fixes the final reversal.
The separate [complex theorem](../lean/Qleisli/QftGraph.lean) defines coefficients
from the direct graph action and proves `check_fourier` and `check_reference`.
They do not merely attach a named QFT meaning to a detached receipt.

The [native experiment](../scripts/test_lean_qft_graph.py) passes 68 decisions
(28 accept, 40 reject) and 744 independently interpreted literal paths. Four
semantic mutations pass graph preflight, metadata validation and word evaluation,
then fail the Fourier matcher. Depth 64 and 256 definitions accept; 65 and 257
reject. A 170-node shared graph represents 2^59+37 literal actions while checking
228 references and charging 773 gate entries, at depth 62. That large case is
verified without executing its expanded action. No dense matrix is constructed.
See the [retained record](../tests/fixtures/lean_qft_graph/README.md).

Only the internal QFT projection is accepted here. Identity call adapters and
one canonical `Bits(m)` owner are deliberate restrictions of this projection;
general port adapters, effects and hierarchy constructors remain future work.
No existing finite API or experimental wire format was broadened or removed.

## Whole-space unitary consequence

The subsequent [QFT unitary proof](../lean/Qleisli/QftUnitary.lean) establishes
`F†F = FF† = I` for the actual accepted graph coefficient matrix. It uses finite
character orthogonality, normalization and the proved little-endian index
bijection. The actual matrix is equated to the mathematical Fourier matrix by
`check_fourier`; unitarity is not assumed from a declared effect or a QFT name.
No dense matrix is constructed by the runtime checker. The
[QPE continuation record](../tests/fixtures/lean_qpe_instrument/README.md#completeness-continuation-2026-09-29)
retains its first attempt, diagnostics, final build and axiom audit. This supplies
an inverse/control premise for later bound schemas; external IR extraction and
execution-transform correspondence remain separate obligations.
