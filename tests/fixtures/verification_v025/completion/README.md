# VM-25 straight-line pure completion

The eleven straight-line pure RawOp constructors now have actual executable
checking/extraction proofs, independent complex denotation and both clean-release
laws. Rust remains production-authoritative. Classical branches/observation are
VM-26; hierarchy closure, transport/packaging and production dual integration
remain VM-27–29. This packet neither publishes 0.2.5 nor completes S05 soundness,
source preservation, shared-QPE correspondence or the three v1 theorem goals.

## Executable boundary and independent meanings

[Pure.verify/inspect](../../../../lean-kernel/QleisliKernel/Raw/Pure.lean) check
original raw ports, operations, effects and final owners. The structural checker
retains twelve-bit registers, global token/wire freshness and zero-width owners.
General checking allocates no global dense matrix. Broad CertifiedCompute uses
the existing local five-data-plus-one-auxiliary profile; protected scopes keep
original uses and the twelve-bit structural capacities.

[Protected coefficient evaluation](../../../../lean-kernel/QleisliKernel/Raw/ProtectedEvaluation.lean)
evaluates original gates/phases on source-selected amplitudes. Its
[actual-definition proof](../../../../lean/Qleisli/RawProtectedEvaluation.lean)
binds every result to the original physical C/use/C coefficients. Function
matrices use the logical data width, so auxiliary metadata cannot impose an
extra six-bit combined-width restriction. Every amplitude evaluation is charged
before traversal; this private accounting remains distinct from Rust prices.

[Original-trace refinement](../../../../lean-kernel/QleisliKernel/Raw/Trace.lean)
proves every actual constructor, original input interface and final output
permutation agrees with the independent data-only reader. The independent
[complex raw action](../../../../lean/Qleisli/Semantics/RawAction.lean) supplies
literal gate, phase, control, dependency, lift, permutation and physical computed
actions. [Actual pure acceptance](../../../../lean/Qleisli/RawPure.lean) preserves
that complete action and discharges every clean-scope obligation. The bounded
[denotation proof](../../../../lean/Qleisli/RawDenotation.lean) additionally binds
the actual reconstructed matrix to complete literal complex circuit traces,
physical C/use/C bodies and phase-exact matrix composition. Reference meanings
import only data/independent semantics and Mathlib, never acceptance or transport.
Specification review remains distinct from implementation conformance.

[Non-dense protected semantics](../../../../lean/Qleisli/Semantics/Protected.lean)
retain separate source, auxiliary, target and arbitrary reference coordinates.
Actual dispatch's Z/T restriction yields exact
`C_f ; original uses ; C_f = zero ∘ logical action` on the zero-auxiliary image.
Every dirty auxiliary amplitude vanishes, including correlated inputs. No
product-state assumption, truth-table matrix expansion, discarded dirty state
or producer clean flag is used. The [actual dispatch bridge](../../../../lean/Qleisli/RawProtected.lean)
connects this law to the original checked constructor. Broad certified uses may
change protected labels/superpositions; their independent finite physical
equation remains mandatory.

## Retained graph and binding

[Function.checkAll](../../../../lean-kernel/QleisliKernel/Raw/Function.lean)
starts from an empty receipt list, reconstructs both original bodies and compares
full matrices including phase. Each call can use only the freshly checked
prefix. Separate required attachments bind the complete signature tree, both
raw bodies, implementation/specification names and exact source names/text.
The original three-field raw evidence API remains available.

Published limits are checked: 4,096 UTF-8 bytes per identity/source name,
128 uniquely named sources, 1,048,576 total identity/source bytes, depth 32,
1,024 literal steps and 1,000,000 dependency-expanded steps. Empty source names
remain allowed; implementation/specification names remain nonempty. Both bodies
are preflighted and expansion-counted without constructing a recursively expanded
DAG. Original protected extraction, output permutations and empty-body cost one
remain represented. [Counting proofs](../../../../lean-kernel/QleisliKernel/Raw/Function.lean)
relate actual bounded execution to an independent literal accounting definition.
[Fresh graph proofs](../../../../lean/Qleisli/RawFunction.lean) establish every
body's original denotation, full-space inverse equations, retained inputs,
separate binding equality and expanded capacities. Source attachment equality
does not prove source-to-IR preservation. Private transport accounting is still
experimental and does not change public Rust prices or failure behavior.

## Reproduction and scope

Run `python3 scripts/test_lean_raw_completion.py --record /tmp/vm25-completion.json`.
[Completion comparisons](native-completion.json) pass **146 native cases,
31 Rust comparisons and 79 independent matrices**, including exact source/body
faults, unchanged-matrix mutations, UTF-8 limits, depth 32/33, expanded cost
524,288/1,048,576, literal steps 1,024/1,025 and original protected H/X behavior.
Auxiliary metadata limits, a two-bit H action and the exact phase selected by a
high auxiliary bit are also checked without evaluating any wide auxiliary state.
Missing/self/forward dependencies and producer flags/caches are Lean-only
negatives: public Rust receipts cannot be forged from unresolved indices.

Run `python3 scripts/test_lean_raw.py --record /tmp/vm25-raw.json`.
[Original-body replay](native-validation.json) passes **121 cases, 104 Rust
comparisons, 85 independent rational matrices and 180 original-trace comparisons**,
including six actual corpus source prefixes. [Original QIRF files](source-ir/0.qirf.json)
and [input/provenance records](native-inputs.json) retain their source identities
and third-party notices. Semantic comparisons use at most three qubits; wide
cases inspect metadata only. No maximum-size corpus is generated or claimed.

[Final validation](validation.json) binds source files, reports and binaries.
[Registry replay](registry-validation.json) rebuilds both packages, audits all
compiled project declarations by origin and freshly checks the kernel. Existing
public Lean types and native transport are compared against the pre-refactor
baseline; external schemas remain disabled. Earlier root and [trace checkpoint](../trace/README.md)
reports retain their original hashes and describe their historical scope.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
