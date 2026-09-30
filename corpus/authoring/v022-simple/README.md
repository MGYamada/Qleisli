# Simple finite corpus authoring, 0.2.2

The user requested simple corpus augmentation first on 2026-09-30.
Six new 1–3-qubit projects were saved before checking, reusing only the existing
three frozen upstream sources. The known tuple/control/rotation workarounds
were available. This was informed authoring, not a controlled model benchmark.

[Session](session.json) records the baseline and complete source hashes.
[Initial diagnostics](check-initial.json) preserve all six actual successful
checks; no source repairs were performed. [Semantic validation](semantic-validation.json)
selects the six new results from the [complete 36-case run](../../validation-v0.2.2.json):
290 semantic probes covering every complex entry, all six shipped mains and six detected
type-correct faults. The complete run also checks four ownership/effect rejection
fixtures. Compiler, oracle, manifest and source hashes are recorded in the reports.

SWAP/Fredkin test owner/axis order and coherent control; constant XOR/complement
test exact bit ordering and whole-space permutation; RX/kickback test scalar
phase and the explicitly narrowed one-bit secret. Numerical tolerance is 1e-11,
not evidence for exact semantic contracts or a general soundness theorem.
Upstream frameworks are not executed; no maximum-size corpus cases are generated.
Historical sessions, upstream pins and prior validation reports are unchanged.
