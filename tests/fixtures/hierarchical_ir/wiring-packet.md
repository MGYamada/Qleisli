# Actual hierarchical wiring inspection

Status: component implemented and proved on 2026-09-29; complete outer Fourier
composition remains pending. The existing shared QFT
producer in `scripts/test_hierarchical_qft.py` supplies the actual outer owner
renames and lifted SWAPs. Its desired sized `.qli` source remains preserved in
the earlier shared-QPE authoring packet. This packet introduces no source form
or primitive meaning.

Compute an output-to-input axis list from actual rewire, structural, tensor and
sequence bodies. Process a proposed dependency order from an empty cache; reject
missing dependencies, duplicate definitions, unsupported bodies and width/axis
faults. Charge cache allocation, metadata traversal, route construction and
composition before doing the work, from the budget remaining after the actual
whole-artifact checks. A computed axis summary is not ownership/type evidence;
the existing whole-artifact typing and finite checks remain mandatory.

Prove that successful inspection constructs a derivation over those same actual
definitions, then connect it to the existing physical complex denotation. The
coefficient is exactly one on the computed basis routing and zero elsewhere;
probabilities alone are insufficient. The later outer Fourier bridge must bind
the actual owner renames, recursive body and full reversal to the independently
requested Fourier contract. No named Fourier schema is enabled by a wiring
summary alone.

Validation covers the producer's widths 1–8, identity and empty-owner cases,
shared dependencies, reordered/missing/duplicated schedules, wrong axes and
interfaces, hidden phase/H bodies, and exact/one-short work budgets. Compare
actual circuit action with independently composed basis routes. Preserve first
source and diagnostics; keep runtime source/compiled audits and the existing
structural-work limit unchanged.

The [native record](wiring-native.json) passes 93 outcomes and 2,736 independent
basis/complex vectors. Whole-artifact checking, recursive-body inspection and
wiring together cost 1,931,284 units at width eight. The [registry audit](wiring-registry.json)
rebuilds both packages and independently replays the kernel. The
[runtime-policy record](wiring-runtime-validation.json) records remaining
executed checks; [first attempts](wiring-first/README.md) preserve actual repairs.

Copyright 2026 Masahiko G. Yamada. Apache-2.0.
