# First finite request-binding attempt

`Finite.lean.txt` was saved before the first `lake build
QleisliKernel.Hierarchical.Finite`. That build failed on 2026-09-29:

* `input.basis` and `output.basis` needed explicit `QuantumPort` types in the
  optional-array lookup block.
* `split` selected inner matches before reducing the cost `let` bindings in
  `inspect_conditions`; its `contradiction` branches therefore still contained
  conditional computations. The repair reduces those bindings first.
* `beq_iff_eq` lacked the derived lawful Boolean-equality instances for the
  exact artifact interface and rule types. These instances are proved by
  ordinary deriving, with no native evaluation or proof admission.

These are compilation diagnostics, not semantic counterexamples. The request
still represents an opaque reconstruction obligation, not a successful finite
equation. The native harness and its first executed result are recorded
separately.

The saved `harness.py.txt` precedes its first run. That initial native build and
execution passed all 67 comparisons, with 29 pending requests and 1,727 complete
field/byte probes. The harness deliberately sends opaque program and meaning
bytes: every pending case still rejects in the ordinary semantic rule checker.
It does not claim these payloads are valid QIRF or exact matrices.

A helper-suite invocation during the scheduled registry rebuild correctly
rejected the not-yet-refreshed source manifest. After `--write` completed its
builds/audits/replay, the 37 document/schema/authoring helpers passed. The 17
runtime source-policy tests also passed with their compiled checks enabled.
