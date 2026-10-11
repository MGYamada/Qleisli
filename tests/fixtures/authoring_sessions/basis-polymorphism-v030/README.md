# Opaque Basis first-source experiment (#44)

This is an informed desired-source experiment, not a model benchmark or a
completed generic feature. [Context](context.md) and `first-files.json` predate
the first invocation. Nine complete edition-2026 projects are frozen in
`attempt-01`; `baseline/driver.py.txt` preserves the actual observer, including
its incorrect expectation that the concrete control would already pass.

All nine first probes reject at parsing with zero native invocations. The
concrete Nat/Op control omitted the mandatory static-fold `yield`. Its actual
diagnostic and the failed observer expectation are retained. The second full
snapshot adds `yield` to that control and the opaque-repeat draft; the other
seven sources are unchanged. `second-files.json` was saved before observation.
All eight abstract forms still reject at parsing. The repaired concrete control
passes with exactly one fresh native invocation. First-source bytes and actual
observations are never replaced by that repair.

Missing Apply, owner duplication, undeclared/forward Basis parameters and an
assumed decomposition/preparation are desired later rejection cases. Their
current parser failures do not exercise those later rules. Forwarding and
bounded repetition are desired positive cases, without a claim that they work
for abstract bases yet. A future specialization must retain exact Unit, Bit,
Bits and tuple trees, phase, axis order, owner/effect obligations and provider
dependencies. Same width does not supply a type identity or coherence map.

The existing kernel is reused; its exact digest, each observed CLI digest,
unchanged wrapper arguments, raw output and native counts are recorded. The
MSRV build between batches changes the CLI digest; the observed source/grammar
is unchanged. These checks do not rebuild Lean, establish source preservation,
admit a constitutional guarantee or close #44/#27/#43.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

## Later implementation observations

The ten appended `implementation/` probes reuse unchanged `attempt-02` source.
Six abstract negatives now reach their actual generic type, access or ownership
rule without a native invocation. The concrete control and the same opaque
repeat body at `Bit` and `Bits<1>` each pass with one native invocation.
Explicit command inputs supply type bindings; these are not inferred from width.

The first opaque-forward follow-up fails at project admission: its additional
provider manifest incorrectly used `schema` rather than `schema-version`.
The observer's positive expectation was premature; its failed assertion,
actual output, inputs and original provider bytes remain in `implementation/`.
The historical result's scope text describes the intended outcomes; the recorded
rows and this correction state the actual outcomes. Only the provider manifest
is repaired. `implementation-provider-repaired/` retains the succeeding run and
its one native invocation; the original client's source remains unchanged.

The additional provider has a separate `B` parameter and explicit own binding.
These observations establish no general source or specialization theorem.
Independent small complex-reference and Unit-phase tests live in
`tests/basis_polymorphism.rs`; #44 remains open for Meaning integration and
its complete acceptance criteria. No fresh Lean replay or guarantee is claimed.
