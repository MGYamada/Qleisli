# Observing function contract boundary

The four unchanged first projects and [context](context.md) were frozen before
the observations in [session.json](session.json). All selected checks use the
same explicitly identified CLI and native checker.

| Project | Actual selected Raw result |
| --- | --- |
| `control` | Checks with `request_origin: none` and `source_meaning_verified: false`. |
| `pure-reference` | Rejects: expected `Q<Bit>`, found `Bit`. This is a result-type refusal, not proof that all later effect conditions were checked. |
| `contract-readout` | Rejects: operation provider requires `Q<A> -> Q<A>` with one exact quantum input. |
| `contract-residual` | Rejects at the same provider requirement; the desired residual-channel inequality has not reached a public native contract gate. |

The frozen context called the last example “parity-readout”; more precisely it
is nondestructive Z readout of one data bit using a fresh copied ancilla. The
first context and source bytes remain unchanged.

The separate [native experiment](native-experiment.json) retains eight exact
CP comparisons and complete histories for thirteen original programs. All
thirteen match the existing independent host oracle. The same-probability
residual replacement and I/Z channel pairs have equal outcome POVM effects
but different Choi coefficients. Hidden Kraus basis changes, split histories
and impossible zero outcomes preserve the corresponding maps. The driver is
freshly compiled against Lean 4.30.0; no maximum-size case or Rust acceptance
result is generated or reused.

The [experimental packet](../../../../experimental/instrument-meaning/proposal.md)
was a candidate when these observations were captured. The human maintainer
[subsequently adopted its exact design](https://github.com/MGYamada/Qleisli/issues/46#issuecomment-6104666552);
the packet's historical notice is preserved. The separate
[ordinary source integration record](../../../../experimental/instrument-meaning/finite-source-validation.json)
now covers private original-artifact evidence and fresh concrete call checks.
Explicit specialization and its source replay remain pending. The original
observations above describe the earlier selected Raw boundary and are unchanged.
This first study changes no public behavior,
schema, dependency version, protected record or proof status. Pure Meaning
retains exact operator phase. Native history reconstruction, experimental CP
comparison, source preservation and human specification adequacy remain
separate judgments. Issue #46 is not complete.
