# Classical and coherent control diagnostic observations

These four first negative projects isolate the condition or selector in each
control form for [#224](https://github.com/MGYamada/Qleisli/issues/224).
Codex authored them with the [control Reference](../../../../docs/src/reference/source-text.md#exact-label-coherent-selection)
and [type Reference](../../../../docs/src/reference/type-model.md) available.
The cases are informed compiler regressions. No external model took part.

- An ordinary `if` receives a live `Q<Bit>` condition.
- An ordinary `match` receives a live `Q<Choice>` selector with two valid
  enum labels.
- A coherent `qif` receives an ordinary `Bit` condition and a distinct
  quantum target.
- A coherent `qmatch` receives an ordinary `Bit` selector. Its target and
  ordinal arm syntax follow the existing coherent form.

Each project uses edition 2026. The [session](session.json) freezes the first
source and manifest hashes and links the actual JSON and text observations.
The caller supplied the baseline CLI built from the #226 candidate with the
same code as `1b538039d2b499fde0de0ced123c027c5a8fdaf5`. Both binaries'
SHA-256 hashes were verified before and after the calls. These observations
bind the executed bytes and the original diagnostic positions. All four cases
returned `type_mismatch` and exit 1 in both display modes. The first `match`
and `qmatch` diagnostics cover their whole expression, while `if` and `qif`
point at their condition. All command records are inert. No circuit executed.
