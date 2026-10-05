# Actual bounded QFT observations

The untouched [first translation](attempt-01/transform.qli) passes all eight
initial check commands: widths 0, 1, 2 and 3, each in text and JSON. Each command
invokes the actual native checker once. No generic check failure occurred and
none is fabricated. Ordinary `pub fn` is used; the resulting checked profile is
`sized-unitary`. JSON explicitly retains `producer-consistency` and
`source_meaning_verified: false`.

The separate [follow-up](attempt-02/reference.qli) adds reference clients after
those observations. Its copied QFT source is byte-identical to attempt 01:
SHA-256 `12753179c20a3a45bb8420e5a4c6a41157b493dcf3f47314b4f41658b4644cfc`.
All four reference-client checks pass before execution. Fifteen complete basis
columns at widths 0–3 and four coherent/reference probes agree with the analytic
positive Fourier expectations. Maximum complex coefficient error is
`1.3743915342634358e-15`, below the declared numerical comparison threshold
`1e-11`; [the summary](small-probes/summary.json) retains the bounded counts.

The three positive-width reference clients transform one half of a Bell pair
while retaining the other owner. The zero-width client retains a scalar-bearing
`Q<Bits<0>>` beside a coherent complex reference. Its two output coefficients
are approximately `(0.5, 0.5)` and `(-0.5, 0.5)`, agreeing with the independently specified
`omega/sqrt(2)` and `i*omega/sqrt(2)`. No native named `.qft` request at width zero
is made; all 31 source check/run observations use the existing native composition
request mode exactly once.

The fixed drivers preserve each command, original stdout/stderr, native argument
log, completed observation time and independently expected coefficient vector.
CLI SHA-256 is
`a2755f3c13068f30f92d92d12d88a4b81a8ae7c0fbd69374aed632e3fb23bacc`;
native checker SHA-256 is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
Both identities and the parent bounded 200-file source map remain unchanged
before and after every observation. [Identity](identity-before.json) records
baseline commit `238e1f0869c96c8da18f215a4569dd68e2cc98b9`, the pinned licensed
translation provenance, additional current stdlib hashes and the compilation
identity limitations.

These are local-module authoring and numerical corroboration results. They do
not expose canonical `std::transform::qft`, prove exact fixed QFT2/3 equivalence,
bind an independently named Fourier request, prove general-size source
preservation or admit a constitutional guarantee. Mathematical family identity,
static-family resource certificates, shared project loading/checking and full
QS/PR/RS/EXACT duties retain their separate required evidence. No Rust, Lean,
stdlib or corpus runtime source is changed and no new build or maximum-width
case is executed.

All basis and reference probes use unit-norm inputs. These observations alone
do not establish behavior for arbitrary unnormalized input vectors. The
[independent-review record](independent-review.json) transcribes findings
received through the root agent; creating that record performs no fresh CLI
execution and does not provide a new proof or human constitutional judgment.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
