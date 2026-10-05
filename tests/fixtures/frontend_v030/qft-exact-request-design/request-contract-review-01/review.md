# Independent review of the frozen first QFT requests

Status: additive, local, non-normative read-only technical review by
`/root/isometry_docs`, separate from request author `/root/isometry_cli_tests`.
No acceptance rule, interpretation, guarantee, std API or Issue status is adopted.
The author supplied the request-file stability barrier before this review.
The inspected 44-file subset is recorded in `inputs.before.json`; this is not
complete source/build/runtime closure or executable authentication.

The four frozen requests are consistent with the existing request grammar and
the retained ordinary #317 contract. No actionable request-definition mismatch
was found. This conclusion concerns the input contract, not its acceptance.
No QFT harness, CLI, native checker, numerical probe or Cargo/Lean build ran
for this review. The separately recorded mandatory constitutional continuity
check passed against `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`.

## Independent mathematical and complete interface requirements

`request-contract.json` fixes
`F_n[y,x] = exp(+2*pi*i*x*y/2^n)/sqrt(2^n)` independently of candidate meanings,
for this experiment's fixed widths 0, 1, 2 and 3. The sign and global phase are
fixed. Axis zero has weight one; actual output reversal is included. No
probability-only comparison, phase quotient or numerical tolerance supplies
this equation. The intended action includes every input and external reference;
the first emission stage checks neither that denotation nor source preservation.

Every JSON request explicitly contains `equation`/`unitary`, entry 0 and one
meaning. Both complete interface sides and the meaning's header are equal:
exactly one quantum port, owner 0, basis `[{"tag":"bits","width":n}]`, ordered
axes `[0,...,n-1]`, and no classical ports. Those values are fixed inputs; they
are not copied from an emitted artifact. Equal physical width cannot replace
the specified basis tree, owner count, ordered axes or complete endpoints.

For widths 1–3, the one meaning is exactly `qft(width=n)`. Rust's strict
`bridge/request.rs::decode_request` selects QLF1 only for the matching singleton
unitary equation; `Protocol.Hierarchical.parseFourier` checks the repeated
complete header. `FourierRoot.checkAll` checks the whole artifact, the actual
recursive body, phase-free entrance and actual reversed suffix, then the
single closed Bits-register boundary. This is the existing bounded named
request, not arbitrary dense-matrix equality or an assertion supplied by a name.

`Protocol.HierarchicalFinite.checkHadamards` fixes `[r,r;r,-r]`,
`r=1/sqrt(2)`, against original finite QIRF bytes. Complete original finite
obligations also remain mandatory. Self-consistent producer descriptions,
provider spelling, returned indices and work counters cannot redefine H.

## Width zero retains its owner and scalar

`n0.json` fixes one `Bits<0>` owner with empty axes and the single rewire
`owners:[0], axes:[], classical:[]`. Its exact scalar requirement is `+1`.
It is not `Q<Unit>`, an empty quantum side, or named `qft(0)`. Both Unit and
Bits0 have zero physical width while retaining different basis constructors;
neither permits silently dropping a quantum owner or erasing scalar phase.

The zero choice was fixed before any first-stage output observation. It is
compatible with the current generic constructor rule: `Root.aligned` compares
complete headers and reference-free constructor data, including this map.
Literal `identity`, `rewire` and a sequence of rewires are different requests.
Rust's graph pairing can reject a child-arity mismatch before native dispatch.
An unexpected original/adapted zero shape must therefore retain its actual
failure; it cannot trigger a replacement request or fallback normalization.
Native named Fourier still rejects width zero and is not widened by this packet.

## Existing mathematical evidence and remaining links

The current proof-only `HierarchicalFourierRoot.inspect_evaluates` derives the
actual physical operator's Fourier matrix from successful actual-root inspection
and the exact equations for every returned H obligation.
`checkAll_unitary` additionally requires every original finite implementation
obligation; `checkAll_reference_laws` derives both inverse laws for the same
operator tensored with an arbitrary finite reference identity. These conditional
analytic/reference results exist and must not be described as absent.

Connecting those premises to the actual native packet/decoder and selected
binary retains its correspondence assumptions and proof gaps. A later fresh
successful native request check binds the supplied payload/request bytes under
that boundary; it does not establish original-source preservation, a general
source-family theorem, quantitative family resources or canonical std exposure.
The current std `qft2`/`qft3` have their original tuple bases. Their relation to
Bits instances requires explicit ordered encodings `a+2*b` and `a+2*b+4*c`,
exact phase/reversal and checked correspondence; equal width is insufficient.

The first-stage contract is four untrusted `emit-proposal` calls only. The
requests are frozen but not passed to a checker. Any later independent request
or mutant decision needs its own fresh native result and exact immutable input
binding, with actual failure stage/native-call count retained. The adapter's
phase-free label handling, complete table closure and body-position preservation
have a separate structure review; this report neither executes nor certifies it.

QS-2026-01, PR-2026-01, quantitative RS-2026-01 and EXACT-2026-01 retain their
pending broader duties. The only admitted guarantees remain ordinary decoded
QLV1 ownership and classical scope, with their original premises and limits.
This review supplies no new admission, proof discharge, #317 completion or
release approval. Historical candidate records remain unchanged.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
