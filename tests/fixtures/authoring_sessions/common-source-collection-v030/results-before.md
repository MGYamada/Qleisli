# Actual pre-code source-collection results

All [23 original command observations](before/summary.json) are preserved before
production changes. There are five successful commands and eighteen real
rejections. No source repair, substitute failure or quantum execution is used.

| First project | Actual checks and proposal emission |
| --- | --- |
| Ordinary finite main importing bundled `std::transforms::qft2` | Text/JSON checks pass; 22 actual native invocations each. No finite artifact is labelled an untrusted proposal. |
| Two local sized modules with a private helper sibling | Text/JSON checks pass with one native invocation each. Exact untrusted proposal emits with zero native invocations. |
| Never-called invalid sibling | `ownership`: `unbound or consumed value q`; zero native invocations. |
| External import of a private helper | `visibility`: `dependency helper::local is private`; zero native invocations. |
| Unsupported sized basis declaration | `unsupported`: `sized preparation profile: requires an ordinary function`; zero native invocations. |
| Earlier unsupported basis, later malformed module | The earlier `a_basis` profile rejection wins at bytes 75–110; zero native invocations. |
| Earlier malformed module, later unsupported basis | `parse` on `a_malformed` at EOF bytes 114–114; zero native invocations. |
| Reserved `std::injected` module-map injection | `module`: `invalid module path`; zero native invocations. |

Each selected negative retains text/JSON check output and a real rejected
`emit-proposal` command; none creates an output proposal. Error-stage ordering
is observable compatibility evidence, not a claim that these errors are
interchangeable.

The helper's [exact untrusted proposal](before/local-helper-private-emit-proposal-json.proposal.json)
has 16,831 bytes and SHA-256
`25eea53f22c07a944a1043b816e7744a6d5ee8365ca0727ce50a660e2f4f1deb`.
Its successful checks explicitly report `producer-consistency` and
`source_meaning_verified: false`. The finite command reports verified produced
IR; neither route establishes general source preservation or a Fourier theorem.

[Frozen identity](identity-before.json) captures local record-only HEAD
`5aee1b3cfde51e347cbff83c76526d22cf249d33`. The parent separately identifies
compiled production commit `238e1f0869c96c8da18f215a4569dd68e2cc98b9` and earlier
record commit `9256fe9ef4ffa722066b0569ee37341cf65dea0d`.
CLI SHA-256 is
`a2755f3c13068f30f92d92d12d88a4b81a8ae7c0fbd69374aed632e3fb23bacc`;
native checker SHA-256 is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
Original sources/manifests, current production Rust, Lean-kernel, stdlib,
contracts and executables remain unchanged through every before invocation.
These identities do not attest compilation of the record-only HEAD.

All provided systems have at most two physical qubits. Existing finite public
checking necessarily traverses all unchanged bundled declarations, including
the retained four-bit arithmetic implementation; no new larger source, maximum
case or simulation is performed.

After root authorization and the new CLI build, `replay.py after-final` may
create a separate capture. Its fixed commands use these same source paths,
record new code/CLI identities and compare exact stdout/stderr/exits, native
call counts and proposal bytes. Differences, including diagnostic ordering,
remain explicit review inputs rather than automatic compatibility approval.
The before capture and frozen source/context/driver bytes must remain intact.
The separate wrapper verifies the exact completed baseline map and all original
input/output identities before and after executing the unchanged capture driver.

This is private collection and loader/profile evidence. Canonical generic QFT
exposure, checker convergence, source preservation, independent semantic
requests and broader QS/PR/RS/EXACT guarantees remain separate requirements.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
