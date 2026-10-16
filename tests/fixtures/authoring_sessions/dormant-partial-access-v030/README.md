# Dormant partial-access first history

This informed pre-repair study concerns
[PR #413 review discussion 4289672012](https://github.com/MGYamada/Qleisli/pull/413#discussion_r4289672012).
It preserves all original files from two experiment directories, with unchanged
QLI bytes, predictions, complete actual stdout/stderr, observations and three
initial Rust snapshots. History and anticipated repaired behavior are distinct.

| Packet | Original files | Original bytes | Actual observations |
| --- | ---: | ---: | --- |
| `first-attempts.tar.gz` | 30 | 80,376 | four file-argument failures, then four missing-schema failures |
| `schema2-followup.tar.gz` | 18 | 11,185 | two accepts and two limit refusals |

The first four calls incorrectly supplied `main.qli` as the project argument;
all refused with `Not a directory (os error 20)`. Correcting only that argument
to a directory exposed four `Qargo.toml requires schema-version = 2` failures.
These eight invocation/configuration failures did not exercise the intended
partial-operation access check. Their sources and complete first diagnostics
remain intact, including the initially invalid project manifests.

The separate schema-2 follow-up corrects the project manifests while preserving
all four QLI sources byte for byte. Its actual two accepts and two limit refusals
are the P1 reproducer: unused `then_op(U,power(closed,4096))` and the reversed
composition accepted with `U` unbound. A wholly closed power and an actual
instantiation refused with `static repetition exceeds 1024 steps`. The plans
predict that the same existing Apply capacity gate should also reach the closed
child beside an unbound operation. The observations do not establish that the
repair has been implemented or independently verified.

These sources have zero authored qubits and scalar phase on `Unit`. Their 4096
repeat probes an existing static work limit; it is not a maximum quantum-system
case, an implementation resource bound or a new accepted limit. The accepted
streams report one concrete local and nine bundled roots, 20 native decisions,
zero independent requests, an absent/not-applicable entry and an unpinned checker.
They explicitly report `source preservation: not proved`.

All three observation records identify CLI SHA-256
`fac790a0f1c2805d8f1e6d3f31a86bf15e9c83474bca425b983c167af0b7d6a3`
and kernel SHA-256
`54c9d60b80f67217abd95c8fe6ec1c06aa262e142d5e6db30f46a20cb90faf07`.
Captured HEAD is `61ef86c13c752fe8c6fbb43ac47b757deaf37be7`, with then-dirty
control work. The parent investigation subsequently preserved that work as
local commit `49753079`; this context does not associate that commit with the
recorded executable's build. The three Rust snapshots are partial source
provenance, not complete build inputs. This is not a clean commit-to-binary
build attestation; every observation's `build_attestation` remains false. No
executable is retained.

`packets.json` binds every original file's path, bytes, SHA-256 and mode (`0644`)
and both compressed/expanded archive identities. Canonical USTAR members are
regular files in path-component order, with zero uid/gid/time, empty owner/link
fields and no extensions; gzip uses an empty filename and zero timestamp.
The original 12-file, 21-file and 9-file before/after input windows remain
distinct. The corrected packet's complete 30-file previous-evidence hash map
also binds the initial sources, all eight failures and three Rust snapshots.
The two packets retain 48 originals / 91,561 bytes within the unchanged
aggregate 80-file / 5 MiB expanded / 2 MiB compressed reader limits.

`scripts/test_generic_dormant_first.py` reads the bounded history in memory and
checks all members, windows, identities, outcomes and full stream associations.
It never executes recorded commands. No source/native/runtime preservation proof,
general dormant-obligation discharge, QS/PR/quantitative RS/EXACT discharge,
release claim or issue credit follows; this grants no issue completion.
