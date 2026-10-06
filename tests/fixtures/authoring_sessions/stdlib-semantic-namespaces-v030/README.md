# Semantic namespace first observations

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.

This informed source study preserves four complete desired/control projects
before the #317 namespace migration. Five `.qli` inputs and four edition-2026
manifests remain unchanged. Generic QFT is excluded; no generic-QFT client,
implementation or proof is introduced here.

| Project | Actual first finite CLI check |
| --- | --- |
| `transform` | Exit 1: missing module `std::transform` |
| `reflection` | Exit 1: missing module `std::reflection` |
| `measurement` | Exit 1: missing module `std::measurement` |
| `demo-local-arithmetic` | Exit 0: ordinary project check passed |

[The actual capture](observations-before/capture.json) and its raw stdout/stderr
are unchanged. [The registered session](session.json) links four normalized
events containing the actual argv, exit and parsed retained stdout. Their UTC
fields identify the later recording time; the original capture supplied no
execution timestamp. [Pending metadata](session.pending.json) and
[pre-check context](context.md) remain the exact earlier unexecuted snapshot,
not a claim that these later observations never happened.

The observed CLI SHA-256 is
`ab944ab6f1bc7342ec1dedeea5b6350d1b0e5cdc8c487d9ef1ba3dc08022c094`;
the selected native SHA-256 is
`39effde0f152a2c926fcea3a7f99fc2f25f9de65906be2b8c527508353c90c85`.
The recorded HEAD is `7f6529ef93838d565552c3f501ce016ef1d1d2b4`, but this CLI
includes the reviewed uncommitted empty-pattern diagnostic repair captured by
the root observer. HEAD alone therefore does not identify its full compiled
source state. The retained attempt hashes bind the observed client sources;
none of these records is a complete compiler/runtime closure or independent
native compilation attestation.

The three missing-module diagnostics are real first failures, not downstream
type/effect/owner tests. Local arithmetic success exercises preserved A001-A003
bodies through ordinary project checking with the selected native boundary; it
does not establish their full complex permutations, run or sample output,
reference semantics, general-size arithmetic or retirement of old std exports.
No semantic oracle, mathematical proof, guarantee or Issue completion follows.
No stored command was replayed during registration.

## Results after the namespace migration

The four unchanged projects were actually checked against the migrated source;
all four checks passed. [The later capture](observations-after-01/capture.json)
preserves their commands, outputs and identities separately. The registered
session now links the four first events and four later events; it preserves all
first sources, raw failures and earlier pending metadata.

The later CLI SHA-256 is
`424f8c5cf4dbbccccfa18f35a4535de881e448811d5b3c1f5021acc4976e0684`.
Following a final Fourier-only comment correction in the embedded transform
module, the CLI was rebuilt (SHA-256
`a7c2b2d387dc0c3ae360b047ff433abb7e341cc21c8a9aefbfe8b5056c791ae8`)
and all four projects passed again. That distinct source state is recorded in
`tests/fixtures/frontend_v030/stdlib-semantic-namespaces/implementation-01/post-comment-validation-03.json`.
These observations establish successful ordinary checking at the selected
native boundary, not a general semantic theorem, constitutional discharge or
release approval. Independent bounded semantic checks have their own records.
