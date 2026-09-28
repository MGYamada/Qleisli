# Input corpus and licensing policy

Status: **adopted by the user on 2026-09-28**. This policy governs the
external input corpus under `corpus/`; it does not change Qleisli's language,
trusted acceptance rules, or release gates.

## Closed source set

Only these three upstream projects may supply translated input programs:

| Source | Canonical repository | Selected material | License |
| --- | --- | --- | --- |
| QuantumKatas | [microsoft/QuantumKatas](https://github.com/microsoft/QuantumKatas) | Archived Q# reference implementations | MIT |
| Qualtran Bloqs | [quantumlib/Qualtran](https://github.com/quantumlib/Qualtran) | Selected Bloq implementation files | Apache-2.0 |
| PennyLane Demos | [PennyLaneAI/demos](https://github.com/PennyLaneAI/demos) | Selected demonstration Python files | Apache-2.0 |

This is a closed list, not a recommendation list. Adding or replacing a source,
including moving from the archived QuantumKatas repository to modern QDK
exercises, requires an explicit user-approved amendment to this policy.
PennyLaneAI/qml redirects to PennyLaneAI/demos; that rename is the same source,
not a fourth corpus. Upstream libraries mentioned or imported by these files
are not additional approved sources for copying or translation.

New examples from these three sources must still receive a file-level license
review. Pin their full commit IDs, original paths and SHA-256 hashes in
[the manifest](manifest.json); preserve the reviewed originals. An upstream
update does not silently change the frozen inputs. Mathematical references and
API documentation may inform verification without becoming copied input corpora.
Qleisli-authored harnesses, fixtures and deliberate negative cases are local
verification material, not a fourth external corpus.

## License allocation

- Qleisli's own compiler, standard library, proofs, tests, scripts and original
  documentation remain **Apache-2.0**, unless a file explicitly says otherwise.
  The package license remains `Apache-2.0`.
- QuantumKatas originals and their QLI translations are **MIT**. Retain
  Microsoft's copyright notice and the complete MIT permission/disclaimer text.
  Identify QLI modifications separately; do not replace upstream attribution.
- Qualtran and PennyLane originals and their QLI translations are
  **Apache-2.0**. Ship that license, retain applicable copyright and attribution
  notices, and prominently identify translated/modified files. Retain applicable
  upstream NOTICE material where required.
- Do not mark the entire repository or corpus `Apache-2.0 OR MIT`. In SPDX,
  `OR` grants a choice of licenses; the presence of material under different
  licenses does not itself grant that choice. Any additional terms on our own
  modifications must still preserve obligations attached to upstream material.
- Do not copy images, datasets, website assets, dependencies or separately
  licensed helper files merely because a selected example refers to them.
  PennyLane's README explicitly identifies a BSD-3-Clause exception for
  `custom_directives.py`; that helper is outside this intake.
- A future change to Qleisli's own license is a separate decision and cannot
  erase third-party obligations. This policy does not authorize such a change.

The selected licenses expressly permit modifications and redistribution subject
to their conditions. This intake decision is scoped to the reviewed files and
retained notices; it is not a blanket clearance of every file in an upstream
repository, external patent rights, trademarks, or referenced publications.

## Required translation record

Each example must identify the upstream file and symbol, finite mathematical
contract, QLI implementation, fixed parameters, semantic tests and excluded
features. Record changed bit ordering, observable result encoding and auxiliary
handling explicitly. A narrowed kernel is not a full algorithm port. Successful
QLI checking alone does not establish semantic equivalence to the source.

Preserve initial authoring attempts and real diagnostics. Distinguish analytic
reference tests from execution of upstream frameworks and distinguish finite
numerical validation from proof. Never label these informed translations a
controlled model benchmark.

## Primary permission records

The pinned originals are distributed with their licenses:
[QuantumKatas MIT](upstream/quantum_katas/LICENSE),
[Qualtran Apache-2.0](upstream/qualtran/LICENSE), and
[PennyLane Apache-2.0](upstream/pennylane_demos/LICENSE).
The pinned [PennyLane README](upstream/pennylane_demos/README.txt) explicitly
covers its demonstrations and identifies its helper exception.
[SPDX license expressions](https://spdx.github.io/spdx-spec/v2.3/SPDX-license-expressions/)
define the distinction between alternative licenses and multiple obligations.
