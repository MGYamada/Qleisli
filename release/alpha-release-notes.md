# Qleisli v0.3.0-alpha

Qleisli is an experimental language for structured quantum algorithms. This
prerelease is a development snapshot, not completion of the v0.3.0 feature goal
or a stable compatibility promise. The crate version is `0.3.0-alpha`; the
constitutional edition remains `2026`. Source syntax and public Rust APIs
include incompatible changes from 0.2.9; consult the Language Reference and
CHANGELOG for the implemented contracts and migrations.

This snapshot includes the common frontend, explicit classical and quantum
types and ownership, checked operation and Meaning contracts, and independent
native Lean verification. Documentation lives in the single mdBook,
**Qleisli Programming Language**. Separate ecosystem tools are independent
projects and are not part of this crate release.

The Constitution, adopted QS/PR/RS interpretations and exactness supplement
remain in force. Exactly two scoped QLV1 guarantees are admitted: ownership
and classical scope of the original decoded root, under their recorded
premises. Broader QS, PR, quantitative RS and exactness proof/enforcement
obligations remain pending. Native IR acceptance and successful tests do not
establish full source/runtime preservation or constitutional conformance.

Remaining feature Issues, generic QFT and deferred features are not declared
complete by this publication. The approved snapshot scope and human decision
are recorded in Issue #351 and the repository's release records.

OpenQASM 3 / QIR adapters are experimental test features, unsuitable for and
not recommended on real quantum hardware. macOS distribution is under
consideration; this release provides no macOS installation instructions.

The published tag, crate and attached validation assets must identify the same
checked commit. Release validation retains all required jobs, full proof
replay, independent checks, package/fresh-install checks and representative
`--quick` corpus reporting. See the release validation assets for the actual
commit, run/attempt and checksums.

Qleisli Project Contributors. Apache-2.0; historical and third-party notices
remain in LICENSE, NOTICE and the source archive.

Qleisli and its tools are independent projects and are not affiliated with,
endorsed by, or sponsored by the Rust Project or the Rust Foundation. Rust and
Cargo are trademarks of the Rust Foundation.
