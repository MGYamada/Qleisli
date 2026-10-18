# Qrates, source identity and external artifacts

This chapter specifies the package and artifact authority boundary for
0.3.0-beta in constitutional edition 2026. It applies the existing decisions in
[#169](https://github.com/MGYamada/Qleisli/issues/169),
[#170](https://github.com/MGYamada/Qleisli/issues/170),
[#172](https://github.com/MGYamada/Qleisli/issues/172),
[#173](https://github.com/MGYamada/Qleisli/issues/173),
[#174](https://github.com/MGYamada/Qleisli/issues/174) and
[#171](https://github.com/MGYamada/Qleisli/issues/171), under the
[authority hierarchy](authority.md). It introduces no registry, dependency
solver, feature system, build hook, foreign-execution API or accepted-handle
format. The [current adapter limits](#current-adapter-and-remaining-binding-gaps)
remain explicit. These rules neither admit a new constitutional interpretation
nor discharge the pending broader QS, PR, RS or EXACT obligations.

## Source and the five artifact roles

The language/kernel and accepted ordinary `.qli` define executable Qleisli
meaning. A bundled, user-authored or generated definition receives the same
applicable source and independent native checks. Its origin supplies no
primitive, ownership, effect, inverse/control or Meaning privilege. The
[primitive boundary](primitive-boundary.md) answers which meanings require
language rules; this chapter answers which artifacts may claim each role.

| Role | What it may establish or select | What it cannot authorize by itself |
| --- | --- | --- |
| Semantic | The normative language/kernel and accepted `.qli` define the requested computation, types, owners, effects and specified contracts. | A source name or annotation cannot manufacture the required evidence or waive a failed check. |
| Evidence | Checked Lean proofs, certificates and verifier decisions establish their stated claims about exact subjects under recorded premises. | They cannot redefine the source denotation, silently strengthen a contract or replace a missing source/target correspondence. |
| Observation | QLT, QDB, QCP, diagnostics, simulations and analyses report bounded denotation, behavior or cost under explicit profiles. | A test pass, resource estimate or diagnosis cannot issue production acceptance or trusted Meaning evidence. |
| Realization | Target profiles, decompositions, routing and associated evidence describe or justify implementation on a selected target. | A native gate set, recognizer or successful synthesis cannot change logical source meaning or supply an absent resource bound. |
| Organization | Qrate manifests, dependency/build records, package provenance and documentation organize and identify inputs/artifacts. | Packaging, a hash, version equality or prose cannot install a semantic rule or certify a program. |

A file may contain several roles; classification follows the actual claim,
not its extension or distribution origin. Documentation tooling must distinguish
prose, machine-readable declarations, requested contracts, test observations and
checked evidence. A doc comment saying “exact Fourier transform” is not a
Fourier equation or proof. Removing an external proof may remove required
acceptance evidence; it cannot change the declared program's denotation.

QLT is an external observational/testing surface. Its permitted bounded
amplitude or cost inspection does not become a `.qli` primitive for inspecting
live coherent state or a program's own denotation. QDB/QCP and other analyses
cannot upgrade acceptance. These tools retain their own implementation scope;
listing their roles does not make them available.

Generated `.qli` or typed program structure must undergo ordinary checking.
The preferred future in-language generator is the typed static/meta layer in
[#60](https://github.com/MGYamada/Qleisli/issues/60) and
[#61](https://github.com/MGYamada/Qleisli/issues/61); the current
[bounded static fragment](static-language.md) does not implement that general
system. A meta expansion cannot inspect live quantum state, inject trusted IR
or escape the original source/effect/evidence obligations.

Serialized Core/IR, caches and generated artifacts are derivative. A supported
artifact path must bind its actual source/context where a source claim is made,
and obtain the applicable fresh independent check. Valid output IR alone does
not prove source preservation. Optimizers and backend intrinsics implement an
existing requested meaning; recognizing a pattern cannot decide what the source
means. Actual output, phase, axis order, workspace, references and resources
retain the [realization](realization.md) and
[production-boundary](production-boundary.md) obligations.

## Qrate, module and file

A **qrate** is the smallest independently versioned and distributable unit of
Qleisli programs. It may contain ordinary source, documentation, tests/QLT,
proofs, resource metadata and explicitly permitted build artifacts. Bundling any
of them confers no extra authority. A qrate may depend on other qrates; it cannot
extend, weaken or bypass the language semantics or the required verifier gates.

A **module** is a canonical namespace and visibility unit. A **file** stores
source. A qrate owns its package/version/public-API boundary; the language's
module and declared visibility rules determine access. Filesystem directories
never grant additional public, private, qrate-local or semantic permissions.
This defines the concepts, not new visibility modifiers.
Module/import ergonomics in [#65](https://github.com/MGYamada/Qleisli/issues/65)
must preserve the qrate contract in [#170](https://github.com/MGYamada/Qleisli/issues/170)
and these canonical-identity distinctions in
[#172](https://github.com/MGYamada/Qleisli/issues/172); that frontend work does not
implement qrate dependency resolution.

The qargo tool manages, obtains, resolves, checks and records qrates according
to this contract; its behavior does not define what a qrate means. Registry, installer,
solver, lockfile syntax, duplicate-version and dependency-cycle policies require
their own supported package specification. The current module-import rules are
not a completed qrate dependency model.

Distinguish these identities:

| Identity | Required distinction |
| --- | --- |
| Logical package | Qrate name and package version, with declared edition/toolchain compatibility. Equal names/versions alone do not identify selected content. |
| Canonical declaration | Qrate identity, canonical module path and declaration identity; a resolved context selects the actual package instance. Absolute paths, line numbers and temporary generation names are diagnostic/storage coordinates. |
| Resolved program instance | The selected source and dependency closure, relevant configuration/static actuals, requested edition, toolchain/canonical-std pair and declared generation inputs. Required profiles/evidence additionally bind the actual artifact and checker. |
| Distribution artifact | The exact package/archive bytes and their provenance. Archive layout and content hashes identify a distribution; they do not define a declaration's mathematical meaning. |

These are normative identity inputs, not new source types, a stabilized hash
algorithm or a claim that a current artifact schema already carries them all.
Dependency selection must be explicit or deterministically implied by the
selected toolchain. A supported locked graph must record the immutable selected
instances and reconstruct the same source/program selection. Ambiguous or
unsupported dependency/version policy cannot be inferred from Cargo conventions.

Moving unchanged source while preserving its canonical qrate/module/declaration
identity does not rename the declaration or change its denotation. A packaging
layout move may change archive bytes and provenance without changing that
canonical name. Moving from canonical `algebra::operation` to
`transforms::operation` changes the namespace. The distinction also applies to
generated files: a temporary directory is not a new semantic identity.

Evidence and caches must distinguish canonical program identity from storage
locations while binding actual source/dependency/artifact bytes and exact
interfaces. Stable names or equal widths do not authorize evidence substitution.
A storage move alone supplies neither a new proof nor permission to rebind an
accepted handle. Changed checked subjects or representations require their
applicable fresh checks and preservation/transport support. This chapter proves
no general relocation or source-preservation theorem.

The existing filesystem convention maps `src/algebra.qli` to `algebra` when
`src` is the selected root; nested relative components form nested module names.
That is a frontend mapping convention. The resulting module name participates
in identity; the absolute source path remains provenance. The existing explicit
binding form makes the distinction visible:

```text
--module=algebra=/first/storage.qli --entry=algebra::operation
--module=algebra=/second/location.qli --entry=algebra::operation
```

Each file's ordinary source tree must separately satisfy the explicit manifest
edition check. With the same checked source/context, both options request the
same module/declaration name; paths locate different storage. These are
supported CLI option forms, not full commands or evidence that the two
compilations have been compared. General cross-qrate resolution and
storage-independent evidence reuse remain separate.

## Configuration selects inputs, not language rules

A manifest may select supported source/environment inputs. It cannot redefine
typing, ownership, effects, primitive meaning, verifier rules or theorem
statements. Fields purporting to ignore phase, allow dirty clean-release,
insert measurement or trust external operations grant no such permission.
Unknown metadata does not become an executable feature by being present or
hashed. Cargo-style additive features are not adopted implicitly.

If supported configuration changes the executable selection, it belongs in the
resolved program identity: selected dependencies and source components, closed
static actuals and declared generation inputs must be reproducible. A target,
approximation or synthesis choice affecting implementation/evidence must be
recorded in the corresponding realization/profile/evidence identity. It cannot
silently alter logical source denotation or weaken an exact obligation. The
[exactness rules](authority.md#exact-constitutional-obligations) remain in force.

For example, the same logical `foo@1.2.0` with two different selected operation
providers or static sizes is not interchangeable evidence for one resolved
program. `foo@1.2.0` is conceptual package notation here, not a dependency syntax.
A mere diagnostic path, documentation choice or archive layout is not a new
semantic switch. Record storage/provenance separately from program-changing
configuration.

Reproducibility records must expose the relevant closure instead of relying on
undeclared network, time, randomness, filesystem state or ambient environment.
An unsupported ambient input must not silently participate in a reproducibility
claim. Hashing a recorded configuration identifies inputs; it supplies no language
semantics, proof or acceptance authority.

## There is no trusted build script

Build-time execution may produce ordinary inputs or artifacts. It cannot create
a primitive, verifier rule, Meaning receipt, accepted IR, clean ancilla claim,
hidden observation or package-local semantic extension. External Rust/Python/shell
generators remain untrusted: their outputs receive the same applicable ordinary
source and independent native checks. A compromised generator may change source;
its provenance cannot make invalid output accepted.

Obtaining or resolving a qrate does not grant arbitrary host-code execution.
Any future external build action must be explicit, inspectable and scoped to
its declared inputs/capabilities; this chapter implements none. The preferred
generation defaults exclude undeclared ambient inputs. Build success is
organizational evidence, not Soundness, exact equivalence, cleanup, Physical
Realizability or quantitative Resource Safety.

A build generator and a runtime foreign provider are different boundaries.
Native code, callbacks, plugins and opaque operation implementations need the
explicit contract, evidence/capabilities and resource obligations of
[#164](https://github.com/MGYamada/Qleisli/issues/164), or genuine primitive
admission. Packaging them or running a build step grants no runtime semantic
entry. No foreign-execution API is introduced here.

Practical forbidden escalations include QLT pass→Meaning evidence,
docstring→verified contract, generated IR→accepted merely because a compiler
emitted it, build success→clean workspace, package install→trusted primitive,
and backend recognition→source equation. Each claimed artifact still needs its
own applicable checking and correspondence. Existing source/native checks
implement parts of this boundary; they are not a proof of every pipeline.

## Canonical std and the selected toolchain

The official Qleisli product `X.Y.Z` selects and bundles canonical std qrate
`X.Y.Z`. The complete canonical prerelease identifier is equal as well:
`Qleisli 0.3.0-beta` pairs with `std 0.3.0-beta`. An official mixed pair is not
supported. Selecting an older/newer canonical std means selecting the matching
Qleisli toolchain, not independently upgrading a standard-library dependency.
Normal user manifests do not independently choose std.

This is distribution/compatibility privilege only. Std's ordinary `.qli` follows
the same source, public-effect, evidence and native checking as user/third-party
source; its namespace cannot hide observations or introduce a primitive. The
[stdlib contracts](stdlib.md) and [primitive boundary](primitive-boundary.md)
continue to govern its existing meanings.

Resolution/reproducibility and official release records must make the effective
toolchain/std pairing unambiguous and reject stale/mismatched supported pairs.
Source version synchronization and release assertions are necessary, but do not
implement qargo resolution or turn matching version strings into semantic proof.
The private embedded-manifest gate is implemented as described below; full
qargo/resolved-pair binding remains unfinished.

## Current adapter and remaining binding gaps

The supported source-tree manifest spelling is:

```toml
schema-version = 2

[qrate]
name = "example"
version = "0.1.0"
edition = "2026"

[source]
root = "src"
```

For the current Qleisli CLI, `--qrate` opts into that explicit source root
beneath the selected qrate directory. Edition-only manifests remain valid for
ordinary source trees; they are not thereby full qrates. Root selection checks
ordinary sources; it is not package/dependency/test/doc orchestration. Unknown
metadata fields receive unused-key warnings and are ignored by this CLI; known
metadata does not implement features, dependency selection or build actions.
The schema/edition check does not validate every qrate name/version/package
contract.

On Unix, `QrateSource` retains the selected directory identity while loading;
it also retains the exact validated manifest bytes used to select the source
root. Subsequent loading inherits that captured request instead of rereading
the selecting manifest. A fresh selection observes an explicit manifest edit.
Nested manifests are captured during discovery and associated with their
original `.qli` and `.qlt` file paths. Project preparation rejects a changed
root or module inventory without a matching captured context. In-memory
`Project::from_modules` requires an explicit `edition::Edition`; it claims no
file manifest provenance. This constructor has no current/default selector.
Retained manifest text shares the bounded loader's existing aggregate project
input budget with source text; each read manifest is counted once, while
inherited references share its bytes. Per-source and per-manifest limits remain
separate. Trees near the former source-only aggregate limit may need less input
data. The explicit Legacy loader remains outside that aggregate byte limit.

These are requested frontend contexts. Native edition propagation and its
independent mismatch checks remain unfinished under #255; this capture does
not prove the verifier checked an edition. Source file contents may still
change concurrently during loading. It is not a filesystem-content
snapshot or a complete resolved dependency/configuration identity. Other targets
retain their documented filesystem trust assumption. Immutable retained program
or evidence snapshots are separate from this directory selection.

The compiler embeds one fixed ordinary std source set and its manifest. The
private bundled-manifest gate parses those immutable embedded bytes once and
requires string `[qrate].name = "std"` and string `[qrate].version` exactly equal
to the compiler's compile-time product version, including prerelease and build
identifiers. Its cached result applies only to the embedded manifest. Ordinary
user manifests retain their normal schema/edition checks and independent package
versions; source and native acceptance judgments are not cached by this gate.

The read-only Rust API `frontend::project::bundled_std()` returns a privately
constructed descriptor after that same embedded-manifest gate. Its product
version, std name/version/edition, exact manifest and complete canonical
module/source inventory describe the linked library's actual embedded bytes.
It performs no toolchain selection, source or native check, serialization or
digest computation. It issues no accepted handle, semantic evidence,
authenticated release identity or native binary attestation.

Release synchronization includes `stdlib/Qargo.toml`, but the embedded gate
implements no qargo resolver or pairing-record API. Full effective toolchain/std
records and stale-content identity checks remain unfinished in
[#171](https://github.com/MGYamada/Qleisli/issues/171). Exact version-string
equality does not identify selected source contents. A source-root path,
module-import graph, private source snapshot or successful check is not a
complete resolved qrate graph.

All ordinary `.qli` and `.qlt` source trees must explicitly select a concrete
constitutional edition in schema-2 `[qrate].edition`, with no current/latest
fallback. Updating the toolchain does not change that selection. However, the
current filesystem edition check is frontend configuration. End-to-end
manifest-edition→artifact→authoritative-native-acceptance binding, mismatch
rejection and the explicit manifest-free/snippet API rule remain open in
[#255](https://github.com/MGYamada/Qleisli/issues/255), alongside
[#137](https://github.com/MGYamada/Qleisli/issues/137). Product-version checks,
source hashes and this chapter do not supply that missing binding or a QLT
implementation.

The six boundary issues retain their individual acceptance and regression duties;
this chapter does not close their umbrella or complete a qrate ecosystem. The
two admitted scoped QLV1 guarantees remain protected. Broader QS/PR/RS/EXACT,
general source/target/runtime preservation and resource theorems remain pending
under their recorded premises.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
