# Qrates, source identity and external artifacts

A **qrate** is the smallest independently versioned and distributable unit of
Qleisli programs. A qrate or a source tree declares itself in a **manifest**,
a file named `Qargo.toml`.

This chapter specifies the authority boundary of packages and artifacts for
edition 2026, under the [authority hierarchy](authority.md). It states what a
qrate, a source file or an external artifact may establish, and what it
cannot authorize by itself. It also gives the manifest format and the source
selection of the `qleisli` CLI. [Status and limits](#status-and-limits)
states the limits of that CLI adapter.

## Source and the five artifact roles

The language, its kernel and accepted ordinary `.qli` define executable
Qleisli meaning. An artifact has one or more of five **roles**. A role states
what the artifact may establish or select. The
[primitive boundary](primitive-boundary.md) answers which meanings require
language rules. This chapter answers which artifacts may claim each role.

The table names three analysis tools. QLT is the Qleisli Testsuite, QDB is the
Qleisli Debugger, and QCP is the Qleisli Circuit Profiler.

| Role | What it may establish or select | What it cannot authorize by itself |
| --- | --- | --- |
| Semantic | The normative language, its kernel and accepted `.qli` define the requested computation, types, owners, effects and specified contracts. | A source name or an annotation cannot manufacture the required evidence or waive a failed check. |
| Evidence | Checked Lean proofs, certificates and verifier decisions establish their stated claims about exact subjects under recorded premises. | They cannot redefine the source denotation, silently strengthen a contract or replace a missing source/target correspondence. |
| Observation | QLT, QDB, QCP, diagnostics, simulations and analyses report bounded denotation, behavior or cost under explicit profiles. | A test pass, a resource estimate or a diagnosis cannot issue production acceptance or trusted Meaning evidence. |
| Realization | Target profiles, decompositions, routing and associated evidence describe or justify an implementation on a selected target. | A native gate set, a recognizer or a successful synthesis cannot change logical source meaning or supply an absent resource bound. |
| Organization | Qrate manifests, dependency and build records, package provenance and documentation organize and identify inputs and artifacts. | Packaging, a hash, version equality or prose cannot install a semantic rule or certify a program. |

Rules:

- A bundled, user-authored or generated definition receives the same
  applicable source checks and independent native checks. Its origin supplies
  no primitive, ownership, effect, inverse, control or Meaning privilege.
- A file may contain several roles. Classification follows the claim that the
  file makes, not its extension and not its distribution origin.
- Documentation tooling must distinguish prose, machine-readable
  declarations, requested contracts, test observations and checked evidence.
- Removing an external proof may remove required acceptance evidence. It
  cannot change the denotation of the declared program.

For example, a doc comment that says “exact Fourier transform” is not a
Fourier equation and not a proof.

### Observation tools

QLT is an external observational and testing surface.

Rules:

- The bounded amplitude or cost inspection that QLT permits does not become a
  `.qli` primitive that inspects live coherent state or a program's own
  denotation.
- QDB, QCP and other analyses cannot upgrade acceptance.

### Generated source

A generator may produce `.qli` source or typed program structure.

Rules:

- Generated `.qli` and generated typed program structure must undergo
  ordinary checking.
- A meta expansion must not inspect live quantum state, inject trusted IR or
  escape the source, effect and evidence obligations of the original.

### Derived artifacts

Serialized Core or IR, caches and generated artifacts are derivative.

Rules:

- A supported artifact path must bind its source and its context where it
  makes a source claim. It must obtain the applicable fresh independent check.
- Valid output IR alone does not prove source preservation.
- An optimizer or a backend intrinsic implements an existing requested
  meaning. Recognizing a pattern cannot decide what the source means.
- Output, phase, axis order, workspace, references and resources keep the
  obligations of [realization](realization.md) and of the
  [production boundary](production-boundary.md).

## Qrate, module and file

A **module** is a canonical namespace and visibility unit. A **file** stores
source. A qrate may contain ordinary source, documentation, tests or QLT,
proofs, resource metadata and explicitly permitted build artifacts.

Rules:

- Bundling an item in a qrate confers no extra authority on it.
- A qrate may depend on other qrates. It must not extend, weaken or bypass
  the language semantics or the required verifier gates.
- A qrate owns its package, version and public-API boundary. The module rules
  and the declared visibility rules of the language determine access.
- A filesystem directory never grants an additional public, private,
  qrate-local or semantic permission.
- These definitions fix concepts. They add no visibility modifier.
- Work on module and import ergonomics must preserve this qrate contract and
  the identity distinctions below.
- A tool that manages, obtains, resolves, checks or records qrates must
  follow this contract. This requirement applies to qargo, a separate tool
  that this repository does not contain.
- The behavior of such a tool does not define what a qrate means.
- A registry, an installer, a solver, a lockfile syntax, a duplicate-version
  policy and a dependency-cycle policy each require a supported package
  specification of their own.

### Identities

A package, a declaration, a program instance and a distribution have
distinct identities.

| Identity | Required distinction |
| --- | --- |
| Logical package | Qrate name and package version, with declared edition and toolchain compatibility. Equal names and versions alone do not identify the selected content. |
| Canonical declaration | Qrate identity, canonical module path and declaration identity. A resolved context selects the package instance. Absolute paths, line numbers and temporary generation names are diagnostic and storage coordinates. |
| Resolved program instance | The selected source and dependency closure, the relevant configuration and static actuals, the requested edition, the pair of toolchain and [canonical std](#canonical-std-and-the-selected-toolchain), and the declared generation inputs. Required profiles and evidence additionally bind the artifact and the checker. |
| Distribution artifact | The exact package or archive bytes and their provenance. Archive layout and content hashes identify a distribution. They do not define the mathematical meaning of a declaration. |

Rules:

- These identities are normative identity inputs. They are not source types,
  not a stabilized hash algorithm, and not a claim that an artifact schema
  carries all of them.
- Dependency selection must be explicit, or deterministically implied by the
  selected toolchain.
- A supported locked graph must record the immutable selected instances. It
  must reconstruct the same source and program selection.
- An ambiguous or unsupported dependency or version policy must not be
  inferred from Cargo conventions.

### Relocation

A canonical identity and a storage location are separate.

Rules:

- Moving unchanged source while preserving its canonical qrate, module and
  declaration identity does not rename the declaration. It does not change
  the denotation of the declaration.
- A move of the packaging layout may change archive bytes and provenance
  without changing that canonical name.
- Moving a declaration from canonical `algebra::operation` to
  `transforms::operation` changes the namespace.
- The distinction also applies to generated files. A temporary directory is
  not a semantic identity of its own.
- Evidence and caches must distinguish canonical program identity from
  storage locations. They must bind the source, dependency and artifact bytes
  and the exact interfaces.
- Stable names or equal widths do not authorize evidence substitution.
- A storage move alone supplies neither a proof nor permission to rebind an
  accepted handle.
- A changed checked subject or a changed representation requires its
  applicable fresh checks and its preservation or transport support.

### Module names and storage paths

```text
--module=NAME=PATH --entry=MODULE::FUNCTION
```

The filesystem convention maps `src/algebra.qli` to the module `algebra` when
`src` is the selected root. Nested relative components form nested module
names. This mapping is a convention of the frontend. The explicit binding
form above names a module and its storage path separately.

Rules:

- The module name participates in identity. The absolute source path is
  provenance.
- The source tree of each bound file must separately satisfy the explicit
  edition check of its manifest.

Both of these option forms are supported:

```text
--module=algebra=/first/storage.qli --entry=algebra::operation
--module=algebra=/second/location.qli --entry=algebra::operation
```

With the same checked source and context, both forms request the same module
name and the same declaration name. The paths locate different storage. The
forms are supported CLI options. They are not full commands, and they are no
evidence that the two compilations have been compared.

<a id="current-adapter-and-remaining-binding-gaps"></a>

## Source-tree manifest

```toml
schema-version = 2

[qrate]
name = "example"
version = "0.1.0"
edition = "2026"

[source]
root = "src"
```

The block shows the supported spelling of a source-tree manifest. A source
file uses the nearest `Qargo.toml` in its directory or in an ancestor
directory. The `qleisli` CLI knows these keys:

| Key | Value | Use by the `qleisli` CLI |
| --- | --- | --- |
| `schema-version` | The integer `2` | Required |
| `[qrate].edition` | The string `"2026"` | Required. It selects the constitutional edition. |
| `[qrate].name`, `[qrate].version` | The name and the version of the qrate | Not validated in a user manifest |
| `[source].root` | A relative directory path | Read only with `--qrate` |
| `[tests].root`, `[docs].root` | Directory paths | Not read |
| Any other key | Any value | Ignored, with a warning |

Rules:

- Every ordinary `.qli` and `.qlt` source tree must explicitly select a
  concrete constitutional edition in schema-2 `[qrate].edition`. There is no
  fallback to a default, to "current" or to "latest". The loader rejects a
  tree without a manifest with the code `project`.
- Updating the toolchain does not change that selection.
- `schema-version` must be the integer `2`. `[qrate].edition` must be a
  string that names a supported edition, and `"2026"` is the only one. The
  loader rejects a manifest that breaks either requirement with the code
  `project`.
- A manifest that declares only the schema version and the edition is valid
  for an ordinary source tree. That tree is not thereby a full qrate.
- The schema and edition check does not validate every name, version or
  package contract of a qrate.
- The CLI ignores an unknown key and reports a warning for it. A known key
  implements no feature, no dependency selection and no build action.
- Dependency tables are unsupported. The CLI treats `[dependencies]` as an
  unknown key: it warns and ignores the table.
- A raw or foreign caller must select the edition explicitly. It must not
  derive the edition from the product version or from std.

The [QLV3 boundary](execution-view.md#native-envelope-cutover) carries the
selected edition through native acceptance.

The loader accepts the manifest above. It also accepts this manifest, which
declares only the edition:

```toml
schema-version = 2

[qrate]
edition = "2026"
```

The loader rejects each of these manifests with the code `project`:

| Manifest | The message contains |
| --- | --- |
| `schema-version = 1`, or no `schema-version` | `Qargo.toml requires schema-version = 2` |
| `edition = 2026`, an integer | `explicit string [qrate].edition` |
| `edition = "2027"` | `unsupported Qleisli edition` |

A manifest with the additional top-level key `unused = true` is accepted. On
`check`, `run`, `sample` and `emit-ir`, the CLI reports a warning with this
message:

```text
unused manifest key `unused`; this Qleisli command ignores it; check the schema-2 spelling (qargo may reject unsupported metadata)
```

> **Implementation note.** `parse_manifest` in
> `src/frontend/project/edition.rs` checks the schema version and the edition.
> `manifest_warnings` in `src/frontend/project/manifest.rs` reports the
> unknown keys. The CLI prints a warning to standard error. With
> `--format=json` it reports the warning as a diagnostic record with the code
> `project` and the severity `"warning"`.

## Qrate source selection

```text
qleisli check <qrate-directory> --qrate
```

`--qrate` opts into the explicit source root beneath the selected qrate
directory. The manifest of that directory names the root in `[source].root`.
`check`, `run`, `sample` and `emit-ir` accept the option. `verify-ir` and
`doc` do not. Root selection checks ordinary sources. It is not package,
dependency, test or documentation orchestration.

Rules:

- The selected directory must itself contain `Qargo.toml`.
- That manifest must give `[source].root` as an explicit string.
- `[source].root` must be a nonempty relative path. It must not contain a
  parent traversal, and no component may be named `target`, in any ASCII
  case.
- Every component of the path must be a directory that is not a symbolic
  link.
- The loader rejects a selection that breaks one of these rules with the code
  `project`.

The loader accepts the roots `src`, `./src` and `src/./`. It rejects `../x`,
`/abs`, the empty string, `.`, `target` and `src/TaRgEt`.

## Captured manifests

A **captured manifest** is the validated manifest text that selected the
edition of a source. A loader retains it with the project that it loads.

Rules:

- A qrate selection retains the exact validated manifest bytes that selected
  its source root. Later loading from that selection inherits the captured
  request. It does not reread the selecting manifest.
- A fresh selection observes an explicit edit of the manifest.
- Discovery captures each nested manifest. It associates the manifest with
  the original paths of its `.qli` and `.qlt` files.
- Project preparation rejects a changed root or a changed module inventory
  that has no matching captured context.
- The in-memory constructor `Project::from_modules` requires an explicit
  `edition::Edition`. It claims no file manifest provenance, and it has no
  default selector.
- The checked methods of `Project` use the retained bytes without reloading
  configuration.
- `ParsedProgram::load` captures the manifest of each selected module.
- The manifest-free `ParsedProgram::parse(edition, modules)` requires an
  explicit `edition::Edition`.
- Every native kernel is bound to an explicit edition. It validates that
  edition against the fresh QLV3 response before it issues a handle.
- A capture is a requested context. It is not acceptance evidence.

> **Implementation note.** On Unix, `QrateSource` in
> `src/frontend/project/manifest.rs` retains the identity of the selected
> directory while it loads. Other targets rely on their documented filesystem
> trust assumption.

## Input limits

The bounded loader limits the bytes that it reads.

| Limit | Value | Scope |
| --- | --- | --- |
| Manifest | 65,536 bytes | Each `Qargo.toml` |
| Source file | 1,048,576 bytes, or the value of `--source-bytes=N` | Each source file |
| Project aggregate | 16,777,216 bytes, or the value of `--project-bytes=N` | The source text and the retained manifest text of one project |

Rules:

- Retained manifest text shares the aggregate project input budget with
  source text.
- Each manifest that the loader reads counts once. The sources that inherit
  that manifest share its bytes.
- The limit for a source file and the limit for a manifest are separate.
- A tree whose source text alone is near the aggregate limit may need less
  input data, because its manifests count too.
- The explicit Legacy loader, which `--legacy-source-limits` selects, is
  outside the aggregate byte limit.
- The loader rejects a manifest over its limit with the code `project`. It
  rejects a source file over its limit, or a project over the aggregate
  limit, with the code `limit`.

## Configuration selects inputs, not language rules

A manifest configures the inputs of a program. It does not configure the
language.

Rules:

- A manifest may select supported source inputs and environment inputs.
- A manifest must not redefine typing, ownership, effects, primitive meaning,
  verifier rules or theorem statements.
- A field that purports to ignore phase, allow dirty clean-release, insert
  measurement or trust external operations grants no such permission.
- Unknown metadata does not become an executable feature by being present or
  hashed.
- Cargo-style additive features are not adopted implicitly.
- Supported configuration that changes the executable selection belongs in
  the resolved program identity. The selected dependencies and source
  components, the closed static actuals and the declared generation inputs
  must be reproducible.
- A target, approximation or synthesis choice that affects implementation or
  evidence must be recorded in the corresponding realization, profile or
  evidence identity.
- Such a choice must not silently alter logical source denotation or weaken
  an exact obligation. The
  [exactness rules](authority.md#exact-constitutional-obligations) apply.
- A mere diagnostic path, a documentation choice or an archive layout is not
  a semantic switch. Storage and provenance must be recorded separately from
  program-changing configuration.
- A reproducibility record must expose the relevant closure. It must not rely
  on undeclared network, time, randomness, filesystem state or ambient
  environment.
- An unsupported ambient input must not silently participate in a
  reproducibility claim.
- Hashing a recorded configuration identifies inputs. It supplies no language
  semantics, no proof and no acceptance authority.

For example, the same logical `foo@1.2.0` with two different selected
operation providers or static sizes is not interchangeable evidence for one
resolved program. `foo@1.2.0` is conceptual package notation here. It is not
a dependency syntax.

## There is no trusted build script

Build-time execution may produce ordinary inputs or artifacts.

Rules:

- Build-time execution must not create a primitive, a verifier rule, a
  Meaning receipt, accepted IR, a clean ancilla claim, a hidden observation
  or a package-local semantic extension.
- An external Rust, Python or shell generator is untrusted. Its outputs
  receive the same applicable ordinary source checks and independent native
  checks.
- A compromised generator may change source. Its provenance cannot make
  invalid output accepted.
- Obtaining or resolving a qrate does not grant arbitrary host-code
  execution.
- An external build action must be explicit, inspectable and scoped to its
  declared inputs and capabilities.
- The preferred generation defaults exclude undeclared ambient inputs.
- Build success is organizational evidence. It is not Soundness, exact
  equivalence, cleanup, Physical Realizability or quantitative Resource
  Safety.
- A build generator and a runtime foreign provider are different boundaries.
  Native code, callbacks, plugins and opaque operation implementations need
  an explicit contract, evidence, capabilities and resource obligations, or
  genuine primitive admission.
- Packaging such code or running a build step grants no runtime semantic
  entry.

The forbidden escalations include these:

| An artifact or event | Does not establish |
| --- | --- |
| A QLT pass | Meaning evidence |
| A docstring | A verified contract |
| Generated IR | Acceptance, merely because a compiler emitted it |
| Build success | A clean workspace |
| A package install | A trusted primitive |
| Backend recognition | A source equation |

Each claimed artifact needs its own applicable checking and correspondence.

## Canonical std and the selected toolchain

The **canonical std** is the standard-library qrate that an official Qleisli
product selects and bundles.

Rules:

- The official Qleisli product `X.Y.Z` selects and bundles the canonical std
  qrate `X.Y.Z`.
- The complete canonical prerelease identifier is equal as well:
  `Qleisli 0.3.0-beta` pairs with `std 0.3.0-beta`.
- An official mixed pair is not supported.
- To select an older or a newer canonical std, a user must select the
  matching Qleisli toolchain. Std is not a standard-library dependency that a
  user upgrades independently.
- A normal user manifest does not independently choose std.
- A user qrate keeps an independent version.
- The pairing is a distribution and compatibility privilege only. The
  ordinary `.qli` of std follows the same source, public-effect, evidence and
  native checking as user source and third-party source.
- The std namespace cannot hide an observation or introduce a primitive.
- Resolution records, reproducibility records and official release records
  must make the effective pairing of toolchain and std unambiguous. They must
  reject a stale or mismatched supported pair.
- Source version synchronization and release assertions are necessary. They
  do not implement qargo resolution, and they do not turn matching version
  strings into a semantic proof.

The [stdlib contracts](stdlib.md) and the
[primitive boundary](primitive-boundary.md) govern the meanings of std.

### The embedded std manifest

The compiler embeds one fixed ordinary std source set and the manifest of
that set. The **embedded-manifest gate** is the check that the loader applies
to that manifest before it loads the set.

Rules:

- The embedded manifest must declare the string `[qrate].name = "std"`.
- The embedded manifest must declare a string `[qrate].version` exactly equal
  to the compile-time product version of the compiler. The equality includes
  prerelease and build identifiers.
- The gate rejects an embedded manifest that breaks either rule with the
  code `project`.
- A user manifest keeps its normal schema and edition checks and its
  independent package version.
- Release synchronization includes `stdlib/Qargo.toml`.

> **Implementation note.** The private function `check_bundled` in
> `src/frontend/project/edition.rs` is the gate. It parses the immutable
> embedded bytes once. Its cached result applies only to the embedded
> manifest. The gate caches no source judgment and no native acceptance
> judgment.

### The bundled std descriptor

The read-only Rust API `frontend::project::bundled_std()` returns a privately
constructed descriptor after the embedded-manifest gate.

| Accessor | Value |
| --- | --- |
| `product_version()` | The complete product version of the linked library |
| `name()`, `version()`, `edition()` | The name, the version and the edition of std |
| `manifest()` | The exact embedded manifest |
| `modules()` | The complete inventory: the canonical name and the source of every embedded module |

Rules:

- The descriptor describes the embedded bytes of the linked library.
- The call performs no toolchain selection, no source check, no native
  check, no serialization and no digest computation.
- The descriptor issues no accepted handle, no semantic evidence, no
  authenticated release identity and no native binary attestation.

### Records of the qargo tool

qargo is a separate tool. Its
[linked-Qleisli contract](https://github.com/MGYamada/qargo/blob/bbce16aed2830eb52cc78ac4b8873e1817663736/docs/linked-qleisli-030.md)
specifies how qargo records the linked pair. This repository does not
produce these records.

| Record or field | Content that the qargo contract specifies |
| --- | --- |
| `qargo.result` and `qargo.build-record`, version 2 | The linked pair of Qleisli and std |
| `effective_std` | The complete Qleisli and std versions, the std edition, the exact manifest digest, the canonical module and source digests, and a content identity |
| `source_configuration_id` | A separate binding of the captured source configuration |

The qargo contract also specifies these points:

- Nonempty checking retains one `Project` and its explicit edition. Build
  metadata uses that same retained `Project`.
- Empty inputs retain no native acceptance claim.
- Reusing an artifact with changed versions, std contents, module inventory
  or configuration fails without overwriting the artifact.
- The diagnostic for a dependency table belongs to qargo. It explains that
  canonical std comes with the linked Qleisli toolchain, and that another std
  version requires its matching toolchain. The `qleisli` CLI does not produce
  this diagnostic.

Rules:

- These records describe observed inputs and checking. A hash is not
  publisher authentication and not mathematical evidence.

## Status and limits

Scope:

- This chapter introduces no registry, dependency solver, feature system,
  build hook, foreign-execution API or accepted-handle format.
- These rules admit no constitutional interpretation.

Limits of the implementation:

- QLT, QDB and QCP have their own implementation scope. Listing their roles
  does not make them available.
- The preferred in-language generator is a typed static and meta layer. The
  [bounded static fragment](static-language.md) does not implement that
  general system.
- The module-import rules are not a completed qrate dependency model.
  Frontend work on module and import ergonomics does not implement qrate
  dependency resolution.
- General cross-qrate resolution and storage-independent reuse of evidence
  are separate work.
- This chapter implements no external build action.
- A qrate selection holds the identity of its directory on Unix only. Other
  targets rely on their documented filesystem trust assumption.
- A capture of a manifest is not a snapshot of filesystem contents. The
  contents of a source file may change concurrently during loading.
- A capture is not a complete resolved dependency or configuration identity.
  Immutable retained program snapshots and evidence snapshots are separate
  from the directory selection.
- The embedded-manifest gate does not resolve external qrates.
- A source-root path, a module-import graph, a private source snapshot or a
  successful check does not establish a complete resolved qrate graph.
- The embedded-manifest gate and the qargo records bind the linked pair of
  toolchain and std. Official package validation, installation validation
  and release validation are unfinished.
- Official registry, package and native installation checks are open. So are
  the supported-host extraction checks.
- Edition binding: the migration to QLV3 and to its helpers is implemented,
  as is the authorized qargo minimum. Complete conformance of the head
  commit, CI and distribution validation are open.
- Product-version checks, source hashes and this chapter do not replace
  native checking. They do not implement QLT.

Tests:

- `tests/editions.rs` checks edition selection, captured manifests, the
  manifest limit, the aggregate budget and the bundled std descriptor.
- `tests/review_v027.rs` checks the warning for an unknown manifest key.
  `tests/review_v026.rs` and `tests/review_v024.rs` check the rules for
  `[source].root`.
- The unit tests of `src/frontend/project/edition.rs` check the embedded std
  manifest.

Proof status:

- The source checks and the native checks implement parts of this boundary.
  They are not a proof of every pipeline.
- This chapter proves no general relocation theorem and no general
  source-preservation theorem.
- The two admitted scoped QLV1 guarantees are protected.
- These rules discharge none of the broader QS, PR, RS and EXACT
  obligations. Those obligations are pending under their recorded premises.
  So are the general source, target and runtime preservation theorems and
  the resource theorems.
- The six boundary Issues have their individual acceptance duties and
  regression duties. This chapter does not close their umbrella, and it does
  not complete a qrate ecosystem.

## History

- This chapter applies the decisions of six boundary Issues:
  [#169](https://github.com/MGYamada/Qleisli/issues/169),
  [#170](https://github.com/MGYamada/Qleisli/issues/170),
  [#172](https://github.com/MGYamada/Qleisli/issues/172),
  [#173](https://github.com/MGYamada/Qleisli/issues/173),
  [#174](https://github.com/MGYamada/Qleisli/issues/174) and
  [#171](https://github.com/MGYamada/Qleisli/issues/171). It was written for
  the product version 0.3.0-beta.
- [#170](https://github.com/MGYamada/Qleisli/issues/170) holds the qrate
  contract, and [#172](https://github.com/MGYamada/Qleisli/issues/172) holds
  the canonical-identity distinctions. Module and import ergonomics are the
  subject of [#65](https://github.com/MGYamada/Qleisli/issues/65).
- The typed static and meta layer is the subject of
  [#60](https://github.com/MGYamada/Qleisli/issues/60) and
  [#61](https://github.com/MGYamada/Qleisli/issues/61).
- [#164](https://github.com/MGYamada/Qleisli/issues/164) holds the explicit
  contract, evidence, capabilities and resource obligations of a runtime
  foreign provider.
- [#171](https://github.com/MGYamada/Qleisli/issues/171) tracks the official
  registry, package and native installation checks and the supported-host
  extraction checks.
- [#255](https://github.com/MGYamada/Qleisli/issues/255) tracks the edition
  binding of native acceptance, alongside
  [#137](https://github.com/MGYamada/Qleisli/issues/137). The QLV3 and helper
  migration and the authorized qargo minimum landed under it.
- The qargo contract that this chapter links is the beta development contract
  of that tool, pinned to one commit.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
