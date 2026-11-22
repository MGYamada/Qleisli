# Qrates, source identity and external artifacts

A **qrate** is the smallest unit of Qleisli programs that has a version of
its own and that can be distributed by itself. A qrate or a source tree
declares itself in a **manifest**, a file named `Qlirgo.toml`.
A directory with only `Qargo.toml` may use that legacy name. If a directory
contains both names, the files must be byte-for-byte identical. The checker
selects `Qlirgo.toml` in that case. Both names require the same explicit
schema and edition. A conflicting or invalid pair fails in its directory.


This chapter specifies how much authority packages and artifacts have in
edition 2026, under the [authority hierarchy](authority.md). It states what a
qrate, a source file or an external artifact may establish, and what it
cannot authorize by itself. It also gives the format of the manifest and
says how the `qleisli` CLI selects source. [Status and limits](#status-and-limits)
states the limits of that CLI adapter.

## Source and the five artifact roles

Source files are not the only files around a program. Proofs, test reports,
target profiles and manifests accompany it. This section sorts all of them
into five **roles**, so that you can tell what a given file is able to
decide.

The language, its kernel and accepted ordinary `.qli` define the executable
meaning of Qleisli. An artifact has one or more of the five roles. A role
states what the artifact may establish or select. The
[primitive boundary](primitive-boundary.md) answers which meanings require
language rules. This chapter answers which artifacts may claim each role.

The table names three analysis tools. QLT is the Qleisli Testsuite, QDB is the
Qleisli Debugger, and QCP is the Qleisli Circuit Profiler.

| Role | What it may establish or select | What it cannot authorize by itself |
| --- | --- | --- |
| Semantic | The normative language, its kernel and accepted `.qli` define the requested computation, types, owners, effects and specified contracts. | A source name or an annotation cannot manufacture the required evidence or waive a failed check. |
| Evidence | Checked Lean proofs, certificates and verifier decisions establish the claims that they state. Each claim is about an exact subject and holds under recorded premises. | They cannot redefine what the source denotes or silently strengthen a contract. They cannot stand in for a missing correspondence between source and target. |
| Observation | QLT, QDB, QCP, diagnostics, simulations and analyses report bounded denotation, behavior or cost under explicit profiles. | A test pass, a resource estimate or a diagnosis cannot issue production acceptance or trusted Meaning evidence. |
| Realization | Target profiles, decompositions, routing and associated evidence describe or justify an implementation on a selected target. | A native gate set, a recognizer or a successful synthesis cannot change the logical meaning of the source. It cannot supply a resource bound that is absent. |
| Organization | Qrate manifests, dependency and build records, package provenance and documentation organize and identify inputs and artifacts. | Packaging, a hash, version equality or prose cannot install a semantic rule or certify a program. |

Rules:

- Every definition receives the same applicable source checks and the same
  independent native checks. This holds whether the definition is bundled,
  written by a user or generated. The origin of a definition supplies no
  primitive, ownership, effect, inverse, control or Meaning privilege.
- A file may contain several roles. The claim that a file makes decides its
  classification. Its extension does not, and neither does the origin of its
  distribution.
- Documentation tooling must distinguish prose, machine-readable
  declarations, requested contracts, test observations and checked evidence.
- Removing an external proof may remove evidence that acceptance requires. It
  cannot change what the declared program denotes.

For example, a doc comment that says “exact Fourier transform” is not a
Fourier equation and not a proof.

### Observation tools

QLT is a surface for observing and testing a program. It is external to the
program.

Rules:

- QLT permits a bounded inspection of amplitudes or of cost. That inspection
  does not become a `.qli` primitive that inspects live coherent state or a
  program's own denotation.
- QDB, QCP and other analyses cannot upgrade acceptance.

### Generated source

Some source is written by a program and not by a person. A generator may
produce `.qli` source or typed program structure.

Rules:

- Generated `.qli` and generated typed program structure must undergo
  ordinary checking.
- A meta expansion must not inspect live quantum state, inject trusted IR or
  escape the source, effect and evidence obligations of the original.

### Derived artifacts

Serialized Core or IR, caches and generated artifacts are derivative: a tool
produces each of them from source or from another artifact.

Rules:

- A supported artifact path must bind its source and its context where it
  makes a claim about source. It must obtain the applicable fresh independent
  check.
- Valid output IR alone does not prove that the source was preserved.
- An optimizer or a backend intrinsic implements a meaning that the source
  has already requested. Recognizing a pattern cannot decide what the source
  means.
- Output, phase, axis order, workspace, references and resources keep the
  obligations of [realization](realization.md) and of the
  [production boundary](production-boundary.md).

## Qrate, module and file

This section separates three units that are easy to confuse: the qrate, the
module and the file. A **module** is a namespace with a canonical name, and
it is the unit of visibility. A **file** stores source. A qrate may contain
ordinary source, documentation, tests or QLT, proofs, resource metadata and
explicitly permitted build artifacts.

Rules:

- Bundling an item in a qrate gives the item no extra authority.
- A qrate may depend on other qrates. It must not extend, weaken or bypass
  the language semantics or the required verifier gates.
- A qrate owns its package, its version and the boundary of its public API.
  The module rules and the declared visibility rules of the language
  determine access.
- A filesystem directory never grants an additional public, private,
  qrate-local or semantic permission.
- These definitions fix concepts. They add no visibility modifier.
- Work on module and import ergonomics must preserve this qrate contract and
  the identity distinctions below.
- A tool that manages, obtains, resolves, checks or records qrates must
  follow this contract. This requirement applies to qargo, a separate tool
  that this repository does not contain.
- The behavior of such a tool does not define what a qrate means.
- Six parts of a package system each require a supported package
  specification of their own. They are a registry, an installer, a solver, a
  lockfile syntax, a policy for duplicate versions and a policy for
  dependency cycles.

### Identities

Two things can share a name and differ in content. This section therefore
keeps four identities apart: a package, a declaration, a program instance and
a distribution have distinct identities. The table states what each identity
has to distinguish.

| Identity | Required distinction |
| --- | --- |
| Logical package | The qrate name and the package version, with the declared edition and toolchain compatibility. Equal names and versions alone do not identify the selected content. |
| Canonical declaration | The qrate identity, the canonical module path and the declaration identity. A resolved context selects the package instance. Absolute paths, line numbers and temporary generation names are coordinates for diagnostics and storage. |
| Resolved program instance | The selected source and dependency closure, the relevant configuration and static actuals, the requested edition, the pair of toolchain and [canonical std](#canonical-std-and-the-selected-toolchain), and the declared generation inputs. Required profiles and evidence additionally bind the artifact and the checker. |
| Distribution artifact | The exact bytes of the package or archive, and their provenance. Archive layout and content hashes identify a distribution. They do not define the mathematical meaning of a declaration. |

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

Source moves: a directory is renamed, a package is repacked, a generator
writes into a temporary directory. This section says which moves change a
name and which do not. A canonical identity and a storage location are
separate.

Rules:

- Suppose that unchanged source moves and that the move preserves its
  canonical qrate, module and declaration identity. The move does not rename
  the declaration. It does not change what the declaration denotes.
- A move of the packaging layout may change archive bytes and provenance
  without changing that canonical name.
- Moving a declaration from canonical `algebra::operation` to
  `transforms::operation` changes the namespace.
- The distinction also applies to generated files. A temporary directory is
  not a semantic identity of its own.
- Evidence and caches must distinguish canonical program identity from
  storage locations. They must bind the bytes of the source, of the
  dependencies and of the artifacts, and the exact interfaces.
- Stable names or equal widths do not authorize substituting one piece of
  evidence for another.
- A storage move alone supplies neither a proof nor permission to rebind an
  accepted handle.
- When a checked subject or a representation changes, the change requires
  its applicable fresh checks and its preservation or transport support.

### Module names and storage paths

```text
--module=NAME=PATH --entry=MODULE::FUNCTION
```

A module has a name, and its source has a place on disk. The filesystem
convention derives the name from the place. It maps `src/algebra.qli` to the
module `algebra` when `src` is the selected root. Nested relative components
form nested module names. This mapping is a convention of the frontend. The
explicit binding form above names a module and its storage path separately.

Rules:

- The module name participates in identity. The absolute source path is
  provenance.
- Each bound file belongs to a source tree. That tree must separately satisfy
  the explicit edition check of its manifest.

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

A source tree states its edition in a manifest. The block shows the supported
spelling of a source-tree manifest. A source file uses the nearest
`Qlirgo.toml` in its directory or in an ancestor directory. The `qleisli` CLI
knows these keys:

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
- The edition selects the constitutional regime. The selection does not
  depend on the toolchain release or on the source grammar. Changing the
  selection requires an explicit edit to the manifest. Updating the toolchain
  preserves the declared edition.
- `schema-version` must be the integer `2`. `[qrate].edition` must be a
  string that names a supported edition, and `"2026"` is the only one. The
  loader rejects a manifest that breaks either requirement with the code
  `project`.
- A manifest that declares only the schema version and the edition is valid
  for an ordinary source tree. That tree is not thereby a full qrate.
- The check of the schema version and the edition does not validate every
  name, version or package contract of a qrate.
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
| `schema-version = 1`, or no `schema-version` | `Qlirgo.toml requires schema-version = 2` |
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

Pass `--qrate` when the directory that you name is a qrate and its manifest
says where the sources are. `--qrate` opts into the explicit source root
beneath the selected qrate directory. The manifest of that directory names
the root in `[source].root`. `check`, `run`, `sample` and `emit-ir` accept
the option. `verify-ir` and `doc` do not. Root selection checks ordinary
sources. It does not orchestrate packages, dependencies, tests or
documentation.

Rules:

- The selected directory must itself contain `Qlirgo.toml` or `Qargo.toml`.
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
Later work on that project uses the retained text and does not read the
manifest file again.

Rules:

- A qrate selection retains the exact validated manifest bytes that selected
  its source root. Later loading from that selection inherits the captured
  request. It does not reread the selecting manifest.
- A fresh selection sees an explicit edit of the manifest.
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

The bounded loader limits the bytes that it reads. It applies one limit to
each manifest, one to each source file and one to the project as a whole.

| Limit | Value | Scope |
| --- | --- | --- |
| Manifest | 65,536 bytes | Each manifest under either supported name |
| Source file | 1,048,576 bytes, or the value of `--source-bytes=N` | Each source file |
| Project aggregate | 16,777,216 bytes, or the value of `--project-bytes=N` | The source text and the retained manifest text of one project |

Rules:

- Retained manifest text and source text share one budget, the aggregate
  input budget of the project.
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
language. This section lists what a manifest can select and what it cannot
change.

Rules:

- A manifest may select supported source inputs and environment inputs.
- A manifest must not redefine typing, ownership, effects, primitive meaning,
  verifier rules or theorem statements.
- A field can purport to ignore phase, to allow dirty clean-release, to
  insert measurement or to trust external operations. Such a field grants no
  such permission.
- Unknown metadata does not become an executable feature by being present or
  hashed.
- Cargo-style additive features are not adopted implicitly.
- Supported configuration that changes the executable selection belongs in
  the resolved program identity. The selected dependencies and source
  components, the closed static actuals and the declared generation inputs
  must be reproducible.
- A choice of target, approximation or synthesis can affect implementation or
  evidence. Such a choice must be recorded in the corresponding realization,
  profile or evidence identity.
- Such a choice must not silently alter the logical denotation of the source
  or weaken an exact obligation. The
  [exactness rules](authority.md#exact-constitutional-obligations) apply.
- A mere diagnostic path, a documentation choice or an archive layout is not
  a semantic switch. Storage and provenance must be recorded separately from
  configuration that changes the program.
- A reproducibility record must expose the relevant closure. It must not rely
  on undeclared network, time, randomness, filesystem state or ambient
  environment.
- An unsupported ambient input must not silently participate in a
  reproducibility claim.
- Hashing a recorded configuration identifies inputs. It supplies no language
  semantics, no proof and no acceptance authority.

For example, the same logical `foo@1.2.0` can be selected with two different
operation providers or with two different static sizes. The two selections
are not interchangeable evidence for one resolved program. `foo@1.2.0` is
conceptual package notation here. It is not a dependency syntax.

## There is no trusted build script

A build can run code of its own, such as a generator or a script. This
section says what such code can produce and what it cannot. Build-time
execution may produce ordinary inputs or artifacts.

Rules:

- Build-time execution must not create a primitive, a verifier rule, a
  Meaning receipt, accepted IR, a clean ancilla claim, a hidden observation
  or a package-local semantic extension.
- An external Rust, Python or shell generator is untrusted. Its outputs
  receive the same applicable ordinary source checks and independent native
  checks.
- A compromised generator may change source. Its provenance cannot make
  invalid output accepted.
- Obtaining or resolving a qrate does not grant permission to execute
  arbitrary code on the host.
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
product selects and bundles. Std comes with the toolchain: a user does not
select it separately.

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
- The pairing is a privilege of distribution and compatibility only. The
  ordinary `.qli` of std follows the same checking as user source and
  third-party source: source, public-effect, evidence and native checking.
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
- Release synchronization includes `stdlib/Qlirgo.toml`.

> **Implementation note.** The private function `check_bundled` in
> `src/frontend/project/edition.rs` is the gate. It parses the immutable
> embedded bytes once. Its cached result applies only to the embedded
> manifest. The gate caches no source judgment and no native acceptance
> judgment.

### The bundled std descriptor

A Rust caller can ask which std the linked library carries. The read-only
Rust API `frontend::project::bundled_std()` answers after the
embedded-manifest gate. It returns a privately constructed descriptor.

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

## Release identity and compatibility

The ecosystem has three products, and each has a version of its own. This
section says how an installation identifies a release of each and checks
that the releases fit together. Select one complete release of each product.

| Product | Components with the product's exact release version | Version authority |
| --- | --- | --- |
| Qleisli | Compiler, native checker and canonical std. QLT, QDB and QCP join the same release when shipped. | Qleisli root Cargo `[package].version` |
| qlirgo | `qlirgo`, `qlinties`, `qlifmt` and `qlidoc` | qlirgo root Cargo `[package].version` |
| qleisliup | The installer and selector use their own release | qleisliup root Cargo `[package].version` |

Earlier companion bundles used the names `qargo` and `qlippy`. The current
release inventory of Qleisli comprises the compiler, the checker and std.
QLT, QDB and QCP have planned implementation scope.

A supported official install, update or rollback selects a complete snapshot
of a product. Verify the inventory of that snapshot before switching the
active selection to it. Each bundled component inherits the full version of
the product, including the prerelease identifier. Reject a snapshot that is
incomplete or that mixes versions. The exact
[canonical std pairing](#canonical-std-and-the-selected-toolchain) is one
application of this rule.

### Declared pairing and exact identity

One release may support a separately versioned release of the other product.
Resolve that pairing from the machine-readable metadata that the
distributions supply. Require an explicit declaration for the requested pair
of Qleisli and qlirgo. Reject an unknown pairing. When a capability is
declared unavailable, treat it as unavailable and keep the selected
toolchain.

The minimum contract uses the following fields. A format may store them
in a signed index, a distribution manifest or its referenced receipts.

| Identity | Contents |
| --- | --- |
| Product and release | The product name, the complete version, and the component inventory with the exact version of each component |
| Exact build | The source revision, the host or target, the SHA-256 and the size of each artifact, and the identities of the emitted compiler/checker build and of the bundled std |
| Interfaces | The supported constitutional edition, the analysis protocol, the artifact schemas and the target/cost-model identities, recorded separately |
| Compatibility | The other product and release that are explicitly supported, the applicable protocol/schema versions or supported ranges, and the availability of capabilities |
| Required environment | The checker, proof/kernel environment and evidence identities for the validation the release claims |

Use the artifact identities to check the selected bytes before use. Where a
result promises reproducibility, retain the exact identities of the source,
the checker and the artifacts that produced it. A human-facing version
identifies the release. The manifest and its associated receipts identify
the exact build.

qleisliup consumes the declared metadata to select an immutable snapshot.
The bound std descriptor and native-result identities provide current
Qleisli coordinates. A linked qlirgo build binds an exact Qleisli package
version and verifies its actual std and checker. A distribution with both
standalone and linked checking records the two Qleisli identities separately.
The registry artifact and host checks control which linked pair may be
described as an official distribution.

> **Implementation note.** The qleisliup toolchain manifest records
> `qleisli`, `std`, `qargo` and `qargo_checker_qleisli` separately. Its
> release manifest binds a host archive by SHA-256 and size. The Qleisli
> distribution report binds the checked commit and tree to the crate digest,
> complete source archive and installation checks. A qleisliup development
> link selects a local directory under its own inspection contract.

### Version-drift checks

A product repeats its version in several files, and the copies can drift
apart. Derive or check repeated manifests and runtime version fields from
the root version of their product. The shared documentation and edition
checks of Qleisli reject drift in the native, Python and Lean version fields
and in the bundled std. The packaged source and installed binaries run
separate distribution checks. The source verifier and the package verifier
of qlirgo check the component manifests and all four executables against the
root version of qlirgo. The complete supported-host distribution retains the
exact build and installation evidence.

## Status and limits

Scope:

- This chapter introduces no registry, no dependency solver, no feature
  system, no build hook, no API for foreign execution and no format for
  accepted handles.
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
- Two tasks are separate work: general resolution across qrates, and reuse
  of evidence that does not depend on storage.
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
  toolchain and std. A prerelease candidate can exercise this pairing with
  the exact checked Qleisli crate and the four locally built companion tools.
  The official linked distribution requires the registry package and
  supported-host installation evidence.
- The finite source and QLV3 paths bind the declared edition. The
  companion qargo manifest gate uses the same explicit edition rule.
  The final release verification binds these checks to one candidate.
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
  So are the resource theorems and the general theorems of source, target
  and runtime preservation.
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
- [#230](https://github.com/MGYamada/Qleisli/issues/230) defines the three
  release domains. [#231](https://github.com/MGYamada/Qleisli/issues/231)
  defines the release and compatibility metadata. The analysis protocol work
  in [#106](https://github.com/MGYamada/Qleisli/issues/106) and tool integration
  in [#107](https://github.com/MGYamada/Qleisli/issues/107) have their own
  interface versions. [#615](https://github.com/MGYamada/Qleisli/issues/615)
  records the linter naming decision.
- The qargo contract that this chapter links is the beta development contract
  of that tool, pinned to one commit.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
