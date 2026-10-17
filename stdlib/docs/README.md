# The standard-library qrate

`stdlib` is a qrate now. Its [Qargo.toml](../Qargo.toml) follows qargo manifest
schema 2: name `std`, product version `0.3.0-beta`, Qleisli edition `"2026"`,
and separate `src`, `tests` and `docs` roots. All three directories are included
in the qrate. The language import namespace remains `std::`.

The canonical bundled `std` has the same complete product version as its
official Qleisli distribution, including prerelease and build suffixes. Normal
programs receive it automatically; user qrates retain their own independent
versions. Select the corresponding Qleisli toolchain to select an older or newer
canonical `std`. Distribution coupling grants no semantic privilege.

The compiler checks the embedded manifest's `std` name and exact product version
alongside schema and edition in one parse, caching only that immutable packaging
result. Ordinary external-manifest and source/evidence checks remain fresh.
The [canonical-version Reference](../../docs/src/reference/stdlib.md#canonical-distribution-version)
explains the remaining qargo pairing/record, stale-content identity and
[#255](https://github.com/MGYamada/Qleisli/issues/255) edition-binding gaps.

The compiler embeds seven ordinary [source modules](../src): `std::basis`,
`std::transform`, `std::reflection`, `std::measurement`, `std::gate` and
`std::structure` and `std::state`, with twenty-five public definitions and five private reflection,
scalar-phase, phase-provider, packed-control and fixed-identity helpers. Their edition manifest is
embedded in the distribution too. It reads no installed qargo executable to use
them. Their mathematical admission rules, exact contracts and path migration
are specified by the [stdlib Reference](../../docs/src/reference/stdlib.md);
contribution and evidence requirements remain in [STDLIB.md](../../STDLIB.md).
Bare language primitives require no import; lexical bindings and ordinary
declarations/imports take priority, even after a moved/wrong-category or failed
check. Only genuinely unbound names select a primitive. Retired foundation
imports have no aliases or prelude. `std::state::{init0,reset}` and
`std::structure::{empty,consume_empty}` are ordinary source definitions with
explicit effects, full type/owner trees and arbitrary-reference contracts.
Concrete emitter support and native acceptance remain separate.

The retired `std::routines`, `std::transforms` and fixed `std::arithmetic`
exports have no compatibility aliases. Useful A001–A003 arithmetic circuits
remain local to [the order-finding example](../../examples/order_finding/arithmetic.qli).
Future parameterized arithmetic and factorization names are reserved meanings,
not available APIs. Generic QFT remains excluded from all v0.3.0 and the current
goal; `std::transform::{qft2,qft3}` retain their fixed contracts.

To check the source using this checkout:

```sh
cargo run --bin qleisli -- check examples/bell
```

This checks every bundled library declaration, including private/unused bodies,
as well as the Bell client. Ordinary source judgment, concrete eligibility and
fresh native acceptance remain separate; namespace placement grants no trust.
The in-progress schema-2 qargo implementation accepts the manifest and captures
the ordinary sources with:

```sh
qargo check --manifest-path=stdlib/Qargo.toml
```

Qargo chooses its linked checker; record that tool identity separately from
this qrate's version and edition. A successful qargo check is ordinary source/IR
validation, not an algorithm proof or certification of all intended contracts.
The recorded qargo 0.1.3 development experiment linked Qleisli 0.2.1 and
failed after manifest capture: its local-module loader rejects `basis.qli` as a
reserved module name. Standalone std-qrate checking needs a specified namespace
adapter in qargo; a full manifest alone does not supply it. Keep the existing
`std::basis` API and embedded-library checking intact. This observed integration
gap is tracked in [Issue 96](https://github.com/MGYamada/Qleisli/issues/96).
QLT execution is still deferred. The [test-root note](../tests/README.md)
identifies the current regression checks.

Other Qleisli source trees currently use edition-only manifests and are not
qrates. The adopted direction is to migrate **all of them to qrate management**;
see the edition and migration contract.
