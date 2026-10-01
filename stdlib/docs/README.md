# The standard-library qrate

`stdlib` is a qrate now. Its [Qargo.toml](../Qargo.toml) follows qargo manifest
schema 2: name `std`, product version `0.2.3`, Qleisli edition `"2026"`,
and separate `src`, `tests` and `docs` roots. All three directories are included
in the qrate. The language import namespace remains `std::`.

The compiler embeds the four [source modules](../src) and their edition
manifest in its distribution. It reads no installed qargo executable to use
them. Their mathematical contracts, ownership/effect rules and proof status
remain governed by [STDLIB.md](../../STDLIB.md) and the
[contract ledger](../../docs/stdlib-contracts.md).

To check the source using this checkout:

```sh
cargo run --bin qleisli -- check examples/bell
```

This checks every bundled library declaration as well as the Bell client.
The in-progress schema-2 qargo implementation accepts the manifest and captures
the four sources with:

```sh
qargo check --manifest-path=stdlib/Qargo.toml
```

Qargo chooses its linked checker; record that tool identity separately from
this qrate's version and edition. A successful qargo check is ordinary source/IR
validation, not an algorithm proof or certification of all intended contracts.
The tested qargo 0.1.3 development executable links Qleisli 0.2.1 and currently
fails after manifest capture: its local-module loader rejects `basis.qli` as a
reserved module name. Standalone std-qrate checking needs a specified namespace
adapter in qargo; a full manifest alone does not supply it. Keep the existing
`std::basis` API and embedded-library checking intact. This observed integration
gap is tracked in [Issue 96](https://github.com/MGYamada/Qleisli/issues/96).
QLT execution is still deferred. The [test-root note](../tests/README.md)
identifies the current regression checks.

Other Qleisli source trees currently use edition-only manifests and are not
qrates. The adopted direction is to migrate **all of them to qrate management**;
see the [edition and migration contract](../../docs/language-editions.md).
