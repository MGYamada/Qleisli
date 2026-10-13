# Qleisli

**Qleisli and its tools (qargo, qlippy, qlifmt, qlidoc, qleisliup, and qleisliup-init) are independent projects and are not affiliated with, endorsed by, or sponsored by the Rust Project or the Rust Foundation.**

**Rust and Cargo are trademarks of the Rust Foundation.**

Qleisli is an experimental language for structured quantum algorithms, with
linear quantum ownership, explicit measurement effects and exact semantic
contracts. Its Rust frontend produces IR checked independently by a native
Lean verifier. Human-written and AI-generated programs use the same checks.
Qleisli is [pronounced exactly like Kleisli](docs/src/reference/project-identity.md).

**Development version: 0.3.0-beta** (unpublished prerelease).

## Edition

**Qleisli language edition: `"2026"`.** An edition identifies the constitutional
regime, independently of syntax and compiler version. Each source tree declares
its edition explicitly in a schema-2 `Qargo.toml`; the repository root has none.
The [Constitution](CONSTITUTION.md) and [governance](GOVERNANCE.md) define that
regime. General Soundness, Physical Realizability and quantitative Resource
Safety remain proof goals; passing checks does not complete them.

## Example

Save this Bell-pair program as `bell/main.qli`:

<!-- quickstart:bell -->
```qli
use std::quantum::init0;
use std::quantum::h;
use std::quantum::cnot;
use std::observe::measure_z;

observe fn main() -> (Bit, Bit) {
    let (a, b) = cnot(h(init0()), init0());
    (measure_z(a), measure_z(b))
}
```
<!-- /quickstart:bell -->

Declare the source tree's edition in `bell/Qargo.toml`:

<!-- quickstart:manifest -->
```toml
schema-version = 2

[qrate]
edition = "2026"
```
<!-- /quickstart:manifest -->

With an already configured compatible compiler and native verifier:

```sh
qleisli check bell
qleisli run bell
qleisli sample bell --shots=8 --seed=0
```

The reference simulation returns `00` and `11` with probabilities approximately
0.5 each. These are simulated results. Measurement consumes its quantum owner;
reusing that owner is rejected. The standard library is embedded.

## Distribution

**macOS distribution is under consideration.**

Checking and execution require a compatible native Lean verifier. A missing,
incompatible or failing verifier rejects without a fallback or automatic download.

## Experimental adapters

**The OpenQASM 3 / QIR adapters are experimental test features. They are not
suitable for real quantum hardware. Their use on real hardware is not recommended.**

They support bounded import/export and reference-simulation tests. Successful
format checking or native verification does not establish device compatibility
or physical correctness.

## Documentation and development

- [Language Reference](docs/src/reference/source-text.md) and [Book contents](docs/src/SUMMARY.md)
- [Examples](examples/) and [roadmap](ROADMAP.md)
- [Trust boundary](TRUSTBOUNDARY.md) and [constitutional CI](CONSTITUTIONALCI.md)
- [Contributing](CONTRIBUTING.md), [working guidelines](AGENTS.md) and [changelog](CHANGELOG.md)

## License

Copyright 2026 Qleisli Project Contributors. First-party code and documentation
use [Apache-2.0](LICENSE), unless individually stated otherwise. See [NOTICE](NOTICE).
Third-party material retains its own licenses and notices; independently authored
Qleisli programs do not inherit this license automatically.
