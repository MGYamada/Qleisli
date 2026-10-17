# Qleisli

**Qleisli and its tools (qargo, qlippy, qlifmt, qlidoc, qleisliup, and qleisliup-init) are independent projects and are not affiliated with, endorsed by, or sponsored by the Rust Project or the Rust Foundation.**

**Rust and Cargo are trademarks of the Rust Foundation.**

Qleisli is an experimental quantum programming language with linear quantum
ownership, explicit measurement effects and exact semantic contracts. A Rust
frontend and independent native Lean verifier support small reference simulations.

Package version: **0.3.0-beta** (unpublished prerelease).
Package, executable and Rust library name: **`qleisli`**.

## Edition

**Qleisli language edition: `"2026"`.** Edition identifies the constitutional
regime, independently of syntax, compiler version and Rust's implementation
edition. Every source tree requires an explicit schema-2 `Qargo.toml`.

## Example

Save this Bell-pair program as `bell/main.qli`:

<!-- quickstart:bell -->
```qli
use std::state::init0;
use std::gate::cnot;

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

## Documentation and proof scope

General Soundness, Physical Realizability and quantitative Resource Safety
remain proof goals. Successful checking is not proof of algorithm correctness
or hardware behavior.

- [Language quick reference](https://github.com/MGYamada/Qleisli/blob/v0.3.0-beta/tests/fixtures/quick_reference/README.md)
- [Trust boundary](https://github.com/MGYamada/Qleisli/blob/v0.3.0-beta/TRUSTBOUNDARY.md)
- [API documentation](https://docs.rs/qleisli) and [source repository](https://github.com/MGYamada/Qleisli)

## License

Copyright 2026 Qleisli Project Contributors. First-party code and documentation
are Apache-2.0 unless individually stated otherwise; see the packaged `LICENSE`
and `NOTICE`. Third-party material retains its own licenses and notices.
