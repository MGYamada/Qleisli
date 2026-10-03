Qleisli 0.2.8 adds opt-in ordinary Rust/Lean dual verification and expands the approved algorithm corpus while retaining compatible 0.2.x contracts.

- `check`, `run`, `sample`, `emit-ir` and `verify-ir` support `--lean-kernel=PATH`; the Rust library exposes `interchange::dual::Kernel`. Both checkers must accept the original artifact/request before execution or emission.
- Native acceptance is refactored into typed stages and connected to independent finite semantics and ordinary linear ResourceSafe for all 19 raw constructors. Full Soundness/EffectSound, hierarchical S05 and authority-transfer gates remain open. Rust remains authoritative; external schemas remain disabled.
- The frozen QuantumKatas, Qualtran and PennyLane corpus grows from 69 to 78 cases, with 54 paired semantic faults. Documentation is reduced by roughly 54%, retaining active plans and imaginary-v1; retired contracts remain available at immutable source references.
- Fix qrate root identity, ancestor traversal permissions, Python QIR-reader identity, structured diagnostic locations/codes, unused QIRF source acceptance, stale documentation references and CI toolchain/environment binding (#181, #192, #239–#244, #247–#249). macOS 11+ and listed Linux architectures require only search permission on ancestors. Older macOS retains its existing descriptor walk/read requirement and deployment targets.
- Retain the partial #223 test-oriented CI migration. Every native bundle builds and audits; releases use full proof replay. Further driver consolidation/performance work remains open.

Validation binds the release to commit `18020190b1c80037442be29d74e90fd9e07253e0`: [full exact-source CI](https://github.com/MGYamada/Qleisli/actions/runs/37087051879), [release PR](https://github.com/MGYamada/Qleisli/pull/252), Rust 1.85/1.98.1, Linux/macOS native checks, installed PyQIR, and clean distribution identity/installation checks. The corpus changes use small systems; existing capacity regressions remain unchanged.

```sh
cargo install qleisli --version 0.2.8 --locked
```

[crates.io](https://crates.io/crates/qleisli/0.2.8) · [API documentation](https://docs.rs/qleisli/0.2.8/qleisli/)

Apache-2.0. Copyright 2026 Masahiko G. Yamada. Required upstream licenses and notices are retained. This release publishes the Rust crate and GitHub source release; no PyPI package or custom binary assets are published.
