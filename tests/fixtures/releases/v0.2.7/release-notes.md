## v0.2.7

- Add native Lean checking for QIRF leaves, finite requests and phase-fixed H, bounded graph/root semantic proofs, and 362 Rust/Lean decoder comparisons.
- Adopt test-oriented routine CI while retaining native audits/comparisons and the full proof lane for releases and policy-risk changes.
- Expand the pinned small corpus from 60 to 69 cases and add nine paired semantic faults.
- Reduce tracked documentation by approximately 55%, preserving active plans and imaginary-v1.
- Fix #207–#212 and #214: tuple reconstruction, QPE fault-harness CI coverage, kernel source policy, upstream attribution, local-call diagnostics, no-clobber proposal output and host-independent manifest warnings.

Production acceptance remains in Rust. General analytic reader-to-Operator closure, universal decoder/compiler proofs and VM-27 authority-transfer gates remain open. This release does not complete R14 or H1–H5.

## Install

```sh
cargo install qleisli --version '=0.2.7' --locked
```

[crates.io](https://crates.io/crates/qleisli/0.2.7) · [API documentation](https://docs.rs/qleisli/0.2.7/qleisli/) · [Changelog](https://github.com/MGYamada/Qleisli/blob/v0.2.7/CHANGELOG.md)

The release uses the annotated tag `v0.2.7` at `7844a10d63880a2b6984c093e2dc7a75033d1e1e`. Exact-source full CI: https://github.com/MGYamada/Qleisli/actions/runs/37022315738. Publication, installation and source-archive evidence will be retained under `tests/fixtures/releases/v0.2.7/`; earlier development validation records remain historical.

Rust installation requires no Lean, Python or LLVM. Optional interoperability has separate requirements. No custom binary or Python package is published in this release.
