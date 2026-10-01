# Small named-QPE capacity profile

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

`Profile.lean` calls the actual executable kernel definitions. `run_profile.py`
checks the same saved packets through the public Rust `Kernel` API, then records
native component costs. The aggregate allowance remains 2,000,000. A separate
stage's success and the diagnostic sum are not accepted instrument receipts.
The records cover target width one and precision widths two and three, using
both textbook and commuting delayed Fourier source. They claim no general
source-preservation theorem or production authority transfer.

Both source schedules have the same measured costs. The
[before record](before-profile.json) and [after record](after-profile.json) retain
packet, producer, host, checker and native executable hashes.
The [local validation](local-validation.json) records fresh Rust/MSRV, Clippy,
changed native tests and reviewed source pins. The
[Fourier comparison](fourier-validation.json) independently checks complete
complex coefficients and six closed Fourier bindings.

| Target, precision | Before actual service | Before isolated diagnostic sum | After actual structural work | After exact work |
| --- | --- | --- | --- | --- |
| `(1,2)` | accepted | 1,242,723 | 1,196,545 | 472 |
| `(1,3)` | `limit` | 2,053,363 | 1,996,759 | 708 |

The `(1,3)` case has 3,241 structural units remaining under the current cap.
These measurements cover the recorded small inputs. Complete independent
provider binding, preparation, readout, every finite equation and each exact H
role remain required. After checking discharges four finite equations/H roles
for `(1,2)` and six for `(1,3)`, preserving their distinct source ports. The full
source root interfaces and independent provider requests equal the before inputs.

Generate current inputs with a fresh audited kernel and an isolated Cargo target:

```sh
QLEISLI_HIERARCHY_KERNEL="$PWD/lean-kernel/.lake/build/bin/qleisli-kernel" \
QLEISLI_QPE_PERF_PROPOSALS=/tmp/qpe-final \
CARGO_TARGET_DIR=/tmp/qpe-cargo \
cargo test --lib native_named_qpe_commuting_fourier_variants_have_the_same_outcome -- --ignored --nocapture
python3 tests/fixtures/qpe_capacity_v023/run_profile.py /tmp/qpe-final \
  --record /tmp/qpe-after-profile.json --producer-commit HEAD \
  --producer-state working-tree --expect accepted --cargo-target /tmp/qpe-cargo
```

The before inputs were exported from commit
`0630f91d75c85c4a96c6b99e74b62356300610cc`. Their hashes are retained in
`before-profile.json`; the large JSON packets are local validation artifacts.
Reproducing those inputs requires a separate checkout at that commit and the
test-only `before-export.patch`, which adds export I/O and changes no producer
or checker rule. Run the same ignored test there; width-three checking accepts
and width-four checking returns `limit`. Pass the resulting directory to
`run_profile.py` with `--expect before` and that full producer commit. A comparison
run can pass it as `--baseline-directory` to assert complete root-interface and
independent provider-request equality. Git retains the baseline source; the
record's original producer hashes and current host/checker hashes are distinct.

`after-profile.json` pins the reviewed working tree over its recorded base
commit. A future release commit must contain the matching producer code.
Historical review and VM-22 records remain unchanged.
