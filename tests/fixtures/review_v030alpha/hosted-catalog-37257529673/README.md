# Hosted primitive-omission calibration repair

CI 37257529673 ran at 9a1ecef79f2f1e42f94093b6f4822f282f6e9129.
Latest Rust all-target tests succeeded, but the subsequent omission calibration
failed because its injected row used the previous catalog macro shape. It
therefore triggered a macro parse error before the required exhaustive-handler
errors. Actual timestamped failure lines, original script and minimal repair
are retained. Required diagnostic and all three handler-location assertions
remain in force.

completed-jobs.json records success for native Lean build/audit/replay and
comparisons, Mathlib Lean, MSRV, interoperability, docs, distribution and macOS
producer jobs. The Rust producer failed at calibration; aggregate gates fail
and the complete run is not successful. The earlier observed-jobs.json is an
unchanged partial observation.

validation/ records an actual successful repaired omission experiment on the
current tuple candidate with Rust 1.98.1: OmittedPrimitive fails exhaustiveness
in concrete preparation, lowering and source preservation. The harness's
temporary crate/target was automatically removed. Source identities stayed
fixed. This is not a same-9a1 rerun or new runtime/native proof.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
