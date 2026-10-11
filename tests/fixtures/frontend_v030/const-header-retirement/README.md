# Retired compile-time header marker

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Issue [#33](https://github.com/MGYamada/Qleisli/issues/33), based on
`b679ba39e2e8ea8c6d95d1e069e1d4806d65141d`. The production parser rejects
`static` in compile-time parameter headers, including mixed headers, at the
marker's original byte span. Its diagnostic instructs replacement by `const`.
Ordered kinds, explicit specialization arguments, contextual const identifiers,
static conditions/folds/lets, original ASTs and native acceptance rules retain
their existing contracts. The Reference describes the migration precisely.

The previous source is preserved by the baseline Git commit; all first sources,
source maps, comparison bytes and oracles remain unchanged. Historical Fourier
inputs for existing bounded regressions receive one asserted, test-local header
translation. Shared measured-client tests still use the filesystem loader with
a scoped temporary translated file and compare its retained actual bytes.
Temporary files are reclaimed by the existing SourceRoot owner. No generic QFT
code is copied into an active source tree, algorithm changed, width added or
implementation obligation reopened.

[source-review.json](source-review.json) records the parser pin review and first
local refusals. Public parser signatures/capacity constants were compared before
refreshing only its current reviewed hash. This is not a proof or new guarantee.
The new parser migration test and two public entry-point refusal cases passed
on latest Rust and MSRV. The existing 16 operation_parameters / 28 parser tests
passed on both toolchains; sized_source finally passed 38 tests with its three
existing ignored cases retained. Broader Rust/CI checks remain pending at this
recording point. Full source preservation and broader QS/PR/RS remain pending.

The first repaired broad groups passed the library tests and then found two
Basis-polymorphism failures from dynamic study paths missed by the literal
include census. Current selection now covers the used Basis/inference/tuple/
mixed-Boolean study inventories, including the independent tuple operation
source. Original bytes and semantic expectation values remain unchanged. Two
Basis inputs already had a qfor predecessor and const selection; those existing
links are reused rather than bypassing or duplicating them. Inventory checks
rejected the initially redundant entries, which were removed.

The focused Basis, inference and mixed-Boolean suites passed 11, 6 and 7 tests
on both toolchains. The tuple suite exposed one further independent-source
header; after selecting it, all 12 tests passed on both toolchains. Final
all-target Clippy passed on both versions. VM-29's scoped identity review retains
all constructors, public signatures, capacities, boundary rules, proof gates
and authority claims, changing only the reviewed linked source identity. The
original failed shared-group outputs remain retained; the full Rust groups
still require a final run after these repairs, with all 4,000 cases intact.

The subsequent six-target probes passed 57 tests across five targets on both
toolchains. Their CLI target initially passed ten and failed one because a
test-local Fourier header translation bypassed the existing qfor migration.
Reading the selected predecessor before translating the header restored all
eleven CLI tests on latest Rust and MSRV. Failed runs remain recorded as failures;
final shared full groups and exact-commit CI are still pending. Fixture
preflight passed with 17,469 files / 125,970,541 bytes before this record update.

The latest all-targets diagnostic completed with nine failures in five targets:
ordinary_types, qli_corpus, repair_diagnostics, sized_cli and sized_declarations.
MSRV stopped at the first ordinary_types failure. Both retained 4,000-case
ownership suites passed (360.65 / 413.49 seconds); these concurrent timings
are observations, not a controlled speed comparison. Fifteen further
header-only selections and two input readers repair the remaining failures.
The static Nat diagnostic still rejects the finite profile at its identifier;
its expected column is 24 instead of 25 after the one-byte-shorter marker.
After repairs, all five targets passed on both toolchains (52 tests, two
existing ignores each). Failed full runs remain failures. Final declared full
groups and exact-commit hosted CI are still required.
