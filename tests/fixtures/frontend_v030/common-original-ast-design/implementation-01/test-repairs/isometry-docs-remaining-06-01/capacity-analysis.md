# Source capacity versus solver capacity

The unchanged work-limit input contains one static Nat and 460 comparisons
(230 upper bounds and 230 lower bounds), with one physical quantum input bit.
Actual attempt06 returned `limit` at the complete original declaration
span 56..4043 with `common source judgment exceeds its 1000000 work capacity`.
The original test's earlier overflow, 33-variable and 64-alternative checks
completed their assertions before this fourth case failed. They remain intact.

The public test now fixes the actual earlier common-work boundary for this
unchanged input. It does not say the solver reached its own limit. The current
exact elimination algorithm separately retains 50,000 pair-work and 4,096
retained-constraint refusal checks; this review does not demonstrate a new
bounded public-source input reaching either one ahead of common accounting.
No new maximum case or capacity override was authored/executed. Direct solver
unit validation would be a separate task; preserving the earlier source test
as a solver-success claim would be inaccurate.

The four files under original-generated-inputs reconstruct the exact retained
Rust source strings from the before snapshot. They are not a new execution or
an independently captured stdin transcript. Their generator and input quantum
widths are unchanged.
