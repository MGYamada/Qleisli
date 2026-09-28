# Fixed-width algorithms with operation arguments

Run `cargo run --bin qleisli -- run examples/operation_algorithms`. The
[main](main.qli) calls shared three-bit QPE with T on `|1>` and returns `1001`
with probability one: low-weight phase bit first, then the retained target.
These are ordinary experimental example APIs; no stdlib or core rule is added.

| Module / public functions | Contract, ownership and acceptance |
| --- | --- |
| [gates](gates.qli): `identity`, `hadamard`, `flip`, `eighth_phase` | Closed `Unitary` wrappers on `Q<Bit>` returning their input ownership; meanings I, H, X, T. Required because sealed gates are not current bracket providers. |
| [estimation](estimation.qli): `phase2`, `phase3` | `Observe`; require `Controlled(U)` for `Op<Bit>`. Return two/three low-weight-first phase bits plus the consumed target's successor. Inputs need not be eigenstates. The control registers are consumed by measurement. |
| [oracles](oracles.qli): `mark00`, `mark10`, `mark01`, `mark11` | `Unitary` on `Q<(Bit,Bit)>`; I − 2 projector onto the named label. Total two-argument basis predicates lower through existing computed XOR/phase/uncompute with exact auxiliary cleanup. |
| [oracles](oracles.qli): `Mark11` | Independent phase meaning from a unary pair-pattern basis function; `bind_op(mark11, Mark11)` checks the circuit against it with the existing exact function checker. |
| [oracles](oracles.qli): `zero_reflection` | Same interface; R0 = 2 projector onto 00 − I. Its sign is the opposite of `mark00`, and matters under coherent control. |
| [amplification](amplification.qli): `uniform`, `amplify_once`, `amplify_twice` | `uniform` is a whole-space H⊗H `Unitary`. The two `Iso` clients allocate A applied to zero, then apply G = (A R0 A†) O once/twice. Require `Apply(A)`, `Adjoint(A)`, `Apply(O)` on pair operations; return all data ownership. Arbitrary supplied operations do not imply a search-success theorem. |
| [interference](interference.qli): `real_overlap`, `imaginary_overlap` | `Observe`; require `Controlled(U)` on `Op<Bit>`. Return meter `CBit` and remaining target owner. For target density matrix ρ, E[(-1)^meter] is Re Tr(ρU) or Im Tr(ρU), respectively. Measurement can correlate with the returned target. |

`phase3` uses the flat result spelling `(CBit,CBit,CBit)`, which has exactly
the previous type `((CBit,CBit),CBit)`. It preserves low-weight-first ordering.

For an eigenstate with U eigenvalue exp(2πiθ), m-bit QPE gives integer y with
probability `|Σ(r=0..2^m−1) exp(2πi r(θ−y/2^m))|² / 2^(2m)`.
The target remains conditional on the observed phase. Tests cover all eighth
roots at m=3, θ=1/8 between bins at m=2, both X eigenstates, a Bell-correlated
input, and preservation of coherence within the identity's degenerate eigenspace.
Using the forward QFT is an intentional type-correct fault returning phase 7/8
instead of 1/8.

For uniform preparation and one mark among four, Grover's success probability
after k iterations is `sin²((2k+1)π/6)`: one iteration succeeds, two overshoot to
1/4. All four marks and the overshoot are checked. Hadamard tests check T and T†
on `|1>` so the real and imaginary signs are distinguishable.

Run `cargo test --test qli_corpus`. All supplied bodies and instantiated static
descriptions pass existing source and independent IR checks. Distribution
assertions use tolerance 1e-12; they are finite validation, not a general Rust
or algorithm proof. Quantum aliases, unavailable access and incorrect exact
type trees reject. Before stdlib adoption, settle result layout and generalized
interfaces and enter their evidence/adoption criteria in the contract ledger.

This removes operation-specific body duplication at the **same target type**.
It cannot share this QPE body with the four-bit target of
[order finding](../order_finding/estimation.qli). Type/size parameters, general
angles and iteration variables remain unimplemented; V1-C2 is not satisfied.
