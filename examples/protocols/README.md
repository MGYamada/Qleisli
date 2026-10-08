# Protocols built from shared Bell operations

Run `cargo run --bin qleisli -- run examples/protocols`. The inline
[main](main.qli) is the user-supplied Claude teleportation body with explicit
imports. It prints `001`, `011`, `101`, `111`, each with probability 1/4:
two random message bits, then the X readout of the teleported `|->`.

The other files extract reusable ordinary `.qli` functions. They are example
APIs, not new language forms, sealed operations or bundled standard APIs.
All quantum arguments are consumed; only returned owners may be used again.
Distinct owners may be entangled. Types and effects are written in the source.

| Module / public functions | Contract and evidence scope |
| --- | --- |
| [bell](bell.qli): `prepare`, `measure` | `prepare` is an `Iso` returning two fresh owners in the positive Bell state. `measure` is `Observe`, consumes both owners, and returns **(phase, parity)** after CNOT and H. |
| [corrections](corrections.qli): `pauli` | `Unitary`; consumes a target and returns Z^phase X^parity applied to it, with ordinary classical control. Classical inputs are reusable. |
| [teleportation](teleportation.qli): `teleport` | `Observe`; consumes input and newly allocated Alice wire, returns `((phase,parity),bob)`. For any joint input density matrix ρ on input and reference, each corrected branch is ρ/4, identifying the input interface with Bob. This is the intended ideal instrument, not a theorem supplied by its type. |
| [dense_coding](dense_coding.qli): `round_trip` | `Observe`; encodes two classical `Bit` inputs into one half of a fresh Bell pair, consumes the pair and returns the same two bits in the same order. |
| [swapping](swapping.qli): `connect` | `Observe`; prepares two Bell pairs, consumes their middle owners, and returns a uniform two-bit message plus a corrected distant Bell pair. |
| [states](states.qli): `zero`, `one`, `plus`, `minus`, `y_plus`, `y_minus`, `magic` | Closed whole-space unitaries used as static preparation arguments. Applied to zero, their states are documented in source. `magic` has relative phase exp(iπ/4); it is not a new primitive. |
| [checks](checks.qli): `teleport_prepared` | `Observe`; needs `Apply` and `Adjoint` access to one preparation. Prepare zero, teleport, undo preparation and measure. Returns random message plus a zero failure bit. |

`cargo test --test qli_corpus` checks all four messages separately for all seven
prepared states, Bell-reference recovery, all four dense-coding messages and
the distant pair after swapping. Inline and modular teleportation have the
same complete distribution. Deliberately omitted/swapped corrections compile
but fail these algorithmic expectations. A basis-state-only check misses the
omitted phase correction.

The preparation client uses `adjoint(Prepare)(output)`. `y_minus` uses two
named `inverse(t)` applications after H and has the full operator
`S†H = [[s,s],[-i*s,i*s]]`, where `s = 1/sqrt(2)`. A separate exact matrix
regression checks both columns and the complete phase. Opposite relative phase
and an added global phase remain valid unitaries but fail that intended meaning;
a prepare/undo round trip alone would not distinguish them.

Calls expand into existing gates, allocation, classical branches and consuming
measurements; final IR passes the independent verifier. Invalid ownership or
effect use rejects through the existing rules. Finite `f64` distribution checks
use tolerance 1e-12 without renormalizing. They do not mechanize the general
instrument equation, prove Rust correctness or establish hardware fidelity.
Before stdlib adoption, stabilize names/result roles and supply the separate
contract-ledger entry and evidence required by the library plan.
