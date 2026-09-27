# Language specification development toward Qleisli 1.0

Status: **English design framework; no new accepted syntax or API**
(2026-09-27). This is P012-0 of the [0.1.2 plan](releases/v0.1.2.md).
It organizes future language work before the imaginary algorithm drafts.
The [finite-core specification](language-spec.md), [grammar](syntax-v0.md),
and [sealed and module APIs](standard-library.md) remain the normative source
contracts. The [terminology guide](terminology.md) applies throughout.

## 1. Specification layers and authority

| Layer | Authority and required evidence |
| --- | --- |
| Current language | The English v0 specification and its SC/FC supplements define accepted programs. Implementation limits and conformance records delimit the delivered profile. |
| Future design | This framework and explicitly imaginary code expose requirements. Their types and syntax are proposals, not parser acceptance or standard-library adoption. |
| Selected extension | Before implementation, write English grammar, typing, ownership, effect, meaning, diagnostics, and source-to-IR rules, with accepted/rejected examples and compatibility impact. |
| Implementation and validation | Bind the actual source and IR to independently checked evidence; record test cases and supported bounds. Documentation or generated code alone is not evidence. |
| Proof | State the model, premises, theorem, and implementation correspondence separately. Finite examples do not discharge general adequacy or soundness obligations. |

The north star is to make the concepts used to think about quantum algorithms
the concepts used to write them. The [six imaginary drafts required before
0.2.0](release-milestones.md#pre-v020-imaginary-v1-code) are design inputs;
executable Shor, QPE, and Grover must still meet V1-C1–C5. Neither this framework
nor a draft freezes a future grammar.

## 2. Semantic constraints that future syntax must preserve

`Q<A>` denotes linear ownership of a subsystem with basis type `A`. A call
consumes each quantum input once and returns every surviving owner explicitly.
Separate owners may be entangled with one another and with an arbitrary
reference system. Register indexing, slicing, and iteration must account for
the entire register, including all temporarily inaccessible components.

For each fixed classical input, pure operations denote isometries, and
unitaries additionally have a two-sided inverse. Use the existing effect order
`Unitary <= Iso <= Observe`. Initializing a fresh register is `Iso`;
measurement, reset, and arbitrary discard are `Observe`. Classical host I/O,
randomness, retries, and orchestration are a separately labeled boundary.

Retain exact operator phase and input/output axis order under composition,
adjoint, power, and coherent control. A mathematical black-box unitary does
not automatically provide controlled access or an efficient power operation.
An inverse of state preparation requires a specified unitary extension or a
separate justified domain; an arbitrary `Iso` is not freely reversible.

For pure implementations retain the meaning contract `U E_in = E_out u`,
including isometric encodings, input premises, actual implementation binding,
and all output ownership. Pure auxiliary release requires exact zero return
and separation for every valid input and reference. Approximation tolerance,
lexical scope, or a returned register name cannot establish that requirement.

An observation contract specifies every classical outcome's completely positive
map and a trace-preserving sum. An approximate algorithm additionally declares
its error metric and statistical failure probability. A block encoding states
its normalization and projected subspaces inside a larger unitary; its useful
block is not an unconditional pure operation. These are distinct contracts,
not consequences of ownership or the pure equality alone.

## 3. Shared notation for imaginary code

The following notation is **unimplemented design notation**. Drafts may refine
it with an explicit local definition; incompatible conventions must be resolved
or recorded in their shared requirement index. Use fenced `text` blocks with
an `IMAGINARY QLEISLI 1.0` label, not executable-example claims.

| Notation | Intended interpretation; unresolved implementation choice |
| --- | --- |
| `Bits<n>`, `Q<Bits<n>>` | A basis of n bits and ownership of that entire register. n is a finite static natural; bit k has weight 2^k. Size inference and capacity policy are unselected. |
| `CWord<n>` | A copyable classical word of n measured bits, with bit k weighted 2^k. It is distinct from a coherent basis label and from quantum ownership. |
| `UInt`, `Real`, `Result<T,E>` | Explicitly proposed classical data. Integer bounds, real-number representation, and host/source placement require separate decisions. |
| `UnitaryOp<A>` | A static/elaboration-time, phase-fixed description of an operation on H(A), with no captured live quantum ownership. Descriptions may be reused; each application consumes its quantum argument. This does not commit to runtime first-class operations and is not a current source type. |
| `U(q)`, `adjoint(U)(q)`, `power(U,k)(q)` | Application consumes q and returns its successor. Adjoint/power require recorded access and evidence; k is finite. A power call does not imply unit-cost access. |
| `controlled(U)(c,q)` | Consume and return distinct control/target owners. Require a phase-fixed controlled implementation, not merely the mathematical existence of U. |
| `for static k in 0..m carry state = initial { ... yield next; }` | A finite ordered fold of all carried ownership through a body with the same interface. The upper endpoint is excluded. Zero iterations still check the body. Expansion/sharing, size checks, and IR representation remain unselected. |
| `on_bit(q,k,U)` | Consume the whole register, apply U to one designated axis, and return the whole register; do not create an alias alongside a live owner of q. Multi-register forms must expose all returned ownership. |
| `observe fn` / `host fn` | A quantum instrument / classical orchestration, respectively. Host syntax, random sampling, and repeated execution are proposals with separate cost and failure contracts. |

Sequential statements execute top to bottom; operator products act right to
left. Every draft must state its register layout and any local convention that
differs from the table. An operation that leaves a target after measurement
returns that target explicitly; callers measure or explicitly discard it when
finishing. A `host` loop prepares fresh quantum inputs on every attempt.

Finite `power(U,k)` can be derived by k applications when those applications
are available, with their full cost and elaboration budget. Efficient access
to a large power is a separate capability and assumption. Controlled powers
similarly require controlled access or a justified implementation derivation.

## 4. Extension records

Each proposed facility has a stable requirement ID and records:

1. Algorithm stages that need it and the structure missing from current code.
2. Classification as language form, sealed built-in operation, or ordinary
   definition. Use **unresolved** for an unsettled classification and identify
   host-only processing separately.
3. Static/classical parameters, input/output types, ownership transitions,
   capture restrictions, effects, and totality of any basis function.
4. Exact operator or instrument, phase/axis convention, entry and cleanup
   premises, and any approximation, failure, or classical assumptions.
5. Intended acceptance/rejection cases and independently checkable IR evidence.
6. Implementation bounds, circuit-generation/execution/oracle/classical costs,
   compatibility impact, and separately tracked specification/test/proof status.

For example, a hypothetical register fold accepts distinct control and target
owners and returns both. It rejects duplicate axes, reuse of a consumed handle,
or omission of the untouched register remainder. A hypothetical reflection
accepts a phase-fixed preparation unitary and its inverse; it rejects replacing
that unitary by a one-way initializer or changing a reflection's sign under
control. These are design obligations, not new compiler acceptance tests.

## 5. Next decisions

The six algorithm bodies and requirement records now exist as imaginary,
reviewed design artifacts. Use their shared needs to select a minimal
next-minor specification under the [v0.x plan](v0x-roadmap.md): operation
capabilities first, with size and evidence generalization subject to the
separate symbolic-checking prerequisite and resumption decision.
Do not implement a hypothetical type solely because it appears in a draft.
The [release plan](releases/v0.1.2.md) records completion of the design corpus
separately from implementation, general soundness, and publication.
