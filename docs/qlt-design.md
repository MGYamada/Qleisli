# QLT: mathematical tests for quantum programs

Status: **design direction adopted on 2026-09-29; no QLT parser, evaluator,
CLI command or certificate interface is implemented**. This English document
records the user-approved design and future work packets. Examples are desired
test source, not accepted `.qli` syntax or claims of executed `.qlt` tests.
Product development is now 0.2.1. **The user deferred QLT implementation to
v0.4.0 or later on 2026-09-29**, after the
[Qleisli type-system specification planned for the v0.3.0 breaking-change release](v0x-roadmap.md#v030-qleisli-type-system-specification).
This supersedes the earlier 0.3–0.4 Rust-experiment window. Existing design and
source records are retained; later Lean migration remains an independent goal.

The [preserved first sources and semantic counterexamples](../tests/fixtures/qlt_design/README.md)
make the proposed language concrete. Follow the
[code-driven method](code-driven-development.md): retain those originals,
append actual diagnostics and revisions when implementation begins, and compare
author burden and evaluation cost without claiming a controlled LLM benchmark.

## 1. Semantic boundary and responsibility

`.qli` describes quantum operations under linear ownership, effects and checked
contracts. `.qlt` describes classical mathematical tests of those programs.
Many such tests inspect amplitudes or complete operators and compare several
evaluations of the same mathematical input. These are not operations offered
on an unknown physical quantum state. `denote` consumes a program description,
not a live quantum owner and not a device handle.

| Boundary | Intended guarantee and restriction |
| --- | --- |
| `.qli` and its checked backend | The [Soundness, Physical Realizability and Resource Safety Theorems](release-milestones.md) concern their declared IR/target/resource profiles. Their general implementation proofs remain open; QLT cost diagnostics alone do not prove RS-C1–C5. |
| `.qlt` evaluation | A separate future adequacy theorem relates the actual test evaluator's successful result to the Lean IR denotation or specified cost model. It does not make introspection into a `.qli` operation. |
| Individual assertions | A successful finite comparison concerns its bound implementation, mathematical reference, parameters and domain. It is not a theorem about every instance of a family. |
| Standard library | Ordinary definitions still undergo the same source, IR and evidence checks as user code. Tests support mathematical specification and regression review; bundled origin and test success grant no verification exemption. |

Dependencies go one way: `.qlt` may refer to public `.qli` definitions through
`qli::`; `.qli` cannot import `.qlt`, call `denote` or invoke a test-only unsafe
operation. The new parser/AST and mathematical runtime remain separate from
the `.qli` language and acceptance core. Reusing lexical/diagnostic utilities
must not make QLT attributes or primitives valid in `.qli`.

Contracts retain ownership, effects, exact phase, entry encodings and exact
auxiliary zero return. QLT tests independently check intended mathematics,
approximation claims, cost regressions and examples. They do not introduce a
second authoritative ownership or semantic-contract language. A backend error
bound used for realizability still needs its declared
[approximation contract and evidence](coefficient-domains.md#exact-approximate-and-device-contracts);
passing a tolerance test cannot authorize exact equality or pure cleanup.

## 2. Initial source and public interface design

Use familiar Rust-style `use`, `fn`, `let`, `#[test]`, `assert!` and
`assert_eq!`. `#[test(n in 1..=N)]` is a QLT-specific bounded parameterization,
not the behavior of Rust's built-in `#[test]`. Expand each concrete parameter
into a separately identified case; validate and charge the expansion first.
The initial example below uses already existing fixed-width `.qli` definitions.

```qlt
use qli::std::transforms::qft2;
use qlt::math::dft;

#[test]
fn qft2_is_dft() {
    assert_eq!(denote(qft2), dft(4));
}
```

QLT values are immutable classical data. Small scalar values may copy; large
matrices use borrowing and explicit cloning in accordance with the
[Rust type/ownership default](design-philosophy.md#follow-rust-for-type-and-ownership-discipline).
Assertions borrow their operands. No quantum owner is cloned. The initial
language excludes general recursion, external processes, network access,
arbitrary host callbacks and device access. Finite helper evaluation and
parameter expansion share explicit resource limits.

| Facility | Initial planned contract |
| --- | --- |
| `qli::module::name` | A reference to a public, closed `.qli` operation with every static argument concretized through the supported source mechanism. It is not a runtime invocation on quantum data. Preserve the exact type tree, ordered ports, effect, dependencies and source/IR identity. |
| `denote(f)` | Initially accept unary `unitary` definitions with the same exact input/output basis type, no runtime classical arguments and a transparent supported implementation. Check source and IR normally, then evaluate the actual implementation into a phase-exact finite matrix. A claimed contract/specification matrix is never substituted for the body. |
| `cost(f)` | Inspect checked implementation IR under an identified structural cost profile. Report primitive kind, controls and expanded invocation counts separately from ownership/layout steps and verification/generation work. Do not evaluate a dense denotation. |
| `qlt::math::` | A separately reviewed classical reference vocabulary. Start with exact matrices, identity, explicit permutations, DFT, adjoint and matrix algebra; channels, polynomials and Hamiltonians follow later. References are not alternate `.qli` circuit implementations. |
| `assert_eq!` | Compare exact values with compatible dimensions, coefficient domain and stated basis order. Retain global phase; do not infer a source type conversion from equal matrix dimensions. |
| `assert!` | Require a Boolean predicate, including a comparison of structural cost counts. It issues no quantum evidence. |

The mathematical type roles are distinct: an operation descriptor preserves
the checked `.qli` interface, `Matrix<D>` carries finite dimensions and a
declared coefficient domain/basis ordering, and a `CostReport` carries the
cost-profile identity and counts. None converts implicitly to a quantum owner
or certificate. These are design roles, not newly exported Rust or Lean types.

### Independent references

Define the positive, normalized DFT by

\[
F_N[y,x] = N^{-1/2}\exp(2\pi ixy/N),\qquad 0\le x,y<N.
\]

For current examples, flatten the declared quantum interface in its documented
order with the first bit least significant. Preserve nested versus flat source
types when resolving a function; matrix indexing is not an implicit `.qli`
layout conversion. A permutation reference satisfies `P[f(x),x]=1` with every
other entry zero and validates that `f` is a complete bijection. For example,
`increment2` is compared against `[1,2,3,0]`, including wraparound.

Construct DFT/permutation entries directly from these mathematical definitions,
without calling QFT generation, source inversion or axis-remapping helpers.
The evaluator and reference may share reviewed scalar arithmetic, but retain
independent existing Rust/Python arithmetic and semantic oracles as regressions.
An implementation-to-implementation comparison cannot replace a mathematical
reference, and an independent reference formula does not prove its own code.

### CLI and doctests

The proposed command `qleisli test <source-root>` discovers
`tests/**/*.qlt` in deterministic path order. `--doc` instead extracts `qlt`
fences from `.qli` documentation comments. Support library roots without
`main`; do not manufacture a quantum entry point merely to inspect a function.
Doctests follow public visibility and explicit imports, and source locations
map back to the original comments. Run bundled-library doctests in the
stdlib's dedicated validation job, not automatically as every client's tests.

`--format=json` uses a separate, versioned test-result format. Do not extend the
closed `qleisli.result` v1 union silently. Reports identify case/parameters,
source location, comparison/cost profile, outcome and whether any Lean
certificate was actually checked. The complete grammar, cost fields, bounded
runner policies and JSON wire schema must be frozen in the TQL-1 extension
specification before exposing the command. This design does not implement it.

## 3. Evaluation, cost and assurance

### First experiment: Rust and exact finite matrices

The user selected **Rust first, then Lean migration**. Reuse ordinary source
checking and the independently verified per-function IR. The existing
[private finite denotation helper](../src/contract/function.rs) supplies an
implementation starting point; it exposes no evidence constructor and does
not trust frontend circuit flattening. Add a narrow checked-function selection
boundary rather than accepting mutable frontend metadata or building test-only
quantum operations. Cache only against immutable implementations, dependencies,
arguments and evaluation profiles, never the function name alone.

The initial domain is `R8 = Z[ζ8,1/2]`, matching
[current exact arithmetic](../src/contract/exact.rs), with row and column
dimensions each at most 64. `dft(N)` initially supports `N` in `{1,2,4,8}`.
DFT16 and finer roots are not R8 constants; reject them as unsupported even
though their matrix dimensions fit. Do not substitute floating-point values.
QFT2/3 and a reversible arithmetic/permutation client are the first adoption
experiments. Wider dyadic QFTs need a specified coefficient extension or later
bounded interval evaluation; they do not justify changing M2's checker profile.

Bound input bytes, syntax/depth, case expansion, matrix allocation, integer
growth, cloning, reference construction and evaluation. Aggregate evaluation
work across the command; never refresh a full budget at each assertion or
parameter instance. Preserve current source/IR capacities. Arithmetic or work
exhaustion cannot turn an uncomputed equality into success.

### Structural cost without dense evaluation

Memoize the cost of shared definitions, then count it at every call and multiply
by repeat counts using checked arithmetic. Validate dependencies and bodies even
for zero repetition. Record small shared IR/checking size separately from large
expanded execution cost; cancellation in a semantic normalizer does not erase
the cost of operations in the inspected implementation.

Cost aggregation itself must not request a matrix denotation. Normal admission
checking, including supported bounded exact leaves, remains separately metered;
this is not a claim that source/IR verification never uses bounded matrices.

The initial profile is a logical IR cost, not device latency or a hardware
T-count. Keep primitive kinds and additional controls explicit. A controlled T
is not one physical T gate; a monomial table/lift is not an already synthesized
gate circuit. Report such nodes separately. Physical gate counts require a
specified target/decomposition profile and inspection of its bound output.

“Large instances” means larger than the dense evaluation limit, while still
inside the verifier's supported width, structure and evidence profile. QLT is
not a route around IR limits. The desired `n=64` arithmetic cost example waits
for a corresponding supported arithmetic/IR profile. Tests must demonstrate
that cost queries do not call matrix evaluation.

### Results and future proofs

| Outcome | Meaning |
| --- | --- |
| `passed` | Every requested assertion for the case was established by the selected evaluator. Rust exact evaluation is a finite implementation result, not automatically a Lean proof. |
| `failed` | An assertion is false; preserve a useful witness such as differing entries, phase or counts. |
| `inconclusive` | The declared resources or later interval bounds did not decide the assertion. Required cases do not pass CI. |
| `error` | Invalid source/IR, unsupported domain/capability, malformed input or evaluator failure prevented evaluation. Required cases do not pass CI. |

Report these separately from assurance: an exact Rust result, a rigorous bound
under stated arithmetic assumptions, and an independently Lean-checked
certificate are different evidence states. No timeout, unknown domain or
evaluation failure may yield partial success for the affected case. Zero
discovered cases must be visible rather than advertised as successful coverage.

The future evaluator theorem must connect the actual evaluation definition to
the same IR denotation used by the quantum soundness proof. For an exact
result `M`, the intended obligation is `eval(p)=M -> M=denote_IR(p)` on checked
inputs, with explicit domain, type and basis premises. Cost evaluation needs
its own correspondence to the declared structural cost model. Source-to-IR
adequacy, theorem-statement review and native compiler/runtime assumptions
remain separate. Moving the implementation to Lean alone proves none of them.

The future [Lean-assisted mathematical debugger](lean-debugger-plan.md) will
consume these results and their evidence status, exposing relevant obligations,
witnesses and source provenance. It does not replace QLT's independent reference
mathematics, promote Rust results to Lean proofs or bypass ordinary verification.
The debugger has its own future 0.x.0 scope, outside the TQL completion gates.

### Later profiles

- Extend from unitaries to isometries, outcome-indexed instruments and channels.
  Compare linear maps on all operators, including off-diagonal inputs and
  arbitrary references. Preserve outcome labels and residual states. Different
  Kraus lists can denote the same channel; list equality is not the criterion.
- Add interval evaluation with inclusion guarantees and an explicit norm,
  input domain and reference/composition bounds. For a certified enclosure
  `[l,u]` of the error, pass when `u <= ε`, fail when `l > ε`, otherwise report
  inconclusive. Entrywise intervals alone are not an operator/diamond-norm proof.
- Extend mathematical references to polynomials, Hamiltonians and matrix
  exponentials. QSVT/Chebyshev examples remain future work with their own
  normalization, parity and approximation contracts.
- Add independent Lean certificate checking bound to actual IR/dependencies,
  reference expression, domain/version, basis order, parameters and error metric.
  It validates the stated instance, not an unstated family theorem. Test
  certificates do not automatically become production contract evidence.

Shot-statistical testing and hardware access are outside the initial QLT
profile. Existing sampling/RNG regression tests remain necessary and unchanged.

## 4. Roadmap and acceptance

| Packet | Intended period | Deliverable and completion gate |
| --- | --- | --- |
| TQL-0: design record | Recorded during 0.2.0 development | This English design, preserved desired sources and semantic faults, explicit execution status, author burden and links from README, roadmap and ledger. No QLT runtime claim. |
| TQL-1: Rust experiment | v0.4.0 or later, after the 0.3.0 type-system work | Freeze the full extension specification, implement exact comparison, structural cost and doctests, then validate QFT2/3 and a separate reversible-arithmetic client against independent oracles. Keep all acceptance paths on checked IR. |
| TQL-2: observations and Lean migration | From 0.5 onward | Add complete instrument/reference comparisons; migrate actual evaluation and cost definitions to the Mathlib-free Lean runtime with separate mathematical bridges, correspondence proofs, audits and differential checks. |
| TQL-3: approximation and certificates | After the required contracts | Add interval bounds, further mathematical references and independent Lean certificate checking; connect relevant evidence to realizability through an explicitly specified interface. |

v0.4.0 is the earliest implementation target, not a promised completion date.
Later packets retain their dependency targets. Follow
[versioning](versioning.md) for each delivered change. TQL-1 does not precede
unfinished [common-QPE/H1–H5 work now targeted for 0.2.1](v0.2.1-plan.md).
QLT migration/proofs are independent targets, not extra requirements for
S05-C1–C5 or PR-C1–C4/V1-C1–C5.

Required experiments for the relevant packet:

1. Reject `.qli` access to QLT facilities and reject invalid ownership,
   contracts/static arguments before obtaining a test descriptor. Check public
   visibility, exact tuple shape and zero-width ownership.
2. Match QFT2/3 against formula-derived DFT and modular increment against its
   independent permutation. Reject inverse-QFT, omitted reversal, wrong scalar
   phase and same-name modified-body expectations. A genuine invalid retained
   certificate must reject at the normal verifier before QLT evaluation.
3. Count shared calls/repeats without matrix construction; check zero repeats,
   invalid dependencies, count overflow and distinct controlled-gate costs.
4. Preserve parameter-specific results, doctest source coordinates, aggregate
   budgets and clear error/inconclusive outcomes. Check 64/65 matrix-dimension
   boundaries separately from the smaller DFT domain boundary.
5. For later instruments, distinguish equal measurement distributions with
   different residual/reference states; allow different Kraus decompositions
   of the same map. For intervals/certificates, reject insufficient bounds,
   changed instances and forged evidence.

Retain original source, actual diagnostics, repairs, independent expected
values and semantic counterexamples. Measure removed host harness code,
duplicate definitions, manual conversions and generation/evaluation cost only
after implementation. No reduction or QLT conformance result is claimed now.
