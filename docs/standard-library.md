<a id="段階0-qli-と標準ライブラリの構成"></a>

# Stage 0: `.qli` files and standard-library organization

Status: **Stage 0 organization fixed; ordinary definitions added** (2026-09-26).
Following the [design principles](design-philosophy.md), this document defines
file rules, initial APIs, and the boundary around sealed built-ins. Its file,
module, and sealed-API rules form part of the [finite core v0 specification](language-spec.md).
This English edition is authoritative and replaces the earlier Japanese edition
without changing those rules. The [frontend](frontend-v0.md) checks v0 source
within its capacity limits and lowers it to [finite IR](ir-prototype.md).
The executable basic examples and [structured algorithms](algorithm-routines.md)
use the same checks; the latter reuse ordinary definitions in `std::routines`.

The [Layer 3 plan](stdlib-roadmap.md) describes seven areas from primitives to
algorithm skeletons and hybrid plans, with semantic contracts and adoption
criteria. The [contract ledger](stdlib-contracts.md) records the 12 bundled
public definitions. Proposed metatypes are distinct from current APIs, and
host-side trials and statistical processing remain outside `.qli` operations.

The [0.2.0 type contract](type-system.md) preserves tuple arity and nesting.
Every binary signature below, including `split`, `join` and `toffoli`, retains
its explicit shape. N-ary callers use [checked explicit conversions](tuple-shapes.md);
no implicit flattening or new sealed operation is introduced.

<a id="qli-が表すもの"></a>

## What a `.qli` file represents

A `.qli` file is UTF-8 **Qleisli source**, not quantum-state data, a circuit
binary, IR, or an execution result. One file defines one module. Top-level
items are `basis fn`, `iso fn`, `unitary fn`, `observe fn`, and `use` only.
There is no execution on load, global mutable state, I/O, or implicit qubit
allocation. A `let` binds a name to a value, not to a mutable cell.

| Item | Initial rule |
| --- | --- |
| Module name | Determined by the path relative to the source root. There is no in-file `module` declaration. |
| Source root | The directory supplied to the CLI, conventionally `src/`. Moving its absolute path does not change module names when relative `.qli` paths stay the same. |
| Local import | `use oracle::phase_oracle;` refers to a public declaration in the root's `oracle.qli`; `foo::bar::name` refers to `foo/bar.qli`. Paths are absolute relative to the source root, not relative to the caller. |
| Standard import | The `std::` prefix is reserved for the bundled standard library and cannot be overridden by local files. |
| Visibility | Declarations are private to their module by default. Only `pub` declarations are accessible from other files. |
| Import syntax | Only explicit `use path::name;`. No wildcard imports, implicit reexports, or cyclic imports. |
| Entry point | Execution requires one parameterless `observe fn main() -> T` in root-level `main.qli`. `T` is `Unit`, `CBit`, or a finite nested binary product of classical types. No quantum ownership may remain at termination. Library checking does not require `main.qli`. |
| Packages | No external dependencies or manifest in this version. Resolve only `.qli` files within the supplied root and bundled `std`. |

The checking/execution commands are `qleisli check src` and `qleisli run src`. `check` checks
types, effects, and ownership in all source declarations and independently
verifies the IR generated for every ordinary function. `run` checks all
declarations, then interprets the closed program in `main.qli`. Features beyond
the [supported subset](frontend-v0.md) receive diagnostics. Displaying results,
choosing host execution counts, and submitting work to devices are host duties.
`src/lib.qli` is an optional library naming convention. `foo.qli` and
`foo/bar.qli` define distinct modules `foo` and `foo::bar`, without implicit
parent/child visibility. Cyclic module imports and recursive function calls
are checked separately.

Missing imports, private names, name collisions, and cyclic imports produce
diagnostics with source locations. Modules are not loaded dynamically.
Unsupported device capabilities and host I/O failures must be diagnosed before
execution or reported as host failures, not hidden inside pure `.qli` values.

Types `Unit`, `Bit`, `CBit`, and `Q<A>`, and language forms such as `if` and
`do/pure`, require no import. `Iso<A,B>` and `Unitary<A,B>` are explanatory
metanotation for static function classifications, not first-class source value
types. Operators `not`, `and`, and `xor` are built in for basis `Bit` expressions
and, separately, ordinary `CBit` expressions. Ordinary `true` and `false`
literals have type `CBit`; the basis literals `0` and `1` have type `Bit`.
There is no implicit conversion between `Bit` and `CBit`, and no implicitly
opened `std::prelude`: library functions require explicit imports.

<a id="標準ライブラリの最小構成"></a>

## Source documentation

Bundled `.qli` uses Rust-style `//!` module descriptions and `///` function
documentation. [Block forms, inner/outer attachment, API and migration](documentation-comments.md)
are specified separately. All four source files and all twelve public/three
private definitions are documented in English. Read a file's documentation with
`qleisli doc stdlib/src/routines.qli`, or use the parser's documented-module API.
This output describes source; it does not check contracts or execute examples.
The existing [contract ledger](stdlib-contracts.md) remains authoritative.
Documentation grants no stdlib-specific exemption or evidence authority.

## Initial standard-library organization

| Module | Initial API | Implementation boundary |
| --- | --- | --- |
| `std::basis` | `xor2`, `and2` | Ordinary `.qli` basis functions. They may be noninjective; any enclosing `do/pure` lift must satisfy its own injectivity check. |
| `std::quantum` | `init0`, `h`, `x`, `z`, `t`, `cnot`, `toffoli`, `split`, `join` | Sealed primitive and ownership-structure operations. Derived operations such as `s(q) = t(t(q))` can be ordinary definitions; `s` is not a bundled public name. |
| `std::observe` | `measure_z`, `reset`, `discard` | Sealed observation primitives. Derived measurements can be ordinary definitions, as `measure_x` is in `std::routines`. |
| `std::routines` | `hadamard2`, `reflect_uniform2`, `measure_x`, `measure_z2`, `parity_zz` | Ordinary `.qli` definitions, evaluating shared structures at fixed widths. No added sealed operations. |
| `std::transforms` | `qft2`, `qft3` | Ordinary definitions of two- and three-bit QFT using static control and finite repetition. |
| `std::arithmetic` | `increment2`, `add2`, `mul2_mod15` | Ordinary definitions of total fixed-width reversible arithmetic. Their [contracts](arithmetic-order-finding.md) include overflow and values outside the modular residue range. |

`Q<A>` denotes owned quantum resources, and each quantum argument is transferred
linearly. The following interfaces summarize types and effects; the
[v0 specification](language-spec.md) supplies exact typing rules. A product
domain is **semantic metanotation**, not an instruction to pack multiple source
arguments into one tuple. For example, `xor2(x: Bit, y: Bit)` has two parameters,
whereas `f((x,y): (Bit,Bit))` has one patterned basis parameter. `cnot` and
`join` take two arguments; `toffoli` takes three; `parity_zz` takes two. Every
other ordinary quantum API listed here takes one argument.

| API | Interface | Effect and ownership |
| --- | --- | --- |
| `basis::xor2`, `basis::and2` | Two `Bit` arguments; result `Bit` | Total basis functions, outside the quantum-effect order. Injectivity is not required for a basis declaration. |
| `quantum::init0` | No arguments; result `Q<Bit>` | `Iso`; create a fresh logical wire in `\|0⟩`. |
| `quantum::{h,x,z,t}` | `Q<Bit> -> Q<Bit>` | `Unitary`; return ownership of the same logical wire. |
| `quantum::cnot` | Arguments `Q<Bit>, Q<Bit>`; result `(Q<Bit>,Q<Bit>)` | `Unitary`; require distinct wires. |
| `quantum::toffoli` | Three `Q<Bit>` arguments; result `((Q<Bit>,Q<Bit>),Q<Bit>)` | `Unitary`; all three wires must be distinct. Results use nested binary products. |
| `quantum::split` / `join` | `Q<(A,B)> -> (Q<A>,Q<B>)` / arguments `Q<A>,Q<B>` returning `Q<(A,B)>` | `Unitary` ownership-structure operations; preserve amplitudes and correlations in the specified wire order. |
| `observe::measure_z` | `Q<Bit> -> CBit` | `Observe`; consume the logical wire and return only its classical result. |
| `observe::reset` | `Q<Bit> -> Q<Bit>` | `Observe`; discard the old state and its correlations, returning a fresh logical wire in `\|0⟩`. |
| `observe::discard` | `Q<A> -> Unit` | `Observe`; consume the wires by partial trace. |
| `routines::hadamard2` | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>` | `Unitary`; apply H to both wires and return all ownership. |
| `routines::reflect_uniform2` | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>` | `Unitary`; reflect with the uniform state as the positive eigenspace, preserving the specified phase. |
| `routines::measure_x` | `Q<Bit> -> CBit` | `Observe`; measure in the X basis and consume the input. |
| `routines::measure_z2` | `Q<(Bit,Bit)> -> (CBit,CBit)` | `Observe`; measure both wires in Z order from left to right and consume them. |
| `routines::parity_zz` | Arguments `Q<Bit>,Q<Bit>`; result `((Q<Bit>,Q<Bit>),CBit)` | `Observe`; retain both separately owned data wires and measure/consume an internal meter. |
| `transforms::qft2` | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>` | `Unitary`; positive-sign four-dimensional QFT, returning all ownership. |
| `transforms::qft3` | `Q<((Bit,Bit),Bit)> -> Q<((Bit,Bit),Bit)>` | `Unitary`; positive-sign eight-dimensional QFT, returning all ownership. |
| `arithmetic::increment2` | `Q<(Bit,Bit)> -> Q<(Bit,Bit)>` | `Unitary`; add one modulo four and return both wires. |
| `arithmetic::add2` | `Q<((Bit,Bit),(Bit,Bit))> -> Q<((Bit,Bit),(Bit,Bit))>` | `Unitary`; retain the first two-bit number and add it to the second modulo four; return all four wires. |
| `arithmetic::mul2_mod15` | `Q<((Bit,Bit),(Bit,Bit))> -> Q<((Bit,Bit),(Bit,Bit))>` | `Unitary`; multiply values below 15 by two modulo 15 and fix 15; return all four wires. |

The names and widths in `routines` are initial implementation contracts, not a
decision on generalized combinators. Their [individual contracts](algorithm-routines.md#公開apiの契約)
record acceptance, rejection, whole-system meaning, and existing IR expansion.
The private `nonzero2(a: Bit,b: Bit) -> Bit` is a total ordinary basis function
used as an auxiliary predicate. Private bundled declarations follow normal
visibility rules.

`std::` ships with the compiler version. User replacement and external package
loading are unavailable. Ordinary `.qli` bodies cannot impersonate primitive
gate matrices, observation semantics, or ownership transitions merely by using
standard-looking names. Bundled definitions receive the same checks as user code.

After `measure_z`, the old logical wire cannot be used. Prepare a new logical
wire with `init0` if needed and classically control it with the measurement
result. A future backend may map the new wire to a previously measured physical
device when its capabilities permit.

Ordinary definitions reside in `stdlib/src/basis.qli`, `routines.qli`,
`transforms.qli`, and `arithmetic.qli`. Rust's module resolver registers the
sealed public names in `std::quantum` and `std::observe`; their public signatures
are tied to these module identities. Derived bodies remain ordinary checked source.

`do/pure` (including its injectivity check), `qif`, `adjoint`, `repeat_static`,
`with_computed`, and `apply_contract` are statically checked **language forms**. They are not
ordinary functions taking arbitrary first-class operation values. `release0`
describes an internal, evidence-dependent step inside the atomic auxiliary
constructor, not a standalone public API. Hardware backends are also outside
the standard library.

The [static-operation contract](static-operations.md) specifies the implemented
finite forms, QFT phases and bit order, acceptance/rejection, and lowering.
Targets are statically resolved function names with a single `Q<A> -> Q<A>`
interface and no classical parameters. General higher-order operation values
remain unimplemented.

The [function-contract form](function-contracts-v0.1.md) separately names an
ordinary implementation and a fixed ordinary specification. It checks their
exact meaning and retains evidence in final IR; it does not add a sealed gate
or change the contract ledger's list of bundled definitions.

<a id="複数ファイルの実行例"></a>

## Executable examples with multiple files

The following blocks reproduce the named files. Their paths and imports follow
the rules above. The test
[`documented_projects_compile_verify_and_simulate`](../tests/compile.rs)
checks the projects' source acceptance, IR verification, and result distributions.

<a id="bell-状態"></a>

### Bell state

`examples/bell/bell.qli`:

```qli
pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}
```

`examples/bell/main.qli`:

```qli
use bell::entangle;
use std::quantum::init0;
use std::quantum::h;
use std::quantum::split;
use std::observe::measure_z;

observe fn main() -> (CBit, CBit) {
    let pair = entangle(h(init0()));
    let (left, right) = split(pair);
    (measure_z(left), measure_z(right))
}
```

The results `(0,0)` and `(1,1)` each have probability `1/2`. The map
`x -> (x,x)` is checked for injectivity; it does not duplicate quantum ownership.

<a id="位相オラクル"></a>

### Phase oracle

`examples/phase_oracle/oracle.qli`:

```qli
use std::quantum::z;

basis fn predicate(x: Bit) -> Bit { not x }

unitary fn phase(a: Q<Bit>) -> Q<Bit> { z(a) }

pub unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| phase(a) }
}
```

`examples/phase_oracle/main.qli`:

```qli
use oracle::phase_oracle;
use std::quantum::init0;
use std::quantum::h;
use std::observe::measure_z;

observe fn main() -> CBit {
    measure_z(h(phase_oracle(h(init0()))))
}
```

Since `predicate(x) = not x`, the oracle's matrix is `-Z`. This closed example
returns `1`. Source v0 hides the computation source and other outer quantum
values from the auxiliary body and accepts only an expanded `Z/T` sequence
on the auxiliary. General work registers and borrowing signatures are deferred.

The total mathematical functions `xor2` and `and2` have noninjective product
domains, so their full maps cannot define isometric lifts
`Q<(Bit,Bit)> -> Q<Bit>`. This semantic fact must be distinguished from a
surface-call error: in `do p <- q; pure xor2(p)` (or `and2(p)`), the function
expects **two** arguments but receives one product argument, so the compiler
reports `Arity` before injectivity is relevant. Explicit destructuring in the
lift binder makes the components available: `do (a,b) <- q; pure xor2(a,b)`
is well typed as a basis computation, but its full map fails the lift's
injectivity requirement; the same applies to `and2(a,b)` on that product domain.
There is no implicit uncurrying of `xor2(p)`. Calls with two basis `Bit`
expressions are valid syntax, and every enclosing lift checks the complete
resulting map for injectivity. `with_computed(q,xor2)` instead uses the predicate's
semantic product domain and is supported for `q:Q<(Bit,Bit)>`.

Likewise, `(q,q)` is rejected for reusing the same ownership. Importing a bundled
name never relaxes resource or quantum conditions.

<a id="有限コアv0の後続仕様"></a>

## Specifications after finite core v0

- General borrowing and preservation-effect signatures for `with_computed`.
  The restricted v0 form and static-operation grammar are already fixed.
- Sized registers, general operation parameters, and arbitrary angles.
  Literal-count finite repetition is already implemented.
- Higher-order functions, external packages, manifests, and further modules.

Stage 1 specification and proof work take priority over these extensions and
API generalization. Future decisions must still satisfy the
[quantum-language requirements](quantum-language-requirements.md).

Future candidates follow the [English language evolution framework](language-evolution.md). They are not adopted APIs. Complete and review the six imaginary algorithm drafts required [before v0.2.0](release-milestones.md#pre-v020-imaginary-v1-code), then select and specify the smallest necessary generalization. Existing finite-core maintenance and Stage 1 proof work may continue in parallel.
