<a id="段階0-qli-と標準ライブラリの構成"></a>

# Stage 0: `.qli` files and standard-library organization

Current file/module/sealed API contract under [language v0](language-spec.md). [Ledger](stdlib-contracts.md) records twelve ordinary public definitions; [STDLIB.md](../STDLIB.md) fixes contribution/adoption. General APIs remain separate. Explicit schema-2 edition manifests are required by [edition policy](language-editions.md); std is a qrate, other roots remain edition-only pending migration.

<a id="qli-が表すもの"></a>

## What a `.qli` file represents

UTF-8 source, one path-derived module per file and no execution on load. Use explicit public imports, grouped leaves where specified; std is sealed/reserved. Private by default, no dynamic loading/reexports/wildcards, distinct foo and foo:: bar modules. Imported/call cycles reject separately. Language types/forms and Bit/CBit operators need no import; library names do. Bit and CBit do not coerce; no implicit prelude. Classical lets are immutable; host I/O/device failures stay outside pure values. check validates every definition; run requires closed parameterless observe main with finite n-ary classical result and no owners.

| Item | Initial rule |
| --- | --- |
| Module name | Determined by the path relative to the source root. There is no in-file `module` declaration. |
| Source root | The directory supplied to the CLI, conventionally `src/`. Moving its absolute path does not change module names when relative `.qli` paths stay the same. |
| Local import | `use oracle::phase_oracle;` refers to a public declaration in the root's `oracle.qli`; `foo::bar::name` refers to `foo/bar.qli`. Paths are absolute relative to the source root, not relative to the caller. |
| Standard import | The `std::` prefix is reserved for the bundled standard library and cannot be overridden by local files. |
| Visibility | Declarations are private to their module by default. Only `pub` declarations are accessible from other files. |
| Import syntax | Explicit `use path::name;` or grouped explicit leaves such as `use std::quantum::{h,x};`. No wildcard imports, implicit reexports, or cyclic imports. |
| Entry point | Execution requires one parameterless `observe fn main() -> T` in root-level `main.qli`. `T` is `Unit`, `CBit`, or a finite nested classical tuple with immediate arity 2–64. No quantum ownership may remain at termination. Library checking does not require `main.qli`. |
| Packages | An enclosing schema-2 `Qargo.toml` explicitly selects edition `2026`. Resolve source within the supplied root and bundled `std`; external dependency loading remains unsupported. The bundled std qrate has a complete manifest. |

<a id="標準ライブラリの最小構成"></a>

## Source documentation

English Rust-style source doc comments are metadata, not checker/evidence authority. doc parses source and prints documentation only; [attachment/API rules](documentation-comments.md) keep the public AST unchanged.

## Initial standard-library organization

All ordinary source gets the same frontend/IR checks as callers. Primitive signatures/effects/arities live in [sealed inventory](../src/frontend/core.rs), with independently checked lowering. Structural tuple arity/nesting and complete zero-width ownership are retained; A/B signature variables do not create generic source APIs.

| Module | Initial API | Implementation boundary |
| --- | --- | --- |
| `std::basis` | `xor2`, `and2` | Ordinary `.qli` basis functions. They may be noninjective; any enclosing `do/pure` lift must satisfy its own injectivity check. |
| `std::quantum` | `init0`, `h`, `x`, `z`, `t`, `s`, `sdg`, `tdg`, `id`, `phase_eighth`, `cnot`, `toffoli`, `split`, `join` | Sealed source primitives and ownership operations; aliases lower to existing finite IR without new acceptance rules. |
| `std::observe` | `measure_z`, `reset`, `discard` | Sealed observation primitives. Derived measurements can be ordinary definitions, as `measure_x` is in `std::routines`. |
| `std::routines` | `hadamard2`, `reflect_uniform2`, `measure_x`, `measure_z2`, `parity_zz` | Ordinary `.qli` definitions, evaluating shared structures at fixed widths. No added sealed operations. |
| `std::transforms` | `qft2`, `qft3` | Ordinary definitions of two- and three-bit QFT using static control and finite repetition. |
| `std::arithmetic` | `increment2`, `add2`, `mul2_mod15` | Ordinary definitions of total fixed-width reversible arithmetic. Their [contracts](https://github.com/MGYamada/Qleisli/blob/7bfcd36916199b05d5ab11851d38d53375ccf71e/docs/arithmetic-order-finding.md) include overflow and values outside the modular residue range. |

### Exact phase aliases (0.2.4)

Let omega=exp(i pi/4): s=diag(1, i), sdg=diag(1,-i), tdg=diag(1, omega^-1), id_A=I_A and phase_eighth_A=omega I_A, phase/reference exact. Consume/return one binding at the same shape, including Q<Unit>. Aliases expand to existing T chains, id to no instruction and scalar phase to an existing zero-axis Monomial; no checker rule is added. Static transforms accept their specified unary types. Scalar phase in restricted two-argument computed use remains outside that profile; certified equality is separate. No dynamic angle or arbitrary matrix operation is introduced.

| API | Interface | Effect and ownership |
| --- | --- | --- |
| `basis::xor2`, `basis::and2` | Two `Bit` arguments; result `Bit` | Total basis functions, outside the quantum-effect order. Injectivity is not required for a basis declaration. |
| `quantum::init0` | No arguments; result `Q<Bit>` | `Iso`; create a fresh logical wire in `\|0⟩`. |
| `quantum::{h,x,z,t,s,sdg,tdg}` | `Q<Bit> -> Q<Bit>` | `Unitary`; return ownership of the same logical wire. |
| `quantum::{id,phase_eighth}` | `Q<A> -> Q<A>` for every supported finite basis `A`, including `Unit` | `Unitary`; transfer one owner, preserving its exact type tree and wire order; allocate no workspace. |
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

<a id="複数ファイルの実行例"></a>

## Executable examples with multiple files

Examples below use ordinary imported definitions plus sealed primitives; the enclosing source root declares edition 2026. Semantics are checked by the same production verifier.

<a id="bell-状態"></a>

### Bell state

Bell preparation is Iso, CNOT retains owners and measurement Observe consumes both; outputs 00/11 with probability one half, preserving result ordering.

```qli
pub iso fn entangle(q: Q<Bit>) -> Q<(Bit, Bit)> {
    do x <- q;
    pure (x, x)
}
```

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

<a id="位相オラクル"></a>

### Phase oracle

Computed total predicates may be noninjective; reversible XOR into private scratch followed by protected phase and uncomputation supplies exact cleanup. A direct noninjective lift or approximate zero does not.

```qli
use std::quantum::z;

basis fn predicate(x: Bit) -> Bit { not x }

unitary fn phase(a: Q<Bit>) -> Q<Bit> { z(a) }

pub unitary fn phase_oracle(q: Q<Bit>) -> Q<Bit> {
    with_computed(q, predicate) { |a| phase(a) }
}
```

```qli
use oracle::phase_oracle;
use std::quantum::init0;
use std::quantum::h;
use std::observe::measure_z;

observe fn main() -> CBit {
    measure_z(h(phase_oracle(h(init0()))))
}
```

<a id="有限コアv0の後続仕様"></a>

## Specifications after finite core v0

Future sizes, capability/generalized library organization, borrowing and approximation require their own contracts/checking/IR/migration. Until v0.5, add algorithm cases to corpus; no draft name is a public API.
