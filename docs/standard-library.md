# Files, modules and bundled standard library

[Language v0](language-spec.md) fixes sealed signatures and forms;
[ledger](stdlib-contracts.md) fixes twelve ordinary public definitions.
General adoption follows [STDLIB.md](../STDLIB.md).

## File and module contract

UTF-8 .qli files define one path-derived module each; loading executes nothing.
The CLI supplied root fixes absolute module paths: oracle.qli is oracle,
foo/bar.qli is foo::bar. Moving the absolute root preserves relative identities.
foo and foo::bar are distinct modules, without implicit hierarchy/imports.
Default discovery remains root-relative; explicit --qrate selects [source].root.
[Edition](language-editions.md) requires schema-2 edition 2026. std has a complete
qargo-compatible manifest; other trees retain edition-only manifests pending migration.
No repository-root manifest or external dependency loader is supported.

Declarations are private unless pub. Explicit use path::name or grouped explicit
leaves resolve public declarations; no wildcard, reexport, dynamic loading or implicit
prelude. std is reserved/sealed, never overridden by local files. Import/call cycles
reject separately. Types/forms and Bit/CBit operators require no import; library
names do. Basis Bit and runtime CBit do not coerce. Classical lets are immutable;
host I/O/device failures remain outside pure values.

check validates all definitions without requiring main. run requires parameterless
observe main in root main.qli returning Unit/CBit/finite classical products, arity
2–64, and no remaining owners. [Source doc comments](documentation-comments.md) are
English metadata, never checker/evidence authority; doc parses and prints only.

## Initial standard-library organization

| Module | Public names |
| --- | --- |
| basis | xor2, and2 |
| quantum | init0, h, x, z, t, s, sdg, tdg, id, phase_eighth, cnot, toffoli, split, join |
| observe | measure_z, reset, discard |
| routines | hadamard2, reflect_uniform2, measure_x, measure_z2, parity_zz |
| transforms | qft2, qft3 |
| arithmetic | increment2, add2, mul2_mod15 |

Sealed [core inventory](../src/frontend/core.rs) and [language contracts](language-spec.md)
fix primitive arities/effects. Ordinary source undergoes the same checks as callers;
basis definitions need totality, not injectivity until lifted. Tuple arity/nesting,
correlations, ordered axes and zero-width owners survive every operation. Signature
metavariables do not create generic user declarations. Measurements consume owners;
reset replaces the old correlated state with fresh zero, discard takes partial trace.

### Exact phase aliases

omega=exp(i pi/4): s=diag(1,i), sdg=diag(1,-i), tdg=diag(1,omega^-1),
id_A=I_A, phase_eighth_A=omega I_A. Each transfers one same-tree owner, including
Q<Unit>, allocating no scratch. Aliases expand to existing T chains, id to no
instruction, scalar phase to a zero-axis Monomial. Static transformations accept
specified unary types. Scalar phase is outside restricted computed identity/Z/T
use; certified equality remains separate. No dynamic angle, arbitrary matrix or
new acceptance rule is introduced.

## Executable examples

[Examples](../README.md#try-it) retain complete multi-file source and manifests.
Bell preparation uses an injective do/pure basis lift, H and ordered measurements,
returning 00/11 with probability 1/2. The phase-oracle example computes a total
possibly noninjective predicate into private scratch, applies protected Z and
uncomputes exactly; interference returns 1. Direct noninjective lift/approximate
zero cannot replace those contracts. [Quick reference](qli-quick-reference.md)
provides copyable CI-checked syntax.

## Specifications after finite core v0

Sizes, capabilities, borrowing, approximation and generalized organization need
separate source/IR contracts, independent checking and migration. Until v0.5 add
algorithm experiments to corpus; draft vocabulary is not a shipped API.

<a id="exact-phase-aliases-024"></a>
