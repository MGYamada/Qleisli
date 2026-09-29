# Measured QPE checkpoint — 2026-09-30

Work stops here at the user's request, after preserving the initial source and
diagnostic. The v0.2.1 objective is unfinished; resume only when requested.

The [first source](attempt-01/readout.qli) is a desired wrapper, not an executable
project: its register helpers are not implemented. The [actual first check](first-check.json)
exits with `unsupported or duplicate import registers::init_zero`. It does not
reach measurement lowering or prove anything about the wrapper's meaning.

Source inspection identifies the next gap. Existing hierarchical `init0` and
`observeZ` nodes have typing checks, but the ordinary semantic rules accept
unitary equations. Structural conversions are quantum-only, and classical
rewiring preserves individual slot types; neither assembles measured `CBit`
values into `CBits<m>`. No checker, runtime or proof implementation was changed
in this checkpoint.

On resumption, specify an explicit, compatible assembly/checking interface
before implementation. A separate readout interface is a candidate, not an
adopted public API. Bind measurement targets and order, low-bit-first result
assembly and all surviving owners to actual nodes. Initialization, the shared
pure QPE body, the complete outcome/residual-target instrument with reference
systems, and production execution remain required. Preserve zero-width owners
and existing public APIs. Use small-system cases under the user's validation
scope; do not start further maximum-size checks.
