# Exact ordinary Unit pattern first study

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

This informed study precedes the next shared pattern-shape implementation under
Issues #27/#32/#43. The [context](context.md), [source inventory](projects.json)
and [executable/source identity](identity-before.json) were saved before any
check. [session.json](session.json) follows the repository authoring procedure.
Nineteen small original programs were preserved; no source was repaired.

The actual [baseline observations](baseline-summary.json) used the existing
canonical-cutover CLI and kernel, with no Cargo/Lean build. The reused CLI's
original build snapshot is identified separately from repository `bfceca3`;
these observations are not a claim that it was rebuilt from that commit.
All bound source and executable hashes were unchanged during observation.

- Seven desired `attempt-01` programs reject at the finite profile's empty
  pattern restriction: a named Unit parameter followed by `let ()`, nested
  ordinary and mixed-owner products, a basis Unit parameter, a unary Unit
  `with_computed` predicate, coherent Unit lifting after scalar phase, and an
  effectful Unit-returning helper.
- Three separately labelled named-binder controls check successfully, including
  coherent scalar phase and an observing discard helper. This establishes the
  existing execution paths, not the new pattern semantics.
- Eight deliberate counterexamples reject. The nullary predicate reports
  `arity`; seven others currently hit `unsupported` before their intended type
  or effect condition. Later tests must reach and check those conditions rather
  than merely retain the first broad rejection.
- The separately desired `fn f((): Unit, ...)` source reports `parse`. General
  runtime parameter destructuring remains outside this immediate unit. Named
  Unit parameters plus `let ()` and existing basis parameter patterns are in
  scope; this record does not silently change the common grammar.

The intended shared rule matches an empty pattern only to exact ordinary Unit,
and a nonempty tuple pattern only to the same immediate tuple arity. Recursion
checks children at existing binder boundaries. Bit, Bits<0>, Q<Unit> and
Q<Bits<0>> are not ordinary Unit; width is never a matching criterion. A
coherent `do () <- q; pure ()` matches the ordinary basis of Q<Unit> inside the
existing checked lift and returns the owner. It does not justify the runtime
`let () = q`.

Implementation validation must inspect retained native operations and exact
phase/reference action. In particular, an effectful Unit-returning RHS must run
before its result is bound, and coherent scalar phase must survive the lift.
Original first sources and diagnoses stay fixed; later validation or new oracle
sources must be recorded separately. No universal source preservation or new
constitutional guarantee is claimed here.
