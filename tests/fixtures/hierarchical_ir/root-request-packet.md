# Independently requested hierarchy roots

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The reconstruction host currently proves consistency only with the artifact's
own meaning table. Add a separate independently supplied request containing
the required physical interface, effect, proof kind and a rooted meaning DAG.
Do not infer or replace those requirements from the submitted artifact.

Use an untrusted graph-pairing proposal to relate actual and requested meaning
nodes. The pure Lean checker must compare every complete interface and every
non-reference constructor parameter, and check corresponding ordered children.
Permit different numbering and sharing in either direction; a node pair can be
shared, but no pair cache or claimed equality is an input. Check the proposal's
complete rooted dependency graph and coverage of the requested table under the
same aggregate structural budget as the artifact. Bind pair zero to the actual
entry proof's meaning and independently requested entry, kind/effect/interface.

Finite descriptions may differ in JSON whitespace while denoting the same
exact matrix. Retain both actual byte strings as explicit finite meaning
equality obligations. The Rust host must freshly decode and compare them in
the existing exact domain and shared budget; no floating tolerance or equality
modulo phase is permitted. This is the existing transitional Rust finite premise,
not a new unchecked meaning predicate or a serialized success flag.

Prove that checked node pairs have equal partial denotations for every fuel,
conditional only on these actual finite equality obligations. Compose that
result with the actual conditional artifact acceptance theorem to bind the
common implementation operator to the requested root. Preserve phase and
arbitrary reference systems. No assumed whole-graph environment is sufficient.

Connect a new host API and private runtime message while retaining the existing
inspection API and protocol unchanged. Independently authored requests must
detect coordinated implementation/declared-meaning changes, wrong root type,
effect, kind, counts, polarity and phase. Include reindexing, differing sharing,
malformed pair proposals, missing coverage and shared budget limits. Save first
sources and actual diagnostics, build/audit both packages, replay kernel and
transport, and run native and Rust regressions. All external schemas and the
remaining profile/sized-source/corpus gates remain pending.
