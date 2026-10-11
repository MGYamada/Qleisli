# Transparent generic provider access: ordinary before-code clarification

This supplements `contract-01.md` under existing Issue #32 before implementing
the provider mask. It is an ordinary implementation decision under the active
development authorization, not a Guardian interpretation or guarantee admission.
Edition 2026, all 111 Issues, their acceptance criteria and proof statuses remain.

The complete original-body checker must not grant an abstract Op additional
access merely because an ordinary wrapper has principal Unitary effect. Body
checking proves that the wrapper's forward source calls use their declared
paths; it does not prove inverse/control paths for opaque actual arguments.

For this bounded implementation, a specialized ordinary transparent provider
has Apply after successful whole-body checking. Its Adjoint and Controlled masks
are each the intersection of that capability on **every supplied actual Op**.
Nat and Basis arguments contribute no capability. With no Op arguments the
intersection is true: closed transparent providers keep their existing
conditional paths, subject to actual retained implementation/materialization,
exact correspondence, capacity and fresh native evidence gates. This source
fact itself supplies no path evidence or accepted handle.

This is conservative rather than maximal capability inference. An unused Op
argument, or a body whose transformations could independently establish a
stronger whole-provider path, can still prevent generic Adjoint/Controlled
use. Such additional paths need explicitly supported whole-implementation
checking; favorable concrete substitution cannot silently authorize a generic
source path. Forward invocation remains available when its actual body rules
and required argument access check, including bodies that apply inverse(U).

Keep original provider identity, actual static specialization sites and located
pending provider/Meaning obligations. Existing concrete gates recheck the real
closed implementation; no identity placeholder, annotation authority, source
retry or native fallback is permitted. A missing generic path is a located
source capability error, distinct from unsupported concrete realization.

The nonnormative `docs/src/design/operations.md` candidate informed review but
does not itself adopt rules. This clarification implements the existing
AGENTS rule that unitarity grants neither inverse nor control access and the
before-code contract's separation of source permissions and actual evidence.
It does not implement general arrows, maximal path inference or their proof
obligations, and grants no Issue completion credit.

Validation must retain a tiny positive forward wrapper with Apply-only U and
negative Adjoint/Controlled uses of that wrapper under the same premises, plus
positive declared-path and closed transparent provider controls. Keep historical
first observations unchanged and report actual results separately.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
