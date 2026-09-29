# Serialized finite meaning and reconstruction

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

The pure finite request retains implementation and mathematical-description
bytes, while the initial Rust adapter takes a `Matrix` directly. Specify and
implement a bounded exact matrix description so both complete byte strings
can be freshly read by the transitional finite checker. This is an additive
transport for the existing scalar domain, not a new semantic acceptance rule.

Use a strict versioned JSON envelope, row-major entries and four independent
canonical dyadics per scalar. Retain the full existing i128 numerator and
126-bit denominator capacity without introducing a common denominator.
Decode under the caller's aggregate exact budget; reject excess dimensions,
unknown fields/domains/versions, noncanonical dyadics and invalid JSON. Decoding
alone does not prove an equation or unitarity.

The new adapter decodes the exact description, reconstructs the complete QIRF
and embedded evidence, compares the exact matrices and retains both immutable
byte strings plus the full boundary. Preserve the six-bit/64-dimensional and
ten-million-unit finite limits, and the hierarchy's 16 MiB payload ceiling.
No hash, producer success flag or old in-memory receipt authorizes acceptance.

Validate handwritten descriptions, unequal dyadic exponents and capacity
edges, malformed fields, row/column orientation, global-phase mutations,
shared budgets, fresh-process reconstruction and whitespace binding. Preserve
the first source before checking and record actual diagnostics. The full
Lean-request host transport and its mathematical correspondence remain open;
this helper must not return a whole-hierarchy seal or enable external schemas.
