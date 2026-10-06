# Authored test migrations and coherent-label index repair

This packet records ordinary repairs under the recorded complete-original-AST
contract. It is not a new decision, guarantee or execution result. The author
did not run formatting, Cargo, tests, CLI, Lean, native checking or Git.
Root owns later formatting and validation.

`before/` and `before.json` retain the four original test files and resolver
bytes read before their edits. `after-authored/` and `after-authored.json` record
the authored barrier, which precedes root formatting. Both original 3,000-file
project stress functions remain byte-for-byte unchanged and unexecuted; root's
validation driver retains its two explicit skips. The first combined patch
failed atomically on a resolver context typo; the five pre-edit hashes were
rechecked unchanged before the corrected patch was applied.

The small project import cycle now loads successfully, while a real two-Basis
call cycle still rejects at its closing call. A separate three-module import
cycle exercises the small-stack loader without generating the historical stress
cases. Shared-resolution controls preserve explicit filesystem/selected module
name policies, reject both public/private self-imports at the final member, and
exercise moved-local and call-cycle failures through both source consumers.

The retained mixed source maps now fail complete parsing at the original
malformed EOF (byte 114) before projection eligibility. Their first sources,
old diagnostic records and all frozen authoring packets remain unchanged.
Declaration tests preserve `visibility`, `name` and missing-access categories;
they adopt shared wording and final-member, access-keyword or whole-use spans.
Finite checks now also inspect missing capabilities in the existing dead-arm
and zero-fold sources. Core diagnostic-category repairs belong to agent A;
these assertions are not relaxed to accept `module` for private/name errors.

The unused `Resolution::modules` wrapper has no actual consumer and is removed.
The separately authorized coherent-label regression adds `EnterBasis` only
after evaluating a coherent lift's input. It moves outer Runtime/Basis names
into the existing frame undo records, retains actual static/FoldIndex identities,
and restores the exact outer map on exit. Visits and new retained cells are
charged before mutation/allocation. Original Binder/Use IDs and the authoritative
Table are retained; this does not introduce runtime global fallback.
The preceding lexical cleanup identity is recorded as a previously observed
barrier, not misrepresented as a newly captured before byte snapshot.

No native rule, accepted handle, proof discharge, source-preservation guarantee,
Issue completion credit or release claim follows from these authored changes.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
