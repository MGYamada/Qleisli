# Context: linear-size register reshape

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0

Informed desired-source work after reading the user's linear-arithmetic/reshape
review, the existing intact-atom helper, sized-Xor failure and adopted design
in docs/size-expressions.md. Current parser limitations were known. No external
model or controlled authoring benchmark was used. The exact deployed model and
sampling settings are unrecorded.

Save and hash the first source before checking. `reshape::<...>` is desired
spelling, not an implemented API. The complete single-owner type and ordered
axes must be preserved by independently checked structural lowering. The split
has label x = low + 2^n * high with low on the first axes; merge is its inverse.
The doubled and successor examples exercise constant multiplication and n+1.
CBits is the adopted classical spelling. No upstream program was copied.

Required later cases include n or m equal to zero, zero-width ownership,
both bit orders, phase/reference coefficients, fresh owner IDs, commuted size
sums without permuting axes, missing size premises and unsupported symbolic
products. The zero-input main only demonstrates desired source reuse and cannot
establish these semantics. Production hierarchy, G020-1 and H1–H5 remain pending.
