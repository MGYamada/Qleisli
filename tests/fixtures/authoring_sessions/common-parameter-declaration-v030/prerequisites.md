# Existing contracts and unexecuted predictions

**Status: non-normative preparation. Every prediction below is unobserved.**
The normative [type model](../../../../docs/src/reference/type-model.md) and
[source text](../../../../docs/src/reference/source-text.md) require one typed
pattern to remain one argument, complete parameter-name uniqueness, separation
from static names, earlier-parameter kind dependencies, exact ordinary Unit
shape and retained quantum owners. All supplied declarations remain checked,
including private unused siblings. These rules grant no new source form or
backend capability.

The proposed sharing must preserve the existing caller's insertion set,
left-to-right traversal, source identity, per-argument stage, error location
and capacity/profile ordering. Finite currently seeds runtime uniqueness with
static names. Sized uses a runtime-only set; its value binder separately rejects
static collisions after type checks. Static duplicate categories/spans also
differ. Recording those differences is not an ordinary migration decision.

| First project | Existing contract and code-derived prediction, not a result |
| --- | --- |
| duplicate-static-natural | Repeated static n is invalid. Finite is predicted to reject static Nat at profile preflight; selected checking should report a duplicate static name at the complete function span. The finite result cannot test its later static-name claim. |
| duplicate-static-operation-unit | Both static parameters have Op<Unit>, within the finite source kind grammar. Predicted finite ownership / duplicate static parameter at the second U; selected name / duplicate static parameter U at the function span. This separate case targets the finite name claim directly. |
| static-runtime-collision | Static U and runtime U cannot coexist as parameters. Predicted finite ownership / duplicate parameter name; selected name / binding U shadows a static parameter/index or discards a value, at the runtime name. The rejected private declaration must not be rescued by selecting entry. |
| nested-runtime-duplicate | The later a in (a,((),a)) repeats the first a. Predicted finite ownership / duplicate parameter name versus selected name / duplicate runtime parameter, both locating the later leaf. Unit consumes no name and the tree remains one runtime argument. |
| first-type-before-later-duplicate | The first type Missing is not declared as Basis. Finite named-Basis profile rejection is predicted before parameter-name checking. Selected resolved projection is predicted to report type / Missing names no Basis parameter before check::declaration. This controls an earlier projection/type gate; it does not isolate a per-argument type check inside declaration. |
| symbolic-type-before-later-duplicate | The unused generic sibling has first: Q<Bits<n - 1>> before two q parameters and the feasible premise n == 0. Finite static-Nat profile rejection is predicted. Selected declaration should scan first, then reject size / subtraction lacks a nonnegative guard before advancing to later duplicate q. This is the separate per-argument scan/type/next control; no invalid-width system is instantiated. |
| duplicate-before-empty-register | The first ordinary tuple repeats q, while a later argument has Q<Bits<0>>. Finite is predicted to reject its register-type profile before signature uniqueness. Selected checking is predicted to reject the earlier repeated q. Width zero remains a logical-owner obligation; an earlier rejection proves no later owner rule. |
| forward-operation-kind | Op<Bits<n>> is declared before n:Nat. Finite static/register profile rejection is predicted; selected checking should reject the unavailable preceding natural in the operation kind. The n <= 2 premise bounds the intended family and cannot legalize forward kind access. No concrete family instance is requested. |
| unused-invalid-sibling | entry is valid intended identity source; never-called unused repeats q across two parameters. Complete preparation must reject the private sibling. Predicted native call counts are deliberately absent: finite may check another declaration first, while selected source preparation should reject before native instance acceptance. Capture the actual order/counts. |
| valid-nested-unit-quantum | (((a,()),b), then a separate ():Unit parameter) retains two Q<Bit> owners and two ordinary Unit components. Returning (a,b) should pass source checks if the current selected target supports this exact interface. Success would be a checking control, not a semantic proof or general eligibility claim. |

The sources use current syntax rather than invented convergence notation.
Generic-invalid cases have a separate non-generic public entry, so missing
host-supplied static bindings should not mask their required all-declaration
checks. No static lookup by spelling, cached signature, truncated zip or
omitted unsupported declaration is permitted to replace the actual source.

Root's later 40 fixed observations will decide which existing stages are
actually reached. Predictions are never executable assertions or fabricated
diagnostics. Genuine unsupported errors, JSON/text, native argv and counts must
be retained. The study neither completes the common checker nor exposes
canonical QFT/stdlib APIs, changes accepted handles, or discharges QS/PR/RS/EXACT.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
