# Actual first parameter-declaration observations

Root executed the frozen driver once before the production refactor. Its actual
process exited 0 after **40 checks: 4 successful, 36 rejected, 44 native calls**.
All34 frozen files and238 selected external source/CLI/native/contract identities
remained unchanged. No first source repair, runtime execution or emit occurred.
The selected CLI was the observed MSRV build whose SHA-256 is
`4a5cc9e753268fd7b0b4972cf84dd1fd6338218bc0b104d71b8465fab89151cf`;
it is not a complete build-closure or compiled-Git-HEAD attestation.

Text and JSON were captured separately for finite and selected-auto checks:

| Case | Finite JSON observation | Selected JSON observation |
| --- | --- | --- |
| Repeated static Nat | Earlier finite Nat-profile rejection | name, duplicate static parameter n, whole function span |
| Repeated static Op<Unit> | ownership, duplicate static parameter, repeated Ident span | name, duplicate static parameter U, whole function span |
| Static/runtime U collision | ownership, duplicate parameter name | name, binding U shadows a static parameter/index or discards a value |
| Nested repeated runtime a | ownership, duplicate parameter name | name, duplicate runtime parameter |
| Missing first type, later duplicate | Earlier named-Basis profile rejection | Earlier resolved projection type rejection: Missing names no Basis parameter |
| Symbolic n-1 first type with n == 0, later duplicate | Earlier finite Nat-profile rejection | size, subtraction lacks a nonnegative guard, before later runtime duplicate |
| Earlier duplicate, later Q<Bits<0>> | Earlier register-profile rejection | name, duplicate runtime parameter |
| Operation kind before its Nat | Earlier register-profile rejection | static, unknown natural name n |
| Invalid unused sibling | ownership, duplicate parameter name; one earlier native call | name, duplicate runtime parameter; zero native calls |
| Exact nested Unit/quantum and separate Unit argument | Success;20 native calls | Success;1 native call |

The successful case has two independent quantum owners and preserves one exact
nested typed pattern as one argument. Its success is not an independent
algorithm oracle. Selected output explicitly records producer-consistency,
request_origin producer and source_meaning_verified false. The native decisions
do not prove complete source preservation or discharge QS/PR/RS/EXACT.

Earlier profile/projection rejections must not be counted as downstream name
or type checks. The separate symbolic negative reaches the first argument's
nonnegative-size obligation, providing a real ordering control. Unused finite
preparation may check an earlier entry before rejecting a sibling; no complete
preparation succeeds in that case. Raw stdout/stderr, primary paths/spans,
exits and exact native argv are retained without normalization in before/.

The original first map, predicted plan and frozen session.before.json remain
unchanged. session.json contains only the actual40 observations. This informed
study is not a blind model benchmark, general family proof, common-checker or
#32/#317 completion. All111 selected Issues and24 #317 criteria remain required.

Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0.
