# v0.2.2 issue regressions

[Issue #55](https://github.com/MGYamada/Qleisli/issues/55): valid unnamed LLVM
blocks collided on the empty display name. `qir-unnamed.ll` preserves the
reproduction from the project's independent QIR fixture. Text/bitcode and mixed
chains now agree; actual cycles and unvisited blocks still reject.

[Issue #56](https://github.com/MGYamada/Qleisli/issues/56): interop lost artifact
pointers and OpenQASM spans. `qasm-unknown.qasm` preserves the token error.
[Before](before.json) and [after](after.json) record the actual outcomes.
The shared malformed-root experiment now produces identical `related` pointers
through verify-ir and interop; file/stdin Unicode/CRLF locations and Python
retention have regressions in [Rust](../../connections.rs) and
[installed Python tests](../../../scripts/test_connections.py).

[Validation](validation.json) records commands, environment, limits and document
reduction. These are local unreleased repairs, not a new publication or compiler
soundness proof. No new maximum-size corpus cases were generated.
