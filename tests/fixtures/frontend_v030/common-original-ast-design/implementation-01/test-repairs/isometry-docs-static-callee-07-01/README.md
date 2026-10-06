# Actual07 static-callee message correction

Only the last `adjoint(g,q)` message assertion changes. Actual07 already
passed its `type` category and original `g` token span assertions before
reporting the message mismatch. That static operation uses the dedicated
wrong-category message: `static operation requires a function name, not a
local value`. The two ordinary runtime `h(q)` assertions keep `a local value
is not callable`. Every original source and moved-owner control is unchanged.

The original formatted actual07 test, exact raw failure excerpt/offsets and
authored after bytes are preserved here additively. No formatting, Rust test,
CLI/native or Lean execution occurred during this repair; root owns validation.
No acceptance, proof, guarantee, Issue completion or release claim follows.
