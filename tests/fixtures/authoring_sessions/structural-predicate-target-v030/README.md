# Structural predicate in terminal OpenQASM

The [unchanged first source](first/main.qli) and its [edition manifest](first/Qargo.toml)
form a project that prepares a superposition, computes the identity
predicate into scratch, applies an exact phase, uncomputes scratch and then
checks a clean workspace before measuring. The phase is observed through the
last Hadamard. The first terminal export reaches the computed Raw operation
and reports it as unsupported. The original JSON response is in
[terminal-before.stdout](terminal-before.stdout).

The observation used the beta candidate at
`5c12f8d73c48696e3b2ce9f7c85579585dac299f` with the matching predicate-profile
checker and `qleisli interop emit-qasm <project> --input=qli --resources`.
The authoring history precedes the terminal adapter. It records a diagnostic
on this small source and carries no resource or preservation claim.

[The ordered-register source](ordered-register.qli) makes the predicate's
coordinate explicit using `Bits<1>`. It exercises the structural circuit path.
