# Finite table predicates in terminal OpenQASM

The [first project](first/main.qli) uses the identity table over `Bit` and
observes its phase on a superposition. The original request for a resource
report failed on `cdee41eee8887d7ae896dbd2829baa73074088dd`.
[The captured JSON response](before.stdout) records the actual diagnostic.
The first source is unchanged.

The [typed project](typed/main.qli) uses a two-variant enum to take the compiler's
existing original-source checking route. It retains a finite table in Raw.
The target check compares the literal output with its original table-driven
operator on all carrier coordinates, including the second row even though
the program prepares the first enum variant.

The CLI command is `qleisli interop emit-qasm <project> --input=qli`.
With `--resources`, the same adapter requests the independent literal
placement check. That check requires the retained typed source request.
