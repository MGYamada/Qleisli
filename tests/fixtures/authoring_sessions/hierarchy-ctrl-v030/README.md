# Ordered hierarchy control access

Both original sources apply CNOT from axis 1 to axis 0. The positive source
requires basis-sector preservation of axis 1. The negative source requires it
of axis 0, which flips in the axis-1 sector labeled 1. The same action and
ordered interface are required in both cases. Either source may have a joint
reference, so computational-basis probabilities alone are insufficient.

The [earliest observations](earliest-observations.json) preserve the initial
missing-schema-version manifest refusal and the later schema-2 results with unchanged
`.qli` files. The [registered observations](session.json) repeat those checks
with the compiler built from the hierarchy-place base. Raw accepts the first
source and reports a sector-contract error for the second. Hierarchy reports
that the required independent sector check is unavailable for both.

CLI and native checker SHA-256 at the registered baseline

```text
4346a74b76f5e7054b3dd28675d28f4c587491b9ad40ee1078a5f38986cd7815  target/debug/qleisli
2b9d205d07460f565a328247ad7250841d2cbaa47538a3b3fa2f1792cfbbcdb2  lean-kernel/.lake/build/bin/qleisli-kernel
```

The [current observations](current-observations.json) use the unchanged
sources. The hierarchy accepts and executes the first source and rejects the
second in the native composition/control invocation. The successful run
moves input basis 2 to basis 3. The exact Lean tests check coefficient and
sector behavior independently of the numerical CLI output.
