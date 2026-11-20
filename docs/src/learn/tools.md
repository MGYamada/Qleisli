# Working with the tools

You have typed `qleisli check` and `qleisli run` in every lesson and read
only the last lines of their output. This lesson goes through the commands
one at a time on a single small program. At the end you will know what each
command reports, and which questions the report leaves for the next part of
the book.

## A program to work on

Replace `bit-lab/main.qli` with a coin flip. The lines that begin with `//!`
and `///` are documentation comments.

```qli
//! A coin that the caller reads once.

/// Prepares an equal superposition and measures it.
observe fn main() -> Bit {
    let q = h(init0());
    measure_z(q)
}
```

## Read the check report

Run `qleisli check bit-lab` and read every line this time.

```text
checked source: bit-lab
native checks: IR structure, ownership, interface, classical scope and decoded execution view; 1 concrete local roots, 24 bundled roots
checker: /path/to/qleisli-kernel
checker identity: unpinned
native decisions: 76; native requests checked: 2
entry request checked: false
source preservation: not proved
```

The counts depend on your program and on the bundled standard library.

| Line | What it tells you |
| --- | --- |
| `checked source` | The project directory that the command read. |
| `native checks` | The checks that the native verifier ran, and the number of functions it checked. One is yours. The others belong to the standard library. |
| `checker` | The path of the native verifier, the separate executable that made the decisions. It is the one you named in `QLEISLI_KERNEL`. |
| `checker identity` | `unpinned` means the tool ran that file without comparing it to a known build. |
| `native decisions` | The number of times the verifier accepted something during this check. Repeated decisions count each time. |
| `entry request checked` | `false` means the verifier checked `main` without a separate request. A request asks the verifier to check one more stated property of an artifact. Without one, the decision covers the checks on the `native checks` line. |
| `source preservation` | `not proved` means the checks cover the program that the compiler handed to the verifier. They do not prove that it matches your source. |

The report is careful about what it claims. Two of its lines say what the
check did not establish. The
[production boundary](../reference/production-boundary.md#cli-success-reports)
defines every field.

Notice the word `checker` in the report. The lessons have said "the checker"
for whatever accepted or rejected your program. Two programs share that
work. The `qleisli` command checks your source and prints the diagnostics
you have repaired. The native verifier decides acceptance, and the report's
`checker` line names it.

## Run and sample

`qleisli run bit-lab` prints the distribution of the result.

```text
0: 5.000000000000e-1
1: 5.000000000000e-1
```

`run` computes these probabilities from a simulation of the whole program.
`sample` draws individual results instead. It needs the number of shots and
a seed, and the same seed gives the same shots.

```sh
qleisli sample bit-lab --shots=8 --seed=0
```

```text
1
0
0
1
0
0
0
1
```

## Give the result to another program

`check`, `run` and `sample` accept `--format=json`. A script can then read
the result without parsing text.

```sh
qleisli run bit-lab --format=json
```

```json
{"format":"qleisli.result","version":1,"command":"run","outcome":"ok","diagnostics":[],"result":{"distribution":[{"bits":[false],"probability":0.5000000000000001},{"bits":[true],"probability":0.5000000000000001}]}}
```

A rejected program gives the same envelope with its diagnostics in the
`diagnostics` list. Put the ownership mistake from
[the second lesson](ownership.md) back and run `qleisli check bit-lab
--format=json` to see one. Restore the coin flip afterwards.

## Render the documentation

`qleisli doc` takes one source file and prints its documentation comments
as Markdown, with the signature of each function.

```sh
qleisli doc bit-lab/main.qli
```

The output begins with the module comment and continues with one section
for each function. Below its title it prints this line.

```text
Source documentation only; no type, ownership or contract verification is implied.
```

`doc` reads comments and signatures. It does not check the program, so it
needs no verifier.

## Keep the checked program

The compiler translates your source into an **intermediate representation**
(IR), a lower-level form of the program that the verifier checks. `emit-ir`
writes that form to a file.

```sh
qleisli emit-ir bit-lab --output=coin.qirf
```

```text
emitted checked IR: coin.qirf
native checks: IR structure, ownership, interface, classical scope and decoded execution view
checker: /path/to/qleisli-kernel
checker identity: unpinned
artifact root request checked: false
source preservation: not proved
```

Open `coin.qirf` in an editor. It is a short JSON file that lists the
preparation, the Hadamard and the measurement. `verify-ir` checks such a
file on its own, without the source. A file has no manifest, so you name the
edition on the command line.

```sh
qleisli verify-ir coin.qirf --edition=2026
```

The verifier accepts the file and prints the same checks. Try changing the
gate name `"h"` in the file to `"hh"` and run `verify-ir` again.

```text
invalid_ir: Lean native checker rejected the artifact/request; no fallback
```

The verifier decides from the bytes in front of it. It does not matter who
wrote them.

## Export a circuit

The `interop` commands exchange programs with other formats. They are
experimental test features and are not suitable for real quantum hardware.

```sh
qleisli interop emit-qasm bit-lab --input=qli
```

The command prints a JSON result. Its `text` field holds an OpenQASM 3
program with a reset, an `h` gate and a measurement. `qleisli --help` lists
every command and option.

## What did the check establish?

You have seen the same few lines after every command.

- A separate executable makes the decisions.
- It checks a form of the program that is not your source.
- The report says which statements about `main` the verifier compared, and
  which it did not.
- Nothing proves that the checked form matches what you wrote.

Why is the system built this way? The next part of the book answers by
following a project through it. Start with
[System architecture](../architecture/system.md).
