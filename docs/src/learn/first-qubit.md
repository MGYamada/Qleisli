# Measuring your first qubit

A qubit is a quantum system with two basis states, called zero and one.
What bit do you expect to see when you prepare the zero state and measure
in that basis? Write a program to find out, then change its preparation.

## Set up the tools

Open a shell at the root of the [Qleisli repository](https://github.com/MGYamada/Qleisli).
Keep this shell open for the lessons. Save the checkout path so you can
find the tools and compare your programs with the bundled examples.

```sh
export QLEISLI_REPO="$PWD"
```

If you have a matching `qleisli` command and native verifier configured, go
straight to the project below. To build them from this checkout you need
Rust 1.85 or later and Lean 4.30.0 with Lake and its native build tools.
Run both build commands from the repository root.

```sh
cargo build --locked --bin qleisli
(cd lean-kernel && lake build && lake env lean -DwarningAsError=true Audit.lean)
export PATH="$QLEISLI_REPO/target/debug:$PATH"
export QLEISLI_KERNEL="$QLEISLI_REPO/lean-kernel/.lake/build/bin/qleisli-kernel"
```

The first command builds the CLI. The second builds and audits the native
verifier, a separate program that decides whether each of your programs is
accepted. `QLEISLI_KERNEL` tells the CLI which executable to use for checking.

## Prepare and measure

Create a practice directory. In the following lessons, run the commands
from `qleisli-lessons`, the parent of your projects.

```sh
mkdir -p "$HOME/qleisli-lessons/bit-lab"
cd "$HOME/qleisli-lessons"
```

Save this manifest as `bit-lab/Qlirgo.toml`. It tells Qleisli which edition
to use when reading this directory.

```toml
schema-version = 2

[qrate]
edition = "2026"
```

In `bit-lab/main.qli`, write a function that prepares a qubit and measures it.

```qli
observe fn main() -> Bit {
    let q = init0();
    measure_z(q)
}
```

Read the first line as a promise to the caller. The function is named
`main`, the empty parentheses mean it takes no arguments, and `-> Bit`
says it returns one ordinary bit. The word `observe` allows this
function to measure a qubit. [Choosing an effect](effects.md) covers the
other words that can stand there.

Execution starts inside the braces. `init0()` prepares a qubit in the
zero state. The `let` binding names its owner `q`. The final expression,
`measure_z(q)`, measures in the computational basis and returns the
measured bit. Let's see what that looks like in the terminal.

```sh
qleisli check bit-lab
qleisli run bit-lab
```

The checker accepts the project. The simulator prints one line.

```text
0: 1.000000000000e0
```

Read the bit on the left and its probability on the right. Here the only
outcome is `0`, and its probability is one.

## Change the preparation

Replace `let q = init0();` with `let q = h(init0());`. The Hadamard gate
`h` takes the zero state to an equal superposition of zero and one. Run
`qleisli run bit-lab` again. The distribution gives each outcome probability
one half. Use `sample` to see eight individual measurements, called shots.

```sh
qleisli sample bit-lab --shots=8 --seed=0
```

Each shot starts with a fresh preparation. Eight shots can give unequal
counts even when the probabilities are equal. Try `h(h(init0()))` and
predict what `run` will show. Applying Hadamard twice returns the qubit
to its starting state, so zero has probability one again.

Next, [follow the owner through a measurement](ownership.md).
