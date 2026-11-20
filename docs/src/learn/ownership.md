# Following a quantum owner

Suppose you want to return the same random bit twice. Your caller should
get either `(0, 0)` or `(1, 1)`. You already know how to produce one bit.
What happens if you write the measurement expression twice?

This lesson uses four rejected programs. Each one shows a different part of
the rule that shapes every Qleisli program.

## Read the diagnostic

In the `bit-lab` project from [the first lesson](first-qubit.md), replace
`main.qli` with this deliberately invalid attempt.

```qli
observe fn main() -> (Bit, Bit) {
    let q = h(init0());
    (measure_z(q), measure_z(q))
}
```

Run `qleisli check bit-lab`. The checker points to the second use of `q`.

```text
ownership: quantum ownership `q` has already been consumed
```

`q` has type `Q<Bit>`. It is an **owner**, a value that gives this
program the use of a particular quantum system. The first call to
`measure_z` consumes that owner and returns an ordinary `Bit`. By the time
the checker reaches the second call, the function has already used `q`.

## Keep the measurement result

Try repairing the program before reading on. You can introduce one
`let` binding. Which expression should you evaluate once, and which
value can you use in both positions of the pair?

Here is one repair for `bit-lab/main.qli`.

```qli
observe fn main() -> (Bit, Bit) {
    let q = h(init0());
    let b = measure_z(q);
    (b, b)
}
```

Run `qleisli check bit-lab` and `qleisli run bit-lab`. The checker accepts
both uses of the ordinary bit. The outcomes are `00` and `11`, each with
probability one half. There was one measurement, and both positions in
the returned pair contain its result.

An ordinary value such as `b` can be read as often as you like. An owner can
be used once. The type tells you which of the two a name holds.

## Pass an owner through a gate

Measurement is not the only operation that consumes an owner. Replace
`main.qli` with this program and predict which line the checker rejects.

```qli
observe fn main() -> Bit {
    let q = init0();
    let r = h(q);
    measure_z(q)
}
```

Run `qleisli check bit-lab`. The diagnostic is the one you saw before, and
it points to `q` in the last line.

```text
ownership: quantum ownership `q` has already been consumed
```

A gate is a function from owners to owners. The call `h(q)` consumes `q` and
returns the owner of the transformed qubit, which this program names `r`.
After that line the qubit is reachable through `r` alone.

Change the last line to `measure_z(r)` and check again. The checker accepts
the program. You can also keep one name for the qubit all the way through.
Change the middle line to `let q = h(q);` and the last line back to
`measure_z(q)`. The second `let` binds the name `q` to the owner that `h`
returned. You will see this shape wherever a gate acts on a named qubit.

## Give up an owner you do not need

What if a function prepares a qubit and never uses it? Replace `main.qli`
with a program that has one qubit too many.

```qli
observe fn main() -> Bit {
    let q = h(init0());
    let spare = h(init0());
    measure_z(q)
}
```

Run `qleisli check bit-lab`. The checker points to `spare`. Its diagnostic
begins with this sentence.

```text
ownership: local quantum ownership `spare` escapes neither through the result nor an explicit discard.
```

Every owner must leave the function in a way you wrote down. The function
can return it, pass it to an operation, or measure it. Reaching the closing
brace is not one of those ways. The rest of the diagnostic compares this
rule with Rust, where an unused value may simply go out of scope.

Qleisli asks for more because losing a qubit is a physical event. If the
qubit is entangled with others, dropping it changes what their measurements
show. The language makes you say so. Add this line after the binding of `spare`.

```qli
    discard(spare);
```

Check and run the project. The checker accepts the program, and the outcomes
`0` and `1` each have probability one half. `discard` consumes the owner and
returns nothing.

## Keep both branches even

An `if` chooses between two blocks at run time. What should the checker do
when one block uses an owner and the other does not? Replace `main.qli` with
this program.

```qli
observe fn main() -> Bit {
    let coin = measure_z(h(init0()));
    let q = h(init0());
    if coin { measure_z(q) } else { 0 }
}
```

Run `qleisli check bit-lab`. The checker points to the `if`.

```text
ownership: branches must consume the same owners and preserve outer binding types
```

When `coin` is one, the first block measures `q`. When it is zero, the
second block leaves `q` unused. After the `if`, the checker could not say
whether `q` has an owner. So both blocks must consume the same owners.

Try the repair yourself. The second block has to give up `q` and produce
the bit zero. Then predict the distribution before you run the program.

One repair changes the last line of `main` to this.

```qli
    if coin { measure_z(q) } else { discard(q); 0 }
```

The simulator reports `0` with probability three quarters and `1` with
probability one quarter. Half of the runs take the second block and return
zero. The other half measure `q`, which gives zero half of the time.

## What you have seen

An owner leaves a function in one of four ways.

| The program | What happens to the owner |
| --- | --- |
| Passes it to a gate or another function | The call consumes it. The result may contain an owner to use next. |
| Measures it | `measure_z` consumes it and returns an ordinary bit. |
| Discards it | `discard` consumes it and returns nothing. |
| Returns it | The caller receives it and takes on the same obligation. |

Can two *different* qubits give the same distribution as one bit used
twice? In the [Bell-pair project](bell-pair.md) you will measure two
distinct owners. For the formal rules behind these diagnostics, see
[Quantum owners](../reference/type-model.md#quantum-owners).
