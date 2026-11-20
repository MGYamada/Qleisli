# Following a quantum owner

Suppose you want to return the same random bit twice. Your caller should
get either `(0, 0)` or `(1, 1)`. You already know how to produce one bit.
What happens if you write the measurement expression twice?

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

Can two *different* qubits give the same distribution? In the
[Bell-pair project](bell-pair.md) you will measure two distinct owners.
For the formal rule behind the diagnostic, see
[Quantum owners](../reference/type-model.md#quantum-owners).
