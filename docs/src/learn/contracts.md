# Stating what an operation means

In the [search project](search.md) you used `reflect_uniform2` without
reading its body. You trusted its name. Can a function ask for more than a
name? In this lesson a caller states the operation it needs. The checker
then compares each implementation you supply with that statement.

## Declare a meaning

From the [practice directory](first-qubit.md#prepare-and-measure), create a
project with the same edition manifest.

```sh
mkdir -p meaning-lab
cp bit-lab/Qargo.toml meaning-lab/Qargo.toml
```

Save this program as `meaning-lab/main.qli`.

```qli
classical fn flipped(b: Bit) -> Bit { not b }
meaning Flip: Bit = permutation_by(flipped);

unitary fn direct(q: Q<Bit>) -> Q<Bit> { x(q) }

unitary fn client[const U: Op<Bit, Flip>](q: Q<Bit>) -> Q<Bit>
requires Applicable(U) { U(q) }

observe fn main() -> Bit {
    let a = client[checked_op(direct, Flip)](init0());
    measure_z(a)
}
```

Read it from the top. `flipped` is an ordinary function on one bit. The
`meaning` line turns it into a specification named `Flip`: the operation on
one qubit that sends each basis state to the state `flipped` names. A
**meaning** says what an operation does. It contains no gates.

`direct` is an implementation. It uses the `x` gate.

`client` has a parameter in square brackets. `U` is an operation on `Q<Bit>`
whose meaning is `Flip`. The caller chooses it when the program is checked,
before any qubit exists. The `requires` line says what `client` does with
`U`: it applies it.

In `main`, `checked_op(direct, Flip)` offers `direct` as that operation. The
checker compares the gates in `direct` with `Flip` before it accepts the call.

```sh
qleisli check meaning-lab
qleisli run meaning-lab
```

The checker accepts the program. The simulator reports `1` with probability
one, because `client` flipped a qubit that started at zero.

## Supply a second implementation

A Hadamard on each side of `z` also flips a basis bit. Add this function
below `direct`.

```qli
unitary fn sandwich(q: Q<Bit>) -> Q<Bit> { h(z(h(q))) }
```

Change `main` to call `client` twice, once with each implementation.

```qli
observe fn main() -> (Bit, Bit) {
    let a = client[checked_op(direct, Flip)](init0());
    let b = client[checked_op(sandwich, Flip)](init0());
    (measure_z(a), measure_z(b))
}
```

Check and run the project. The checker accepts both calls, and the
simulator reports `11` with probability one. `client` did not change. It
names the meaning it needs, and any implementation the checker has compared
with that meaning can take the place of `U`.

## Try an implementation that is almost right

Change the body of `sandwich` to `z(x(q))`. On a qubit that starts at zero,
`x` gives one, and `z` leaves the probability of measuring one unchanged.
Would `main` print the same line? Predict what the checker says, then run
`qleisli check meaning-lab`.

```text
contract: exact equation U E_in = E_out u does not hold
```

The diagnostic points to the second `checked_op`. The simulator never ran.
The measured bits would have been the same, and the checker rejected the
program anyway.

`z` reverses the sign of the amplitude for one. So `z(x(q))` sends zero to
one with a minus sign and sends one to zero with a plus sign. `Flip` gives
both a plus sign. You saw in [the teleportation project](teleportation.md)
that a relative sign changes what a later measurement shows. A meaning is
exact. Equal probabilities on one input do not satisfy it.

Restore `h(z(h(q)))` and check that the project passes.

## Ask for what you use

The line `requires Applicable(U)` names a **capability**, a use of `U` that
the caller must make available. `Applicable` lets `client` apply `U`.
Running `U` backwards and running `U` under the control of another qubit
are separate capabilities with their own names. A meaning does not grant
them. A function lists each capability it uses, and the checker asks every
caller to supply it.

You have stated a meaning, supplied two implementations and seen the
checker reject a third. The
[bundled contract example](https://github.com/MGYamada/Qleisli/tree/main/examples/operation_contracts)
does the same for an operation defined by a phase.
[Checked operations](../reference/checked-operations.md) gives the rules for
`checked_op` and `meaning`, and
[Operation access](../reference/functional-boundary.md#operation-access)
describes the capabilities.

Next, [tour the tools](tools.md) with the projects you have built.
