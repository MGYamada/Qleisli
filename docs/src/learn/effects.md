# Choosing an effect

You have written `observe fn main` and `unitary fn entangle`. The word before
`fn` is the function's **effect**. It is a promise to every caller about
what the body can do to qubits. What happens when the body does more than
the word allows? Break two promises in the Bell project and find out.

## Prepare inside a unitary function

Every caller of `entangle` has to supply two qubits. Add a function to
`bell-lab/pair.qli`, below `entangle`, that supplies them itself.

```qli
pub unitary fn fresh_pair() -> (Q<Bit>, Q<Bit>) {
    entangle(init0(), init0())
}
```

Replace `bell-lab/main.qli` with a program that calls it.

```qli
use pair::fresh_pair;

observe fn main() -> (Bit, Bit) {
    let (left, right) = fresh_pair();
    (measure_z(left), measure_z(right))
}
```

Run `qleisli check bell-lab`. The checker points to `fresh_pair` in
`pair.qli`. Its diagnostic begins with this sentence.

```text
effect: body effect `Isometry` exceeds asserted `Unitary` effect of `fresh_pair`.
```

A **unitary** function transforms the qubits it receives and returns the
same number of qubits. `entangle` fits: two owners go in and two come out.
`fresh_pair` receives no qubits and returns two. A function that also
prepares qubits is an **isometry**. The checker worked that out from the
calls to `init0` and compared it with the word you wrote.

In `pair.qli`, change `pub unitary fn fresh_pair` to
`pub isometry fn fresh_pair`. Check and run the project. The checker accepts
it, and the simulator reports `00` and `11` with probability one half each.

## Measure inside an isometry

Move the measurements out of `main` in the same way. Add a third function
to `pair.qli`.

```qli
pub isometry fn read_pair() -> (Bit, Bit) {
    let (left, right) = fresh_pair();
    (measure_z(left), measure_z(right))
}
```

Replace `main.qli` with a program that only calls it.

```qli
use pair::read_pair;

observe fn main() -> (Bit, Bit) {
    read_pair()
}
```

Predict the diagnostic before you run `qleisli check bell-lab`.

```text
effect: body effect `Observe` exceeds asserted `Isometry` effect of `read_pair`.
```

Measurement turns a qubit into an ordinary bit, and no gate can take that
step back. A function that measures has the effect **observe**. Change
`pub isometry fn read_pair` to `pub observe fn read_pair`, then check and
run. You get the Bell distribution again.

## Read the four words

The three quantum effects are ordered from the least to the most a body can
do. Each word allows everything the words above it allow.

| Word | The body can | In this book |
| --- | --- | --- |
| `unitary` | Apply gates to the owners it receives | `entangle` |
| `isometry` | Also prepare qubits | `fresh_pair` |
| `observe` | Also measure and discard | `read_pair`, `main` |

A function can call functions at its own level or below. `read_pair` can
call `fresh_pair`, and `fresh_pair` can call `entangle`. The other direction
fails. In `main.qli`, change `observe fn main` to `unitary fn main` and
check the project.

```text
effect: body effect `Observe` exceeds asserted `Unitary` effect of `main`.
```

The body of `main` contains no measurement of its own. The effect comes
from its call to `read_pair`. An effect covers the whole body, including
every function it calls. Change `main` back to `observe fn`.

Write the lowest word that the body fits. A caller that sees `unitary`
knows the function neither prepares nor measures anything.

The fourth word, `classical`, marks a function on ordinary values. It
receives no owners and returns none. Add one above `main` in `main.qli`.

```qli
classical fn agree(a: Bit, b: Bit) -> Bit { not (a xor b) }
```

Change the result type of `main` to `Bit` and its body to these two lines.

```qli
    let (left, right) = read_pair();
    agree(left, right)
```

What will `qleisli run bell-lab` print? The two bits of a Bell pair always
match, so `agree` returns one every time.

```text
1: 1.000000000000e0
```

In [Searching four inputs](search.md) a classical function does a second
job. It describes a condition that a quantum operation then applies to all
candidates at once.

Next, [teleport a qubit](teleportation.md) with the `entangle` function you
kept in `pair.qli`. For the rules, see
[Effects](../reference/functional-boundary.md#effects) and
[effect assertions on declarations](../reference/source-text.md#effect-assertions-on-declarations).
