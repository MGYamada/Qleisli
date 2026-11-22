# Searching four inputs

Imagine a two-bit combination lock. You can write a function that recognizes
the right pair of bits. How can a quantum program use that function to find
the pair? We'll build a small Grover search. You'll be able to run it at
three points and see exactly when the marked input becomes more likely.

## Prepare the four candidates

From the [practice directory](first-qubit.md#prepare-and-measure), create
a project with the same edition manifest you used in `bit-lab`.

```sh
mkdir -p search-lab
cp bit-lab/Qlirgo.toml search-lab/Qlirgo.toml
```

Write the following program in `search-lab/main.qli`.

```qli
use std::measurement::measure_z2;
use std::transform::hadamard2;

observe fn main() -> (Bit, Bit) {
    let prepared = hadamard2(join(init0(), init0()));
    measure_z2(prepared)
}
```

You've already prepared two qubits in the Bell project. Here, `join`
groups their owners into a single owner of type `Q<(Bit, Bit)>`.
`hadamard2` applies a Hadamard to each qubit. With these two zero inputs,
that gives each candidate an equal chance. `measure_z2` measures both
and returns their bits in order.

```sh
qleisli check search-lab
qleisli run search-lab
```

The checker accepts the program. The simulator prints four lines.

```text
00: 2.500000000000e-1
01: 2.500000000000e-1
10: 2.500000000000e-1
11: 2.500000000000e-1
```

## Mark one candidate

The rule for our lock fits in one line. A pair matches when both bits are
one. Save this module as `search-lab/oracle.qli`.

```qli
use std::gate::z;

classical fn marked((a, b): (Bit, Bit)) -> Bit { a and b }

pub unitary fn mark(q: Q<(Bit, Bit)>) -> Q<(Bit, Bit)> {
    with_computed(q, marked) { |ancilla| z(ancilla) }
}
```

Start with `marked`. It takes an ordinary pair apart, gives its bits the
names `a` and `b`, and returns one only for `11`. The public function
`mark` uses this rule on the quantum input. `with_computed` computes the
predicate into a temporary qubit called `ancilla`. The `z` gate changes
the sign of the component where that qubit is one. The computation is then
undone to return the temporary qubit to zero.

In `main.qli`, add `use oracle::mark;` to the imports and change the final
expression to `measure_z2(mark(prepared))`. Predict what will happen to
the line for `11`. Check and run the project again.

All four lines have the same probabilities as before. Each candidate
started with an amplitude of +½. Marking takes the amplitude of `11` to
−½. Measurement gives the squared magnitude of each amplitude, and
both +½ and −½ give ¼. How can the program make use of that sign?

## Turn the sign into a measurable difference

Replace `search-lab/main.qli` with this version. It adds a reflection
between marking and measurement.

```qli
use oracle::mark;
use std::measurement::measure_z2;
use std::reflection::reflect_uniform2;
use std::transform::hadamard2;

observe fn main() -> (Bit, Bit) {
    let prepared = hadamard2(join(init0(), init0()));
    let marked = mark(prepared);
    let amplified = reflect_uniform2(marked);
    measure_z2(amplified)
}
```

Run `qleisli check search-lab` and `qleisli run search-lab` again. This
time the simulator prints one line.

```text
11: 1.000000000000e0
```

To see where the other three candidates went, follow their amplitudes.
After marking, the four signed amplitudes have mean ¼. The reflection
takes each amplitude to twice that mean minus its old value.

| Candidate | After marking | After reflection | Probability |
| --- | --- | --- | --- |
| `11` | −½ | 2 × ¼ − (−½) = 1 | 1 |
| Each of `00`, `01`, `10` | +½ | 2 × ¼ − ½ = 0 | 0 |

## Choose a different answer

Try changing the combination to `10` by editing just the predicate in
`oracle.qli`. The first printed bit is `a`, and `not` flips a classical
bit. Write down your expression before you check and run it.

One solution is `a and not b`. It returns one when the first bit is one
and the second is zero. With the same reflection, the simulator reports
`10` with probability one. As a final exercise, choose a predicate for
`01` and check which output your program produces.

You have built one Grover iteration for a search with one marked input
among four. You can see how the bundled example packages that iteration
as a reusable function in `$QLEISLI_REPO/examples/grover/search.qli`.
The [standard library reference](../reference/stdlib.md) describes the
operations used here. The [v1 algorithm goals](../imaginary-v1/index.md#marked-search)
describe the larger search problem.

Next, [state what an operation means](contracts.md) and let the checker
compare an implementation with it.
