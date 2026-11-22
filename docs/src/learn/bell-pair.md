# Building a Bell pair

In the previous lesson both output bits came from a single measurement.
Here you will measure two qubits, one time each. First predict whether
their results can disagree.

## Entangle two qubits

From the [practice directory](first-qubit.md#prepare-and-measure), make
another project using the same edition.

```sh
mkdir -p bell-lab
cp bit-lab/Qlirgo.toml bell-lab/Qlirgo.toml
```

Save the following function as `bell-lab/main.qli`.

```qli
observe fn main() -> (Bit, Bit) {
    let (left, right) = cnot(h(init0()), init0());
    (measure_z(left), measure_z(right))
}
```

Read the arguments to `cnot` from left to right. The first qubit is in an
equal superposition and the second starts at zero. A controlled-NOT
flips the second qubit on the component where the first is one. It takes
the two input owners and returns two output owners, which the pattern
binds to `left` and `right`.

```sh
qleisli check bell-lab
qleisli run bell-lab
```

The checker accepts the program. The simulator assigns probability one half
to `00` and one half to `11`. Before measurement the two qubits form an
entangled Bell pair. The two names tell you which qubit each operation uses.
The joint state determines how their measurements are correlated.

## Try two independent preparations

Replace the first line inside `main` with
`let (left, right) = (h(init0()), h(init0()));`. Keep the two measurement
calls and run the project again. Each individual bit has equal chances
of being zero or one. This time all four pairs, including `01` and
`10`, have probability one quarter. Look at pairs when you want to
distinguish independence from perfect correlation.

Next, [give the Bell circuit its own function and module](functions-and-modules.md)
so you can try different inputs.
