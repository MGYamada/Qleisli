# Teleporting a qubit

Alice has a qubit. Bob has half of a [Bell pair](bell-pair.md), and Alice
has the other half. How can Bob recover the state of Alice's input if all
she sends him is two ordinary bits? You'll write a function that teleports
its input, then try two inputs to find out why Bob needs both bits.

## Use the shared Bell pair

From the [practice directory](first-qubit.md#prepare-and-measure), copy the
manifest and the `pair` module from the
[functions and modules project](functions-and-modules.md#move-the-function-into-a-module).
This lesson uses its public `entangle` function.

```sh
mkdir -p teleport-lab
cp bell-lab/Qargo.toml bell-lab/pair.qli teleport-lab/
```

Save the protocol in `teleport-lab/transfer.qli`. Its argument is a qubit
chosen by the caller. Its result keeps Alice's message alongside Bob's
corrected qubit so you can inspect each outcome.

```qli
use pair::entangle;

pub observe fn teleport(input: Q<Bit>) -> ((Bit, Bit), Q<Bit>) {
    let (alice, bob) = entangle(init0(), init0());
    let (input, alice) = cnot(input, alice);
    let phase_bit = measure_z(h(input));
    let parity_bit = measure_z(alice);

    let bob = if parity_bit { x(bob) } else { bob };
    let bob = if phase_bit { z(bob) } else { bob };
    ((phase_bit, parity_bit), bob)
}
```

Follow the three owners, as you did in [Following a quantum owner](ownership.md).
The caller supplies `input`. The first line of
the function supplies `alice` and `bob`, one for each half of the Bell
pair. Alice applies a CNOT to her two qubits and a Hadamard to the first,
then measures both. Together those operations make a Bell-basis
measurement. The measurements consume both of Alice's owners.

Alice sends the two results to Bob. Read his two `if` expressions in
order. A parity bit of one tells him to flip his qubit with `x`. A phase
bit of one tells him to apply `z`, which reverses the sign of the
amplitude for `1`. Each branch returns the owner that Bob uses next.

## Read all four messages

In `teleport-lab/main.qli`, start with an input whose measurement you can
predict. The `x` gate prepares one from zero. What should the last output
bit be if Bob has recovered that state?

```qli
use transfer::teleport;

observe fn main() -> ((Bit, Bit), Bit) {
    let input = x(init0());
    let (message, bob) = teleport(input);
    (message, measure_z(bob))
}
```

```sh
qleisli check teleport-lab
qleisli run teleport-lab
```

The checker accepts the project. The simulator gives these four outcomes.

```text
001: 2.500000000000e-1
011: 2.500000000000e-1
101: 2.500000000000e-1
111: 2.500000000000e-1
```

Take `101` as an example. Alice obtained phase bit `1` and parity bit
`0`, so Bob applied only `z`. His readout is the final `1`. All four
messages are equally likely, and Bob reads one for every message.

## Find a missing correction

Try removing just the `let bob = if phase_bit { z(bob) } else { bob };`
line from `transfer.qli`. Check and run the project again. The checker
accepts the edit and you get the same four lines. On the state one, a
sign change leaves the probability of measuring one unchanged. What
input would let you see that the phase correction is missing?

Keep that line out for one more run. In `main.qli`, change the preparation
to `let input = h(x(init0()));` and the readout to
`(message, measure_z(h(bob)))`. The preparation makes the *minus state*,
a superposition in which the zero and one components have opposite signs.
The Hadamard before readout measures Bob's qubit in the X basis. If he
recovers the minus state, that Hadamard takes it back to one.

Run the project and look first at the messages whose phase bit is one.

```text
001: 2.500000000000e-1
011: 2.500000000000e-1
100: 2.500000000000e-1
110: 2.500000000000e-1
```

For messages `10` and `11`, Bob reads zero. On those branches the two
components have the same sign, and the final Hadamard takes that state
to zero. Restore the phase correction and run again. Bob reads one for
all four messages. You used the same protocol on two inputs and chose a
measurement that makes a relative sign observable.

For one last experiment, return to the first `main`, which prepares one.
Keep the phase correction and remove the parity correction. Which messages
should give Bob zero? Run the project and check the middle bit of the
two outcomes that end in zero. Restore the parity correction when you're done.

The [bundled protocol example](https://github.com/MGYamada/Qleisli/tree/main/examples/protocols)
puts Alice's measurement and Bob's corrections in reusable functions.
Bennett and colleagues derive the protocol for an unknown input in
[the original teleportation paper](https://doi.org/10.1103/PhysRevLett.70.1895).

Next, [search four inputs](search.md) with an algorithm that uses a
relative sign to pick out a marked candidate.
