# Writing functions and modules

Suppose you want to use the circuit from the [Bell-pair project](bell-pair.md)
with different inputs. Which lines belong to the circuit, and which lines
choose what to prepare and measure? Let's give the circuit a name, then
move it into a file that other functions can use.

## Give the circuit a name

Replace the contents of `bell-lab/main.qli` with these two functions.

```qli
unitary fn entangle(control: Q<Bit>, target: Q<Bit>) -> (Q<Bit>, Q<Bit>) {
    cnot(h(control), target)
}

observe fn main() -> (Bit, Bit) {
    let (left, right) = entangle(init0(), init0());
    (measure_z(left), measure_z(right))
}
```

Read the call in `main` first. Each `init0()` supplies one argument.
Inside `entangle`, the parameters `control` and `target` name those two
owners. The type after each parameter name tells you what the caller must
pass. The type after `->` tells you what comes back. Here that's a pair
of owners. The `let` pattern gives each returned owner a name in `main`.

Why does the last line of `entangle` have no semicolon? The call to
`cnot` is the function's final expression. Its value becomes the result
of the function. The caller can pass those qubits on to another gate or,
as `main` does here, measure them. The `unitary` function applies gates
to its inputs. The measurements belong to the `observe` function.
[Choosing an effect](effects.md) explains those two words.

From the practice directory, check the project and run it.

```sh
qleisli check bell-lab
qleisli run bell-lab
```

You should see `00` and `11` with equal probability, just as in the
original Bell circuit. Use that distribution to check your next edit.

## Move the function into a module

Cut the whole `entangle` definition from `main.qli` and paste it into
`bell-lab/pair.qli`. The file name gives the module its name, `pair`.
At the top of `main.qli`, above `observe fn main`, add this import.

```qli
use pair::entangle;
```

Run `qleisli check bell-lab`. The checker points to the import on the
first line. Look at the last part of the diagnostic.

```text
project: `pair::entangle` is not public
```

The checker found the function. Moving it put the caller in a different
module, and functions are private to their module by default. In
`pair.qli`, change `unitary fn entangle` to `pub unitary fn entangle`.
`pub` makes the function available to other modules. The `use` in
`main.qli` lets the caller write its short name. Check and run again.
The checker accepts the import, and the circuit gives the same two outcomes.

## Try a different input

Leave `pair.qli` as it is. How could you make the measured bits *disagree*
on every shot? The `x` gate flips a basis bit. Try giving the second
parameter `x(init0())` and predict which pairs you will see.

Run `qleisli run bell-lab`. The two outcomes are `01` and `10`, each
with probability one half. The target starts at one. On the component
where the control is one, `cnot` flips the target back to zero.

Keep your `pair.qli` file. Next, [choose an effect](effects.md) for two
more functions in it. In [Teleporting a qubit](teleportation.md), you'll
use `entangle` to supply Alice and Bob with a shared Bell pair.
For the rules that apply to imports, see
[Prelude, imports and qualified names](../reference/prelude.md).
