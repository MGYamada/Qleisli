# Qleisli Python connections

Copyright 2026 Masahiko G. Yamada. Licensed under Apache-2.0.

This development host package calls the separately installed Qleisli 0.2.6 Rust
executable built from the same checkout. The latest published Rust release is
0.2.6; Python registry publication is separate.
It does not embed Rust or require an LLVM installation. Install a local wheel,
then select `Client(executable="/path/to/qleisli")`, set `QLEISLI_BIN`, or put
`qleisli` on PATH. Prebuilt all-in-one platform wheels are not provided yet.

```python
from qleisli import Client

client = Client(executable="target/debug/qleisli")
program = client.from_openqasm('''OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q; bit[2] c; reset q;
h q[0]; cx q[0], q[1]; c = measure q;
''')
print(program.run())
print(program.sample(shots=8, seed=0))
print(program.to_qir())
```

Use `compile_project(path)` for a `.qli` project and `from_ir(bytes)` for a
QIRF artifact. `from_qir(text_or_bitcode)` requires the optional `qir` extra
(PyQIR 0.12.5, MIT, with its LLVM dependency notices). It supports the declared
QIR 2.0 Base terminal subset, not arbitrary LLVM or adaptive programs. The
reader runs in a separate process and never executes imported code. All inputs
then pass the Rust verifier. `QleisliError.diagnostics` retains structured Rust
diagnostics. Result bit lists keep declared output order; probabilities are
numerical diagnostics and samples are local simulations, not device results.

`python -m qleisli INPUT --input=qasm|qir|qirf|qli --action=check|run|sample|emit-qasm|emit-qir|emit-ir`
provides a JSON command-line host. Sampling requires `--shots` and `--seed`.
Each operation rechecks the actual artifact. Mutating a Python object or its
serialized IR cannot create a trusted evidence handle.

For a checkout, install into a virtual environment (QIR support is optional):

```sh
cargo build --bin qleisli
python3 -m venv /tmp/qleisli-python
/tmp/qleisli-python/bin/pip install --only-binary=pyqir './python[qir]'
```

This builds only the pure Python host wheel; the separate Cargo step builds the
Rust executable. `--only-binary=pyqir` fails explicitly on platforms without a
reader wheel, instead of attempting a local LLVM build. Omit `[qir]` when only
OpenQASM/QIRF and QIR output are needed. PyQIR retains its own MIT license and
bundled LLVM/transitive notices; none of that binary code is included in this
host wheel.
