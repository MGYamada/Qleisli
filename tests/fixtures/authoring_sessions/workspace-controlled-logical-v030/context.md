# A controlled phase as a workspace logical action

A closed two-qubit case declares controlled S as its logical action and uses the
same original function inside a clean workspace. The first source is retained
alongside a second source that moves the final gates before the first terminal
observation. The native source-body check originally rejected both programs.
The independent staged read found the refusal while reconstructing the declared
logical action. The public target resource report had yet to run.

Rechecking the terminal derivative with the repaired kernel emits three T/TDG
instructions and six other gates on three reserved wires. The third source
keeps the declared controlled S and runs controlled S adjoint in its body.
The repaired checker rejects that phase mismatch at the clean restoration
equation.
