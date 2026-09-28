// Independently authored input; output bits follow declaration order.
OPENQASM 3.0;
include "stdgates.inc";
qubit[2] q;
bit right;
bit left;
reset q;
h q[0];
cx q[0], q[1];
left = measure q[0];
measure q[1] -> right;
