# #158 live signal ownership: first observations

Three original programs and six CLI observations: returning the signal and explicit discard succeed; losing the live signal refuses ownership. A block condition does not establish clean return, postselection or a resource certificate.

`first/` retains the entire original packet verbatim, including its unexecuted
status. `attempt-01/` contains identical source and manifest copies. Separate
observation records retain every original external metadata/stream byte; the
root session pins their complete original and retained inventories.

`collector.py.txt` is inert provenance, never imported or executed by checks.
The recorded executable hashes identify observed binaries; they are not source
build attestations. The shared reader only reads bounded files and does not run
historical commands. No original first failure or source is rewritten.
