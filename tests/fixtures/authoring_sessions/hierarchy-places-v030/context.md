# Selected static index in the hierarchy

The first source contains `indexed`, which uses an `excl` index, and
`explicit`, which uses `take_bit` and `put_bit` on the same axis. The
original hierarchy refused `indexed`. Its Raw check and the hierarchy
check of `explicit` passed. The same `indexed` source later passed the
explicit hierarchy profile with the unchanged native checker.

The observation reports retain the actual invoked path and diagnostic.
The bounded source and graph replay tests check axis selection separately
from the producer's composition request.
