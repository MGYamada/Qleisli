# Imported enum in an ordinary helper body

This first #64 project uses a transparent reexport to construct a three-label
enum inside a classical helper. Neither the helper nor the closed project
main returns a nominal type. The expected result is one Bit with value 1
because the exact C label selects its written arm, regardless of arm order.

The timestamp comes from the captured stdout file. The baseline worktree
was 870b510b7ce2cf0cb7531effc1ce64844197d073. The baseline observer SHA-256
was a86863d42184633166b71fee14d5f7df05975f1f080ac041075201c1af40b74f
and the native checker SHA-256 was
abbce360dbb4dcf9425872c93e16456b576623f46bd9daeef25b7bdf841658ae.
