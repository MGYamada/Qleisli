# Context preserved before the first check

This is an informed Unit-pattern implementation study under adopted Issues
#27/#43 and the common frontend plan in #32. Codex had read the current common
parser, shared Type<N>, finite profile/basis/runtime binders and sized generic/
concrete binders, and coordinated an independent review. It is not blind model
benchmarking. No external model was invoked; exact deployment/sampling settings
are unavailable. English source is authoritative.

The task is exact ordinary Unit patterns, including nested let and existing
basis patterns. Named ordinary Unit parameters are already grammar; general
ordinary parameter destructuring remains a separate desired unsupported case.
No parser change is authorized for that case in this implementation unit.
A runtime `let () = q` must not erase Q<Unit>. Coherent `do () <- q; pure ()`
instead binds the ordinary Unit basis inside the existing checked lift and must
return a Q<Unit> owner with scalar phase preserved.

Every source below and its hash was saved before any command. Main cases form
one multi-project first attempt; independent controls, negatives and the wider
unsupported grammar remain outside the repair sequence. There are no repaired
sources or invented failures. Only the existing canonical-cutover CLI and
native kernel will be run, with small programs and no build or large copy.
The reused binary's original build snapshot is recorded separately from the
current repository head/source hashes. This is not a fresh build of that head.

Required implementation validation later must check exact runtime/basis shape,
all ordinary/quantum mismatches and owner scope, emitted Discard/work/effect,
unary predicate arity and cleanup, and exact scalar phase with independent
reference/control-sensitive tests. Baseline check success alone does not prove
any of those semantic obligations or discharge a constitutional guarantee.
