# Informed operation application study

The author read the current parser, common original-source checker, selected
projection and Issues #33/#32/#250 before writing this complete desired source.
The current implementation has adjoint(U,q), repeat_static(n,U,q), static
constructors with _op suffixes and two-stage controlled(U)(c,q). Those are
observations, not permission to retain competing spellings in the final release.
No external model or blind benchmark was run; model/sampling metadata is unavailable.
The first source is preserved before any operation-application implementation.

The desired example uses two source qubits, opaque Basis and bounded Nat
specialization, a phase oracle, inverse, power and coherent control. It is a
Grover-style operator-pattern study, not an implementation of Grover or QFT.
It introduces no runtime callable, new native primitive or guarantee.
Actual parser failure cannot establish its downstream capability/owner rules.
Expected computational-basis probabilities are all four pairs at 1/4, but
that observation alone would miss its relative phases. A later action comparison
must independently check controlled-Z followed by target Z on arbitrary inputs.
At k=1, |++> amplitudes in ordered (control,target) labels are [1,1,-1,1]/2.
Existing ordinary functions named inverse/power/controlled must have an explicit
migration or contextual-name rule rather than silent reinterpretation.

The first actual observation rejected the observer's missing schema-version=2
manifest, before parsing the desired source. Attempt 02 corrects that manifest
and leaves the complete source byte-identical; the first observation remains.
Coordinate clarification before execution: the earlier amplitude list uses
control as the low bit, ordered labels 00,10,01,11. In lexicographic
(control,target) order 00,01,10,11 the independent values are [1,-1,1,1]/2.
Use the explicit label mapping in expectations.json to avoid an axis assumption.

Attempt 03 is a separate legacy-spelling translation, observed before any
canonical power or Z-adapter implementation. Its actual refusal exposes the
selected preparation's unsupported `std::quantum::z` adapter. The initial
observation was made under `attempt-03-legacy-probe`; the identical source and
manifest are stored under consecutive `attempt-03` to satisfy the session
format. The command and diagnostic paths in the observation remain unchanged.
On 2026-10-07 the maintainer prioritized local CI repairs; this study remains
unimplemented and earns no feature or guarantee completion credit.
