# Typed layout checking: the next CD-3 component

Status (2026-09-29): **implemented with executable permutation/reindexing proofs**
in the Mathlib-free Lean kernel. This specifies the `typed-layout-v1` experiment. Its executed
checks and proof status are recorded separately in the [0.2.0 record](releases/v0.2.0.md).
It does not enable production hierarchical QPE or transfer Rust verification authority.

## Source, obligation and boundary

The [first source](../tests/fixtures/lean_layout/first_source/main.qli) moves
three quantum owners, including `Q<Unit>`, and returns them in a different
order. It already checks in Rust. The [baseline](../tests/fixtures/lean_layout/baseline.json)
records that the earlier Lean executable cannot check its proposed layout.
The initial phase DAG has only one owner and cannot express this interface.
This packet checks an explicit owner/axis permutation independently, without
requiring authors or a later source producer to justify zero-width ownership
and wire order in prose. It preserves the [type contract](type-system.md).

The obligation is structural resource/encoding binding at the selected 16-axis
boundary, beyond the finite six-bit contract matrix profile. The existing Rust
source checker already handles the small motivating example. This component
migrates its layout obligations to proved executable Lean checks; it adds no
new primitive quantum meaning or convenience-based acceptance exemption.

A layout is a pure coordinate permutation with coefficient +1; it performs no
gate, preparation, observation, disposal, split/join or implicit type conversion.
Every output owner corresponds to exactly one input owner of the **same full
basis type**, even at width zero. Register reshaping, splitting/merging owners
and arbitrary encodings need their own subsequent checked forms. Layouts are
currently submitted directly; no `.qli`-to-layout producer is claimed.

## Data and checking

Types use a canonical prefix list of atoms: `Unit`, `Bit`, `BitsN` for 0≤N≤8,
and `tK` followed by exactly K child types, 2≤K≤64. For example the flat type
`(Bit,Unit,Bit)` is `t3 Bit Unit Bit`; `((Bit,Unit),Bit)` is
`t2 t2 Bit Unit Bit`. They are unequal. `Bits1` differs from `Bit`; `Bits0`
differs from `Unit`. These are experimental wire types, not new source syntax.
A stack of pending child counts validates one complete tree and counts its
width, with no implicit reassociation, trailing type or empty tuple.

A port is a type and an ordered axis list of exactly its width. Each interface
contains at most 64 owners and 16 axes, with axis IDs forming exactly 0..n−1
without duplication. Unit and Bits0 ports have empty axes but occupy real slots.
Input and output interfaces must have the same owner and axis counts.

`owners[j]` is the input owner supplying output owner j. `axes[k]` is the input
axis supplying output axis k. Both maps have checked two-sided inverse lists.
For each output owner, its type equals the selected input type, and mapping its
ordered output axes through `axes` must give exactly that input owner's axis
list. Width equality alone, or a permutation detached from the owner ports,
is insufficient. This makes source tuple shape and within-register order
explicit in the layout contract.

The independently supplied requirement fixes the complete input/output
interfaces and both forward maps. It is read separately and compared exactly;
an artifact cannot rewrite the client's expectation. The inverse maps are
untrusted evidence, recomputed/checkable by finite composition. A structurally
valid wrong swap must fail the independent requirement. Missing, duplicated or
invented zero-wire owners must fail structure checking even though wire counts
are unchanged.

## Executable proof boundary

The theorems concern the actual `Layout.check` function: acceptance
implies exact agreement with the separate request, valid owner/axis permutations
and the checked port/type compatibility. For a forward map f and inverse g,
checking establishes f(g(i))=i and g(f(i))=i on every valid index.

The implementation reindexes finite basis assignments using these maps. Both
round trips are proved, then lifted to arbitrary coefficient-valued functions on assignments
and an unchanged reference index. The coefficient type is arbitrary, so this
is exact reindexing without a phase change, approximation or separability premise.
It is not a proof of the Born rule, general complex arithmetic, QPE, source
translation, parsing or native compilation. No dense matrix is constructed.

All declarations below are in [Layout.lean](../lean-kernel/QleisliKernel/Layout.lean):

| Declaration | Established scope |
| --- | --- |
| `check_conditions` | Actual acceptance implies equality with the independent request and successful structural checks. |
| `check_interfaces` | Both interfaces pass validation; owner counts and axis counts agree. |
| `check_owner_permutation`, `check_axis_permutation` | The submitted maps have bounded, length-matched two-sided inverses. |
| `check_ports` | Every output owner's exact type and ordered axes match its selected input owner. |
| `reindex_round_trip`, `reindex_reverse_round_trip` | Both coordinate round trips are identities for arbitrary values. |
| `check_reference_round_trip` | Actual acceptance implies the coefficient/reference round trip for every amplitude function. |

Prefix decoding and the relationship to source types are not mechanized here.
The equality/ownership/permutation statements refer to these executable data
structures and validators. General gate semantics, norm/probability theorems,
allocation/disposal and clean auxiliary release require subsequent components.

## Wire and capacity contract

The artifact starts `qleisli.layout 1 typed-layout-v1`; the independent request
starts `qleisli.layout-request 1 typed-layout-v1`. Both then contain:

```text
inputs N
port S typeAtoms... W orderedAxes...
... N port lines ...
outputs M
port S typeAtoms... W orderedAxes...
... M port lines ...
owners M inputOwnerIndices...
axes W inputAxisIndices...
```

Only the artifact appends `inverse_owners N ...` and `inverse_axes W ...`.
`S` counts prefix type atoms. Counts must match exactly. Integers are canonical
unsigned decimal tokens, separated by exactly one ASCII space. Every line ends
in LF; CR, tabs, Unicode separators, extra/unknown fields, missing final LF and
noncanonical numbers reject. The CLI entry is `--layout ARTIFACT REQUIREMENT`.
The existing word and phase-DAG commands retain their contracts.

Each file is at most 65,536 bytes. The pure checker independently limits each
interface to 64 owners and 16 total axes, each type to 128 atoms and at most
32 nested tuple constructors, and input plus output types to 512 atoms.
Each type width is at most 16; Bits atoms are at most 8. Maps are bounded by
the corresponding owner/axis counts. The charged conservative work bound is
`8 * (1 + inputOwners + inputAxes + inputAndOutputTypeAtoms)^2`, at most
2,000,000. The request obeys the same bounds. This is an explicit capacity
accounting model, not a theorem about wall-clock time or allocator behavior.

Success emits one JSON line in `qleisli.kernel-result` version 1 with profile
`typed-layout-v1`, `accepted:true`, `code:accepted`, stage `verification` and
statistics for owners, axes, type atoms, charged work and dense dimension zero.
Failures exit 1, return `accepted:false` and null statistics, and distinguish
`syntax`, `limit`, `io`, `invalid_ir`, and `contract`. File/decode failures name
artifact or requirement stage. No partial success is returned.

## Acceptance experiment

Check 16-bit interfaces without enumerating 65,536 labels. Independently test
small permutations on all basis assignments and on arbitrary complex amplitudes
with a reference index. Include altered type arity/nesting, owner and axis maps,
inverses, missing/extra/duplicated zero-wire owners, stale requirements,
well-typed wrong permutations, malformed prefix trees and every capacity.
Run pinned Lean build, reduction tests, compiled audit and fresh kernel replay;
replay the existing phase-word and phase-DAG suites. Preserve sources and actual
observations in the [development fixture](../tests/fixtures/lean_layout/README.md).
The subsequent [shared typed call component](lean-layout-dag-slice.md) composes
whole interfaces and checks both call adapters, with actual graph soundness.
General gates, encodings, schema proofs and source integration remain subsequent
CD-3 obligations.
