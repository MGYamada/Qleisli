# Source text and lexical boundary

These rules govern the current `0.3.0-beta` source scanner and parser in
constitutional edition 2026. Both finite project loading and sized explicit
module loading use one scanner, token stream, parser and source `Module`/`Span`
representation under the
[common frontend decision](https://github.com/MGYamada/Qleisli/issues/32).
A single mandatory judgment checks each complete original AST before finite or
selected concrete eligibility. Declaration and lexical identities, types,
static premises, owner/access rules, body dependencies and principal effects
come from the same original-source checker in `src/frontend/check.rs` and
`src/frontend/check/`. Every declaration is checked, including private and
unused siblings, both arms and zero-iteration bodies. Parsing alone confers
neither source approval nor native verification evidence.
The [qrate and artifact Reference](packages-and-artifacts.md) distinguishes
canonical module/declaration identity from source-file storage and resolved
configuration. Its edition-binding gaps are separate from scanner/parser checks.

The [elaboration whitelist](elaboration.md) specifies permitted surface-to-core
expansion, evaluation order, owners, phase, original locations and remaining
independent checking obligations. It does not grant an unsupported projection.

Runtime wildcard, duplicate-name and exact tuple/Unit rules use the common
pattern traversal. Ordered static kinds and runtime parameter names retain
original declaration ordinals and binder identities. A static kind may refer
only to preceding static parameters; complete declaration registration does
not make a forward static kind available. Valid forward and backward sibling
references resolve against the complete registered declaration table. Quantum
values have fresh
dynamic owner identities distinct from these lexical keys. Arguments and RHS
expressions evaluate completely, once, from left to right before binding.

The raw AST also retains bare lexical assignment and a `let mut name = ...`
marker solely for typed refusal. Neither form can occur in a successfully
checked program or be lowered to replacement. Assignment inspects the resolved
destination's current type before checking its RHS; even a consuming RHS does
not authorize replacing a quantum-containing place. A mutable binding checks
its initializer's type to distinguish quantum ownership from unsupported
ordinary mutability. Both refusals retain original byte locations. `mut` is
contextual: `let mut = 0; mut` remains an ordinary immutable binding and use.
General field/index assignment syntax and ordinary reassignment are unsupported;
these diagnostic forms grant neither. See the
[assignment and mutability boundary](rust-boundary.md).

One private source collection retains complete original bytes, common AST and
provenance. Filesystem entries retain their selected path; in-memory entries
carry no invented file or manifest. Both loaders add the fixed registry's eight
ordinary source modules and validate its edition-2026 manifest. Both loaders
apply their byte policies to bundled bytes before copying or parsing;
placement under `std::` supplies no checking exemption. The selected loader
also reserves all eight bundled module slots. It accepts 1 through 56 supplied
modules: the eight bundles count toward its
64-module ceiling and its 1 MiB aggregate byte limit. Its 64 KiB/module limit
also applies. Finite bounded and explicit legacy byte-loading policies remain
separate; this unit does not make an unbounded byte loader bounded.

The finite loader consumes the collection into the existing mutable `Project`
compatibility view. Finite checking, compilation and checked-effect operations
reconstruct facts from that view's current original ASTs; no stale parallel
collection or approval is reused after caller mutation. Source-only
documentation and rendering do not acquire semantic checking from this rule.
The selected path retains its immutable originals
and records a concrete projection result for each declaration only after the
complete common judgment. A located unsupported projection is an eligibility
failure when that definition is requested, not a skipped original body or
fallback source approval. Retirement of that lowering projection, canonical
generic std APIs and source-preservation proofs remain separate work in
[#32](https://github.com/MGYamada/Qleisli/issues/32) and
[#317](https://github.com/MGYamada/Qleisli/issues/317).

## Parsed finite type declarations

The parser retains fieldless `enum Name { A, B, ... }` and named
`struct Name { field: Type, ... }` declarations, optionally preceded by `pub`.
Record fields retain their own `pub` marker. The common frontend elaborates
these into ordinary nominal type trees, with original module/declaration/source
identity, variant order and complete ordered field types. Signatures retain
both `T` and `Q<T>` without reducing nominal identity to physical width.
Common preparation retains and checks explicit fieldless `Type::Variant`,
`Type { field: expression, ... }` and ordinary `value.field` forms, including
original type/member identity, visibility and written initializer order; see
the [type model](type-model.md#opaque-basis-specialization-in-the-selected-profile).
Common preparation also checks ordinary `match` with exact qualified enum
labels and exhaustive, disjoint arms. Runtime blocks allow an expression or
block per arm; classical bodies allow ordinary expressions. The finite project
adapter executes eligible closed ordinary callers through the strict native
ordinary-v2 route, including ordinary parameter functions inlined by the common
emitter. Nongeneric public selected ordinary runtime and classical roots use
that same emitter and native gate after a fresh complete original-source
judgment. Small quantum temporaries use the same Raw emitter and complete
hidden-history checks. Nongeneric mixed interfaces, including nominal quantum
ports, use the separate runtime-v1 gate with full original type/storage trees.
Generic selected/dependency transport, full qmatch and
nominal finite-table consumers remain unfinished. The
[type model](type-model.md#opaque-basis-specialization-in-the-selected-profile)
and [production boundary](production-boundary.md#mixed-runtime-root-requests)
specify the distinct capacities and checked scope. Common frontend facts alone
provide no execution evidence or accepted handle.
An explicit Rust check-only carrier adapter uses the same complete judgment
and source lowering to check an independently requested exact logical matrix;
its sealed typed result grants no ordinary execution. Its precise scope and
remaining AST-preservation duty are described in the linked type model.

Nominal names already participate in the common module/import/reexport
resolver as a distinct collection-local type category. Transparent reexports
retain the original declaration and visibility; source-path traversal retains
each alias module. The conservative initial profile requires an unambiguous
binding per module/import spelling. Function/type collisions, empty enums and
duplicate variant/field names reject at the original offending name. These
name checks precede finite field elaboration. Fields must be ordinary finite
types: unknown, recursive, non-type and quantum-owned fields reject. Closed
field sizes reuse the existing Nat-helper arithmetic and premise checks;
this adds no general `const<T>`. A local ordered Basis binder cannot fall back
to a global enum. Callable and operation consumers reject a type target.

For nominal elaboration, complete retained module sources must parse to the
supplied ASTs. The check also inspects original enum/struct tokens, so deleting
AST declarations cannot hide them. Comments and identifier substrings are not
declarations. Non-nominal constructed-AST consumers retain their existing
boundary. This original-byte check is not a general source-preservation theorem
or the pending source/native evidence/cache binding.

Prepared nominal facts retain the original references in field types and closed
Nat-helper calls. Ordinary provenance collection follows these type dependencies,
their transparent reexport chains and the helpers' original lexical dependencies.
It checks retained declaration/source/occurrence identity before collecting
bytes. This is untrusted provenance preparation. The ordinary-v2 route separately
binds actual signature and recursive-field type paths, nominal origins and
complete input/result storage; validating an unused helper grants no source-row
coverage. Other intermediate nominal modules still require their own typed
dependency transport. A host Basis description alone grants no execution
authority. Read-only retained nominal maps preserve the existing `Send + Sync`
source-handle contract.

The Rust `Project` view labels `ResolvedImport.kind` as
`ImportKind::Function(FnKind)` or `ImportKind::Type`. Its `declaration_span`
points to the original declaration in the canonical `module`; `span` remains
the importing occurrence. Rust callers that previously consumed a bare
`FnKind` must match the import category explicitly. Project loading and this
descriptive metadata do not grant source acceptance or a native handle.

Each declaration retains its whole original span, body span and ordered
variants/fields. Named type paths retain all qualified segments and their byte
span. Type/member documentation attaches to those original occurrences;
source-only rendering makes no verification claim. An empty record remains
a distinct declaration; the parser does not replace it with Unit. Empty enums
and invalid/duplicate type members do not acquire semantic validity by parsing.

The bounded syntax profile admits at most 64 members per declaration, using
the existing source product limit. Payload variants, discriminant assignments,
tuple structs and generic type declarations are not parsed. Ordinary match
uses the same 64-member bound for its arms. `enum`, `struct`, `match` and `qmatch`
are reserved keywords in the unpublished beta language; rename existing
functions, bindings or module paths that used those identifiers. These parser
changes do not complete [finite ADTs](https://github.com/MGYamada/Qleisli/issues/64).
The coherent exact-label form has the separate checking and execution limits below.

## Exact-label coherent selection

`qmatch(selector, target) { label => operation, ... }` selects a coherent
operation without measuring its selector. Each arm names one resolved static
operation; it is not an ordinary expression or block. Labels may be written in
any order, but must cover the selector's logical basis exactly once. Wildcards,
ranges, payloads, guards and dynamic arm calls are outside this form.

Common preparation requires one `Q<A>` selector and one distinct `Q<B>` target,
and returns `(Q<A>, Q<B>)` with both complete type trees unchanged. Zero physical
width does not remove either linear owner. For `Unit`, `Bit` and closed
`Bits<n>` with `0 <= n <= 6`, labels are canonical decimal ordinals from `0` to
`cardinality(A)-1`. For a fieldless nominal enum they are qualified variant names
of that exact original declaration, respecting imports, reexports and visibility.
Unused physical tags are not enum labels. The common form has at most 64 arms.

Every arm must have the exact target interface, a valid Unitary effect and
Controlled access under the existing operation rules. A generic earlier arm,
a constant selector or an unused declaration cannot skip a later arm's type,
effect, access or dependency obligations. Unitarity alone grants neither
control nor inverse access. All arm phases remain exact.

If arm `s` denotes the exact operator `U_s`, the operation maps each basis
vector `|s,y>` to `sum_z U_s[z,y] |s,z>` and extends linearly to every input,
including inputs entangled with an external reference. Thus it preserves
coherence between selector sectors and agrees exactly with `qif` for `Bit`.

The finite executable slice currently accepts built-in selectors only and
retains the existing encoded-contract limits of six joined selector/target
bits and 1024 circuit steps. Selector axes precede target axes, so `(s,y)` has
integer coordinate `s + 2^selector_bits * y`, independently of written arm
order. The complete proposed circuit and independently obtained exact block
meaning go through a fresh native encoded equation before emission; a Rust
sector projection cannot issue acceptance. The emitted Raw root still undergoes
ordinary native checking.

```qli
pub unitary fn select(s: Q<Bit>, q: Q<Bit>) -> (Q<Bit>, Q<Bit>) {
    qmatch(s, q) { 1 => global_phase_eighth, 0 => h }
}
```

Nominal selector execution and the selected specialization projection remain
explicitly unsupported. Exposing the full twelve-joined-bit/64-label boundary
still requires original source binding and native integration of the restriction
and arm checks below; the small slice does not replace that requirement. The internal finite restriction
component now proves correspondence through actual contributions, accumulation,
steps and complete circuit execution, and checks every ordered local sector.
Its internal Raw component checks the original pure program and independently
reconstructed trace, retaining every circuit event and proving that omitted
identity reorders are literal identities. The physical port/wire frame is
checked separately from logical source owner transport; empty wire lists alone
cannot identify or order zero-width owners. Physical widths do not establish
original nominal or source type identity.
The enclosing QIRF component reuses fresh graph/root checks and proves exact
original-program embedding into that pure Raw subject. It rejects observing,
classical and branch instructions in this straight-line component.
Its internal nominal component independently checks original type declarations
and each ordered owner's code, then compares each active physical sector on
that code with the exact requested logical map. Product labels retain their
actual physical coordinates; padding sectors are checked separately and do not
increase logical cardinality. The original requested-sector checks and the new
computed-sector path share reconstruction; the refactor preserves all old
results, errors and remaining work.
The internal arm component reconstructs each original QIRF implementation's
logical map and checks a separate controlled implementation against exact
identity/arm sectors. One fresh graph checks the main plus all actual arm/control
subjects named by the request. Root membership comes from those subjects;
unrelated nodes still refuse, and root membership supplies no source usage.
Ordinary requests keep their original main-only root and reachability rules.
Every canonical logical ordinal binds its actual original arm, independently
of written order. The source component binds original named functions to actual
function-evidence entries and their fresh complete inputs/dependency snapshots.
It preserves the original function bytes, full target types and public effects.
An independent source metadata component now retains the actual qmatch token
occurrence in its original function, complete named-arm parameter/result owner
forests, canonical enum labels and original import/reexport paths. It rejects
public observing/isometric arms and keeps an absent private annotation unknown;
body checking must independently establish its inferred effect. Original
quantum parameter patterns and structural let/tuple moves now identify operands
in the complete live source frame. Quantum product owners remain atomic;
ordinary tuples can group separate owners. A two-port subject retains the exact
original parameter/result order and distinct logical identities at zero width.
It cannot sharpen a public observing/isometric function to Unitary. Unknown
prefix expressions refuse instead of contributing unproved type facts.
The complete structural suffix and result retain actual returned roles. An
independent run over original Raw joins, splits and owner-moving operations
compares those roles with actual output-token order, including at zero width.
A matching zero-width source/Raw permutation is allowed; a mismatched one
refuses. Opaque-owner refinements, allocation/release and general calls/control
flow still need their checked source/representation rules. The internal
native/QDV component retains its actual graph/request but grants no ordinary
source execution handle. General source binding and nominal execution remain
unfinished. Common enum checks, native acceptance
of a proposed circuit and conformance tests do not prove original-source
preservation or complete nominal integration. Ordinary nominal execution uses
the separate ordinary-v2 route above. `qif` keeps its existing
fixed `0`, then `1` syntax and access contract.

## One structured quantum result boundary

Verified quantum-core functions are expression-oriented. A body has one
structured result boundary: its final block expression. Every runtime branch
must retain and merge the complete required owner frame and exact result tree.
Both arms are checked even when one is statically unreachable. No early exit
can discard, release, reset or uncompute a live owner implicitly.

Early `return q`, residual propagation `q?`, runtime `panic!`, `assert!` and
`unreachable!` macro edges, unwinding, hidden abort and partial quantum
functions are not admitted. This applies to Unitary, Isometry and Observe bodies;
an observing effect does not authorize a hidden exit. Syntax refusals explain
the final-expression alternative and retain the original token's byte span.
Use explicit ordinary branches, admitted coherent control and finite folds
under their own owner/effect rules; `qmatch` retains the separate limits above.
This chapter grants no `qreturn` or `qtry` form.

For example, `unitary fn keep(q:Q<Bit>)->Q<Bit>{q}` has the structured result;
replacing its body with `{return q}` is invalid. A final `if` whose arm returns
Unit while the other returns `Q<Bit>` is also invalid; refusal inserts no
cleanup. Ordinary identifier names retain normal resolution. A variable or
checked ordinary function named `return`, or a function named `panic`, is not
a return/abort primitive; an ordinary `return(q)` call keeps normal call rules.
Comments containing these spellings do not create executable edges.

A future host orchestration language may specify `Result`, residual exits,
assertions or process failure separately. No such host failure semantics is
imported into the present core. Ordinary error values, if separately admitted
as data, would not themselves imply propagation or unwinding. The runtime
checker/transport's fail-closed refusal is likewise not a source-level exit.

## Checking failures and quantum execution

Within the declared finite model, a supported verified quantum-core operation
has no implicit exceptional execution edge. This applies to Unitary, Isometry and
Observe: measurement supplies its specified ordinary outcome and instrument,
not permission to panic, unwind, abort, partially return or abandon an owner.
This totality requirement is the adopted failure contract; it is not a claim
that every source form or target has a completed production Soundness proof.

Invalid sizes, type trees, static indices, access/capability requirements and
required constraints reject during checking or specialization. The current
`take_bit[n,k]` requires an established `k < n`; it does not compile an unknown
index into a quantum runtime bounds trap. Checked Nat arithmetic cannot wrap
or defer overflow to a quantum exception. Bounded elaboration, unsupported
profiles and unproved obligations also reject before an executable handle is
issued for that proposal. See [static checking](static-language.md).

An explicit ordinary result such as a Bit may select an ordinary `if`, but
both arms must satisfy the complete required owner frame, exact type tree and
effect rules. A recoverable alternative returns its declared data and owners
through the normal structured boundary. It must not implement a hidden exit,
implicit cleanup or a success-only path. For example, an operation may return
`(flag, q)` or `(flag, x(q))` in its two arms when their declared interfaces
agree; omitting `q` in one arm is invalid. The unchanged caller frame, including
correlated owners and zero-width quantum owners, still participates in the
branch merge. An ordinary condition does not establish separability.

The finite project path supports those runtime ordinary branches. The current
selected specialization projection can reject such a runtime expression as
unsupported during preparation; it must not turn it into an unchecked body or
a runtime failure path. This profile restriction is separate from the language
contract and the shared original-body ownership/effect judgment.

Source failure handling cannot reset/discard workspace, discharge a clean or
dirty restoration obligation, erase exact phase or owner ordering, or shorten
an access lifetime to omit required work. The absence of an unwind construct
does not prove pending access, restoration, target or quantitative resource
contracts. Their implementations must obey this rule when admitted.

Operating-system failure, verifier/transport failure, backend crash and device
loss are external faults, outside the quantum-core operational theorem unless
an explicit future target contract models them. They provide no source escape
hatch or owner-disposal semantics. Missing, incompatible, timed-out or malformed
native checking rejects without an accepted handle or fallback. Such a refusal
is a failed attempt to check an artifact, not an executed quantum branch.

Reference simulation can separately refuse its host execution/component/space
budgets or report a numerical/internal-consistency error. No result distribution
is thereby certified as the successful program result. These host limits are
not static quantum resource certificates, and reporting an error is not proof
of physical state recovery or clean/dirty restoration after an external fault.
The current Rust simulator and native IO retain their disclosed correspondence
assumptions; the core failure contract does not prove host panic freedom.

## Ordinary function effects and assertions

An ordinary body-bearing function may use `fn`, `unitary fn`, `isometry fn` or
`observe fn`. A public function that processes quantum values or operations
must explicitly use `unitary`, `isometry` or `observe`. This includes closed
functions, zero-width owners, quantum intermediates and operation formals;
ordinary classical public functions may retain inference. The order is
`Unitary <= Isometry <= Observe`; composition takes the least upper bound. Copying
an ordinary Bit does not copy a quantum owner or add a quantum effect.

An explicit effect prefix permits quantum processing even behind an entirely
classical signature. External quantum-use checking conservatively retains that
public permission instead of inspecting the implementation's current use flag.
An unannotated public classical API cannot acquire hidden quantum work without
changing its public declaration and passing the complete checks again.

The complete body is checked independently. Its inferred effect must fit the
declared upper bound; a prefix is never an inference seed. An Observe body
cannot assert Unitary or Isometry, and an Isometry body cannot assert Unitary.
An implementation inferred as Unitary may expose Isometry or Observe, but
external callers use only that checked public effect, even with source
available, inlining, specialization or a cached provider. Changing the public
effect is an API change; a body-only edit cannot silently regenerate it.

Same-module calls use the checked internal inference of the original callee.
Calls across original module identities use its checked public effect;
an import alias does not change that identity. Internal inference itself
retains any further external boundary: an internal wrapper cannot wash an
external Observe call into Unitary. Private functions retain inference.
All branches, zero-count fold bodies and unused declarations are checked.
Type, ownership, access and termination checks still apply independently;
an annotation cannot supply a missing check or arbitrary mathematical Meaning.

The selected vocabulary in [#57](https://github.com/MGYamada/Qleisli/issues/57)
is **isometry**: `V†V = I_input`, without a claim of surjectivity or executable
inverse/control access. Zero-state preparation is an isometry but not a unitary
between its different input/output dimensions. A unitary additionally satisfies
`VV† = I_output`. In categorical terminology these are a dagger-monomorphism
and a dagger-isomorphism, respectively.

The old source prefix `iso` is retired in 0.3.0. Replace `iso fn` with
`isometry fn`; the old word produces a lexical migration error located at its
original token before native checking. It remains reserved for that error,
not an accepted alias or an ordinary identifier. Comments and longer ordinary
identifiers such as `isotope` and `iso_value` are unaffected.

The canonical names are:

| Surface | Canonical spelling |
| --- | --- |
| Source effect assertion | `isometry fn` |
| Rust effect | `qleisli::ir::Effect::Isometry` |
| Rust function and token kinds | `frontend::ast::FnKind::Isometry`, `frontend::lexer::TokenKind::Isometry` |
| Lean Raw effect | `QleisliKernel.Semantics.Raw.Effect.isometry` |
| Lean hierarchy effect | `QleisliKernel.Hierarchical.Artifact.Effect.isometry` |
| Lean retained bounded QFT graph effect | `QleisliKernel.QftGraph.Effect.isometry` |

Rust callers migrate `Effect::Iso`, `FnKind::Iso` and `TokenKind::Iso` to their
`Isometry` variants; there is no Rust compatibility alias. Body-effect
diagnostics also use `Isometry`.

The three Lean names are reducible aliases for their existing `Effect.iso`
constructors. They provide the canonical spelling for new Lean expressions
without changing constructor identity, generated recursors, existing `.iso`
case names or derived `Repr` output. Historical formal statements and callers
using the constructor retain that compatibility. The QFT graph alias changes
only an existing public type's vocabulary; it adds no QFT implementation.

Versioned JSON/QIRF effect tags, the checked source graph's effect tag and
native hierarchy adapters retain `"iso"`; the binary hierarchy effect tag
remains `1`. These explicit transport exceptions neither introduce a second
source effect nor grant inverse/control access.

`QleisliKernel.Raw.State.iso` is an internal allocation-tracking Boolean, not
an effect assertion or evidence of the isometry law. Local proof witnesses
named `iso` likewise are not public effect vocabulary. These implementation
names and the compatibility constructors remain unchanged; naming alone
establishes no semantic property or constitutional guarantee.

Both arms and the body of a zero-iteration static fold participate in common
checking and effect inference. A decreasing runtime self-call uses the least
effect solution only after the actual decrease check; mutual dependencies
reject. An invalid or unresolved source body yields no checked effect fact.
A valid source body may retain its principal effect while its requested
concrete projection or lowering remains unsupported. These source facts are
not accepted IR handles or a source-preservation proof; finite and selected
concrete lowering and native checks remain distinct.

**`"externally unitary"` is not supported.** The current compositional rules
retain internal observation, reset and discard as Observe. Even if a separate
argument claims the induced public channel is unitary, an ordinary annotation
cannot replace those rules with an external certificate. A contradictory
annotation is therefore an effect/semantic error. Its diagnostic states the
inferred and asserted effects and explains this unsupported semantic boundary,
without a GitHub Issue reference. This does not prove that the public channel
is mathematically non-unitary; it means the proposed external justification
is unavailable. Externally isometric justification is likewise unsupported.

The Rust interface exposes immutable `ProjectEffects` from
`project_effects_with_kernel` for finite projects, and `ParsedProgram` facts
for selected source. `function_effect` exposes the internal inferred effect,
checked assertion, typed quantum-use flag and distinct `public_effect()` for
inspection. Only `public_effect()` (also `public_function_effect(path)`) is an
exported effect contract; inspecting internal inference grants no eligibility.
Their `documentation` methods render the public contract for public functions
and inferred/asserted diagnostic facts for private functions from retained
source bytes; changing a source file afterward cannot rebind
the report. Concrete finite declarations still undergo native verification;
generic facts remain conditional on their checked source premises. The
source-only `doc` command and `render_markdown` keep their explicit lack of
semantic checking and do not manufacture inferred facts.

Source-selected providers use the checked effect visible in the caller's
original module. Host-selected public providers always use the public contract,
including unused bindings; the host cannot claim same-module status. Explicit
private provider bindings supported in the selected entry's own module retain
their existing internal visibility. Generic bodies use formal bounds and cannot
sharpen them from a fortunate later provider. Adjoint/control and pure contracts
still require their separate evidence and a visible Unitary effect; other
general arrows obey their declared effect ceiling. A provider input/output
shape mismatch remains a type error; it is not external effect justification.

Source contract effects and actual artifact effects are distinct. A conservative
Observe contract does not rewrite a genuinely pure Raw body as observing, nor
does that Raw body's sharper classification grant an external source capability.
Actual operations and histories still reach fresh native checking. Concrete
profiles may refuse otherwise source-valid contracts: the current observing
FunctionEquality profile requires genuinely observing original artifacts, so
conservative Observe annotations on pure bodies cannot select a pure-contract
fallback. Such refusals disclose a concrete-profile limit, not a false pure
label, source effect error or general preservation theorem.

## Instruments and ordinary feed-forward

The judgment `Γ ; Δ ⊢ e : T ! Observe` gives an upper bound on the quantum
behavior of the complete expression. Fix the ordinary inputs `x`. Let `A` and
`B` be its complete input and output quantum interfaces, including the live
caller frame retained by the ownership judgment, and let `c` range over the
ordinary projection of its declared result. The intended meaning is a finite
quantum instrument with completely positive, trace-nonincreasing maps
`Φ[x,c] : L(A) -> L(B)` whose complete sum is trace preserving.

For the complete hidden histories `h` and their public-result projection, write:

```text
Φ[x,c](ρ) = Σ_{h : public(x,h) = c} K[x,h] ρ K[x,h]†
Σ_h K[x,h]† K[x,h] = I_A
```

Every history contributes its unnormalized weight. Hidden measurement, reset
and discard outcomes remain in the sum even when they are not returned as
ordinary data. If the ordinary result is Unit, its public outcome set is the
singleton `{()}`. For every finite external reference `E`, the same instrument
acts on an arbitrary joint input through `Φ[x,c] ⊗ id_E`; separate owners do
not imply a product state. Normalizing a selected branch or comparing only
outcome probabilities does not establish this contract.

The effect order `Unitary <= Isometry <= Observe` is an order of permitted
quantum behavior. For fixed ordinary inputs, a pure implementation has one
public result and acts by its exact `U[x]` or `V[x]`, with `U†U = UU† = I` or
`V†V = I` respectively. Their density maps are singleton instruments. The
underlying pure meanings still retain exact phase and their separate inverse
and controlled-access obligations. Instrument equality cannot erase those
contracts or turn a public Observe interface into a pure capability.

An Observe bound permits a pure implementation and does not require every call
to create a public Bit. Body inference remains independent, and callers across
an original module boundary use the checked public bound. Observation, reset
and discard still infer Observe under the existing compositional rules, even
when a separately described public channel happens to be pure.

Destructive `measure_z : Q<Bit> -> Bit` consumes its input owner. For result
`b`, its map uses `K[b] = <b|`, retaining the conditional state and weight of
all other owners and references. The existing state-retaining example is
`std::measurement::parity_zz`: it returns both data owners and a Bit, consumes
its internal meter, and acts by `P[s] = (I + (-1)^s Z tensor Z)/2`. Coherence
within each parity sector is retained. Retaining an owner does not promise an
unchanged state. The explicit discard-plus-preparation implementation of reset
instead consumes the original owner and returns a fresh zero owner.

Ordinary `if` uses an ordinary Bit. Following observation it selects the next
operation separately in each complete history; both arms must pass checking
and return the same complete result and live-owner shape, including zero-width
owners. Sequential composition retains every intermediate history and its weight;
only histories with the same final public result are summed. A coherent `qif` uses its separately checked coherent
operation and preserves coherence between selector sectors. An ordinary branch
cannot inspect a live `Q<Bit>` or insert an implicit measurement.

These are normative source obligations. Ordinary native validity currently
checks its stated structural ownership and classical-scope properties; general
EffectSound/CPTP and source preservation remain unfinished. The dedicated
[original-artifact instrument request](production-boundary.md#original-artifact-observing-instrument-requests)
checks both original bodies, complete Kraus sums, requested complete signature
trees and their ordered root-port projections, and every unnormalized public
map on arbitrary finite references within its bounded profile. Recovering the
original source type trees remains a separate obligation. That profile requires genuinely observing original artifacts;
a conservative public Observe bound on a pure implementation can therefore be
well typed while this particular request refuses it. Its refusal supplies no
pure-contract fallback. The [primitive boundary](primitive-boundary.md) and
[standard-library contracts](stdlib.md) give the admitted measurement actions.

## Observation and postselection

Ordinary Observe has the complete-instrument contract above: the sum of all
outcome maps is trace preserving. An individual outcome map may decrease trace;
its trace is that outcome's probability, not permission to discard the other
outcomes and advertise the selected map as the whole operation.

Qleisli 0.3.0 provides no source postselection effect or construct. Keeping only
chosen outcomes and continuing on their renormalized state is not authorized by
Observe, an ordinary `if`, a successful check or a clean-release operation.
Returning a success Bit together with the declared owners is an ordinary
instrument only when both success and failure outcomes remain in its semantics.
Classical feed-forward executes the selected arm for each history; it does not
remove histories whose measured Bit selects the other arm. Hidden outcomes of
explicit discard also remain in the complete sum.

A future postselection proposal would need a distinct semantic category. For a
chosen outcome set `S`, it would have to specify the trace-nonincreasing map
`Φ_S = Σ_{c in S} Φ[c]`, its success probability `p_S(ρ) = Tr(Φ_S(ρ))`, and any
conditional state `Φ_S(ρ) / p_S(ρ)` only where `p_S(ρ) > 0`. It must expose
success and failure outcomes, ownership on both outcomes, composition with
surrounding operations and reference systems, and resource accounting for any
requested retries. A zero-probability event supplies no conditional state.
This describes requirements for a future proposal, not an admitted API or an
extension of the current effect order.

Postselection is distinct from the [checking and external failures](#checking-failures-and-quantum-execution)
already described above. A failed check, panic, target fault or exhausted host
budget supplies no accepted successful quantum branch. The bounded host trial
driver separately reports retries, exhaustion and execution errors; it retains
no quantum state and grants no source-level postselection or clean-release
capability. Exact clean release still requires its independently checked
all-input and reference-safe zero-return obligation, without conditioning on a
favorable observation.

Numerical trajectory sampling may normalize a branch after drawing its outcome
from the supplied random source. That representation does not permit the source
to choose a favorable outcome, erase its probability or omit alternative outcomes
from the instrument contract; simulation retains its stated numerical and runtime
assumptions. The observing Physical Realizability target concerns the complete
instrument and actual admitted realization without hidden conditioning, as in
[the realization contract](realization.md). This boundary does not discharge
ordinary-root EffectSound/CPTP, source/runtime preservation or the broader
QS, PR, quantitative RS and EXACT obligations.

## Total classical declarations

Provisional `static fn` declarations instead return static Nat values through
the [bounded helper rules](static-language.md#provisional-bounded-nat-helpers).
They have no runtime interface, effect or accepted-handle authority.

`classical fn f(pattern: T, ...) -> U { expression }` declares a total, pure
finite function on ordinary values. Its body is one restricted label expression:
names, `()`, `0`/`1`, ordered products, eager `not`/`and`/`xor`, and acyclic calls
to other classical functions, plus the existing nullary ordinary
`empty_bits()` language primitive constructor, requiring no import, with its exact `Bits<0>` signature.
Other quantum primitive calls remain excluded. It has no runtime statements, observation or
quantum capture. Parameter/result trees and argument-list arity remain exact;
noninjective functions are permitted.

The same checked body may be called in ordinary runtime expressions, existing
Meaning/predicate construction and coherent `basis` expressions. Runtime
arguments evaluate once, left to right, before parameter binding. Their effects
and owner consumption remain in the caller, including when an ordinary result
is ignored. An already measured Bit is ordinary data; a live `Q<T>` cannot be
passed as `T` without explicit observation. For example:

```qli

classical fn flip(b: Bit) -> Bit { not b }
fn invert(q: Q<Bit>) -> Q<Bit> { basis q as b { flip(b) } }
fn read_flipped(q: Q<Bit>) -> Bit { flip(measure_z(q)) }
```

Coherent lifting independently requires injectivity of the complete map;
computed predicates retain their separate exact cleanup contracts. A classical
declaration or its name grants no inverse/control access, Meaning evidence or
native acceptance. Meaning declarations remain descriptions, not runtime
callees. Supported Unit/Bit/product and exact closed empty-register runtime calls lower their original
expression nodes through ordinary operations in both concrete consumers;
ordinary execution does not evaluate a precomputed truth table. Nonzero finite
registers and general selected hierarchy coherent-lift conversion retain their
separate profile refusals; selected Raw supports bounded complete label maps.

The retired declaration spelling `basis fn` rejects with a located migration
diagnostic directing authors to `classical fn`; there is no compatibility alias.
The coherent expression `basis q as pattern { expression }` and static
`A: Basis` parameters keep their existing meanings. Historical first sources
and validation records retain their original spelling; current replay selects
explicitly recorded derivatives.

## Bytes, characters and positions

Source is UTF-8. Every source span is a half-open byte interval in the original
input. Source loading, scanning and diagnostics must not normalize those bytes.
LF and CRLF are accepted line endings. Ordinary whitespace is ASCII space or
tab; bare CR, vertical tab, form feed and non-ASCII whitespace reject. Bidi
control characters and other control characters reject, including in comments.
A rejected Unicode scalar's span covers its complete UTF-8 encoding.

Identifiers use ASCII letters or underscore initially, followed by ASCII
letters, digits or underscore. Comment prose may contain other ordinary Unicode
characters. This does not admit Unicode identifiers or alternate whitespace.

The existing finite keywords are reserved in the common grammar, including
identifier positions formerly treated contextually by the sized parser:
`use`, `meaning`, `static`, `Op`, `requires`, `Apply`, `Adjoint`, `Controlled`,
`permutation_by`, `phase_by`, `checked_op`, `bind_op`, `inverse_op`, `then_op`, `tensor_op`,
`controlled_op`, `repeat_op`, `conjugate_op`, `pub`, `classical`, `basis`, `isometry`, `iso`, `unitary`,
`observe`, `fn`, `let`, `if`, `else`, `qfor`, `do`, `pure`, `with_computed`,
`apply_contract`, `adjoint`, `repeat_static`, `qif`, `qmatch`, `enum`, `struct`,
`match`, `true`, `false`, `not`, `xor`, `and`, `Unit`, `Bit`, `CBit` and `Q`. The existing import exception admits
`basis`, `observe` and `classical` immediately after `std::` as module names.

`iso` remains reserved solely for the effect-prefix migration error described
above; it does not introduce an accepted declaration or identifier.

`do` and `pure` remain reserved tokens solely to reject the removed coherent
notation with a migration diagnostic. They introduce no accepted expression,
alias, monadic operation or state preparation. `classical fn` declares total
ordinary computations; the distinct `basis` expression is specified in
[Coherent basis maps](coherent-basis.md).

`checked_op` is the reserved exact-meaning constructor described in
[Checked operations](checked-operations.md). The retired `bind_op` spelling
remains reserved solely for a located migration error; it is never an alias.
Existing declarations or finite filesystem module names using `checked_op`
as an ordinary identifier must be renamed. Occurrences in comments and longer
identifiers remain unaffected. The lexer scans the complete file before
parsing, so a later retired token can precede an earlier grammar error. Token
capacity rejection keeps precedence over that token's migration diagnostic.
Selected explicit module keys retain their separate existing validation rules;
this change does not unify them with finite filesystem module names.

`Applicable`, `Adjointable` and `Controllable` are contextual predicates in
`requires` clauses, followed by an operation parameter in parentheses. They
remain ordinary identifiers elsewhere. The old `Apply`, `Adjoint` and
`Controlled` tokens and `inverse_op`/`controlled_op` remain reserved for located
migration errors. `adjoint(U)` is the current static description and
`adjoint(U)(q)` its application; the two-argument form is retired.
`controlled` and `inverse` retain ordinary single-stage name resolution.

`Bits`, `CBits` and `Nat` are contextual type/kind names and remain valid names
in identifier positions. `as` is contextual: it separates the quantum input
expression and pattern in `basis input as pattern { expression }`, and remains
an ordinary identifier elsewhere. Retained tokens for `CBit`, `true` and `false` permit
targeted rejection of their old type/literal uses; they do not keep those uses
accepted. Type-position `CBits<n>` likewise rejects. The replacement types and
literals are `Bit`, `Bits<n>` and `0`/`1`.
`qfor` is reserved and starts an explicitly static quantum-owner fold.
`for static` starts an ordinary-only fold. The `for` word, the `in`/`carry` parts of either header,
and `yield` at the start of a fold tail recognize their existing sized roles.
Those words remain identifiers in other positions. `controlled(op)(args)` is
the existing controlled-application construct; `controlled(q)` remains an
ordinary call to an identifier. Neither spelling guesses a resolved provider
category or grants control access.

Numeral tokens retain their decimal spelling. The scanner does not convert
them to a machine integer, infer a Bit/Nat category or grant a static value.
The common natural-expression parser rejects leading zeroes except `0` and
literals exceeding `i128`. It retains addition/subtraction, multiplication and
parentheses with source spans; multiplication binds more tightly than addition
or subtraction. Existing static checks still require nonnegative, bounded and
supported expressions. A power repetition count has the existing `2^e` form,
with compound exponents parenthesized; this is not general exponentiation in
the natural-expression language. Finite lowering evaluates each original
`power` count under its complete static bindings, using checked ordinary-u32
intermediates and a 0-through-4096 bound on every nested count. An outer zero
does not excuse an invalid inner count or a child's closed contract. Ordinary and basis Bit expressions
share the `0`/`1` literal recognizer; other numerals are not Bit values. This
does not change static-Nat literals or infer a quantum owner from a numeral.

## Comments and documentation

`//` starts a line comment. `/* ... */` is a nested block comment. Unclosed
block comments reject. Character validation applies equally to code, ordinary
comments and documentation comments; comments cannot hide forbidden controls.

`//!` and `/*! ... */` are inner documentation comments. `///` and
`/** ... */` are outer documentation comments, except that `////`, `/***` and
`/**/` begin ordinary comments. Documentation text may normalize CRLF to LF in
its extracted metadata; source offsets continue to refer to the original bytes.

Classification and placement are shared. Outer docs must precede a function
or use item; inner docs belong to the module or the initial documentation area
of a function body. The common declaration attachment check rejects misplaced
docs before either profile checks source. Metadata remains descriptive and is
available through `parse_documented_module`; ordinary module loading may retain
only the syntax and original source. No profile may silently ignore invalid
placement.

## Punctuation and bounded scanning

The physical scanner recognizes individual punctuation marks. The common lexer
forms composite tokens only from immediately adjacent marks: whitespace and
comments never join them. For example, `::` is distinct from
`: /* comment */ :`. The token stream includes the existing sized arithmetic
and comparison marks; `==>` is `==` followed by `>`, not a valid alternative
arrow. The scanner/parser never retries another grammar or chooses a backend
based on the input.

The sized entry retains its limit of 10,000 non-EOF tokens and block-comment
depth 64. Comments and EOF do not consume the token allowance; the next excess
token is rejected before allocating its owned text. The finite entry retains
its existing iterative comment processing without a newly imposed depth limit.
Source-byte and aggregate project limits remain separate entry-point policies.
The common parser applies its 64-level recursive syntax and runtime/type tree
bounds, 64-field tuple bound and 128-depth natural-expression bound. This counts
the quantum wrapper and its basis parse in the same recursion budget; certain
deep sized natural types therefore reach the common limit one level earlier
than the removed parser. These are engineering limits, not the constitutional
quantitative Resource Safety theorem.

All declarations remain in the common AST and undergo the original-source
judgment before either concrete profile. Source-semantic errors therefore
precede an unsupported concrete form, including in unused declarations. Empty
parentheses in a type position reject with a diagnostic directing the author
to `Unit`; the value and pattern remain `()`. Existing empty pattern/block,
empty `yield`, empty specialization brackets and parameter trailing-comma
spellings remain represented by the shared syntax. Parsing or source checking
adds no emitter support or new `Op<A,B>` form.

The common judgment has a 1,000,000-work engineering budget. It charges visits,
allocated/copied type and lexical cells, normalized arithmetic and solver work
before the corresponding operation. Per-value type size is bounded by 4096
cells and depth 64. The same judgment takes an additional 16,384 retained-scope
cell limit on the selected path; finite retains its existing aggregate/type
and snapshot capacities without that extra selected limit. Concrete
elaboration, evidence, native work and loader/parser limits are separate.
Exhaustion rejects; it is not a discharged quantitative Resource Safety
certificate or evidence that the program's mathematical obligation is false.

Ordinary and classical function parameters use the existing name, wildcard and
tuple pattern syntax. The colon annotates the entire parameter pattern, and
the source argument list keeps that parameter as one argument. For example,
`unitary fn first((a, _): (Bit, Bit)) -> Bit { a }` takes one ordinary pair.
Pattern checking preserves exact arity and nesting, rejects duplicate parameter
names and checks quantum ownership even in unused declarations. Tuple patterns
do not implicitly split a quantum register. Argument expressions retain their
evaluation order and effects before callee binding; a wildcard or Unit pattern
does not erase the computation that produced its argument.

## Declaration resolution and current profiles

Unqualified calls resolve lexical runtime/static bindings first, then ordinary
same-module declarations or explicit imports, then the six derived names in
the [ordinary prelude](prelude.md), and only then a language primitive when the
spelling is genuinely unbound. A moved binding, wrong callable category
or failed ordinary type/effect/access check remains the selected use and error;
there is no fallback. The canonical primitive identities and complete migration
of the 27 retired qualified entries are in the
[primitive boundary](primitive-boundary.md#bare-lookup-and-ordinary-shadowing).
Primitives require no import or prelude and their names are not reserved.
Qualified foundation paths and hidden aliases are unavailable. Ordinary stdlib
imports retain visibility, public effects and source/body obligations.

An imported declaration retains its canonical module and declaration name.
Visibility is checked before use: a private declaration cannot be imported from
another module or selected as a host entry. A sized host-supplied provider is
checked from the entry module's context, including when the provider is unused.
Imports add no runtime action or verification privilege. A moved local binding
continues to shadow a declaration with the same name; failed local lookup does
not fall back to that declaration. Evidence retains the original source,
dependencies, canonical names and static bindings.

Both paths resolve imports against the complete registered declaration tables.
Unused import-only cycles are permitted because imports have no runtime action.
Every self-import is a declaration-name collision, including a private or
public declaration imported into its own module. Duplicate imports and clashes
with local declarations reject. Missing members, private members, collisions
and retired foundation entries point to the final path token; a missing module
points to the complete `use` span.

Same-module sibling calls may refer forward or backward and may use private
declarations. Cross-module imports and host-selected entries require public
visibility. Runtime calls, static providers, classical and Meaning dependencies
from every original body enter the checked graph. Mutual cycles reject. Only
an actual runtime self-call to the identical DefId with the checked Nat decrease
is permitted, including its directly transformed runtime form; a recursive
opaque provider, classical/Meaning cycle or failed decrease does not qualify.
Finite may subsequently refuse to materialize such a source definition under
its concrete profile. Names, effect fixed points and zero-count repetition
cannot stand for the required decrease proof.

Runtime parameter, let and fold-carry bindings cannot shadow an active static
Nat, Basis, Op or fold-index binder. Static formals may shadow global
declarations. A consumed quantum owner may be rebound after complete RHS
evaluation; hiding a live owner rejects, including a zero-axis owner or one
nested in a product. A static name used as a runtime value is a located type
error; reusing an actually consumed runtime owner remains an ownership error.
A resolved local value used as a callee is a wrong-category error, never a
retry through a same-named global declaration.

`src/frontend/resolve.rs` and `resolve/locals.rs` retain canonical declaration,
lexical-use and original-span associations. The common typed primitive catalog
has 13 bare typed identities; finite and selected concrete emitters retain
their profile-specific adapters. The eight ordinary bundled modules undergo the same common
judgment as caller source. Transparent `pub use`, root-qualified references and
the explicit prelude opt-out follow the [prelude/import contract](prelude.md).
There is no ambient standard-library discovery or replacement of reserved `std`
modules; `as`, glob and relative imports remain unsupported.
Source facts, concrete capability and independent native acceptance remain
separate responsibilities. Remaining lowering integration is tracked in
[#32](https://github.com/MGYamada/Qleisli/issues/32); the current prelude/import
integration and its conformance evidence are tracked in
[#58](https://github.com/MGYamada/Qleisli/issues/58).

## Migration and evidence

The old sized scanner skipped bare CR/form feed and forbidden characters inside
comments. Those inputs now reject. Replace noncanonical whitespace with ordinary
space/tab or LF/CRLF and remove forbidden controls. VT already rejected before
this change; its diagnostic now comes from the shared character rule.

Remove legacy self-imports and use the module's declaration directly; ordinary
import-only cycles now need no source repair. Rename runtime binders that shadow
active static names. Earlier profile refusal may now be preceded by the actual
source type, owner, access or dependency error. Both paths charge all original
bodies and bundled sources, so an old symbolic input may reach the common work
capacity before an inner solver limit. Earlier sources and diagnostics remain
historical records; these migrations do not change edition 2026.

Reserved-word identifiers in old sized source must be renamed. Misplaced docs
must move to their module/declaration attachment boundary. Unclosed block
comments now use the common `unterminated block comment` diagnostic. The former
one-function restriction is removed: supported ordinary siblings share one
module, while mutual recursion remains rejected. Edition remains 2026 because
edition names the constitutional regime, while release compatibility records
these source changes.

`tests/fixtures/frontend_v030/shared-scanner/` in the
[repository](https://github.com/MGYamada/Qleisli) preserves the original byte
fixtures and actual old/new CLI diagnostics. The two successful small source
pairs emitted identical untrusted proposal hashes. The subsequent
`tests/fixtures/frontend_v030/common-parser/` packet preserves ten initial
source observations, independent review counterexamples, exact commands/results
and four small before/after proposals with identical bytes. It also records the
shared-depth edge above. These are bounded migration evidence, not a general
source-preservation proof, new formal guarantee or native acceptance claim.

`tests/fixtures/frontend_v030/shared-resolution/` retains the resolver's ten
original profile observations, 25 matching command results and five identical
small proposals, including distinct same-named providers and decreasing
self-recursion. Private Rust debug representations are not canonical names or
evidence formats; their printed fields change with the internal resolver.

`tests/fixtures/frontend_v030/lexical-resolution/` retains the subsequent shared
local/static binding comparisons. The `multi-declaration/` and
`sized-declarations-independent/` packets preserve original rejected siblings,
their declared acceptance/diagnostic changes, and independent small phase/axis
comparisons of split-module and same-module programs. Earlier failed sources
and results remain historical evidence. Existing single-declaration observations
and six small proposal byte sequences are unchanged by the sibling extension;
newly accepted source still undergoes its actual native check.

Both current finite `with_computed` forms now require the
[explicit predicate domain](type-model.md#predicate-domains-and-argument-lists).
Replace a legacy `p(a: A, b: B)` predicate with `p((a,b): (A,B))` for a
`Q<(A,B)>` register. For three or more parameters, write the register's exact
tree; the old fold was left-associated. A `Q<Unit>` predicate takes an explicit
Unit parameter. Ordinary calls retain their argument-list arity, so update any
ordinary callers or provide a separate unary wrapper. The
`tests/fixtures/frontend_v030/predicate-domain/` and
`predicate-domain-independent/` packets retain old diagnostics, explicit current
translations, small proposal comparisons and independent phase/reference
checks. Source-bearing artifact identities change when embedded source changes.

The former `do p <- q; pure e` expression is removed. Its explicit migration is
`basis q as p { e }`, preserving the input expression, complete pattern and
single basis expression. The braces delimit the restricted basis-expression
grammar, not an ordinary statement block. The migration does not join separate
owners, allow outer runtime captures, remove injectivity checking or prepare a
state. [Coherent basis maps](coherent-basis.md) specifies the semantics,
diagnostics and concrete-profile limits. Both finite and selected source use
this one parser; a profile cannot retain the retired notation as an alias.

Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0.
