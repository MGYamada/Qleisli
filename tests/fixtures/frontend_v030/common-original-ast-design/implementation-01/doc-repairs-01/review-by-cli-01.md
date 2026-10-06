# Documentation review by the common-checker author

This is an additive read-only review of the original four-target documentation
proposal and its first CHANGELOG clarification. I authored the common checker;
I did not author these documentation patches. This is separate document/code
comparison, not independent validation of my own checker or a replacement for
the root/adapter implementation reviews. No test, Cargo, CLI, native, recorded
driver, Git or network command was executed for this review. Only the required
constitutional identity/continuity guard was run; it passed against trusted
`faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`. It is not fresh Lean replay.
The two admitted scoped QLV1 guarantees remain protected. QS/PR/RS/EXACT's
broader proof/enforcement obligations remain pending; no adoption or discharge
is made here.

## Actionable finding

The added primitive-boundary paragraph still names
`sized/check.rs::primitive_signature` (proposed.patch line 305). That function
no longer exists. Current sized/check.rs consumes already checked interfaces
and performs closed substitutions; the common source primitive contracts live
in check/primitive.rs, the selected concrete subset in sized/primitive.rs, and
materialization in sized/elaborate.rs::primitive. Replace the obsolete function
reference in an additive clarification, preserving the first patch. This is a
stale implementation reference, not a source-rule or native-acceptance change.
The finding was sent to the root and documentation author before this note.

## Existing requested clarifications

The documentation author's two already identified corrections remain necessary:
constrain the later-kind sentence to ordered static formals, retaining ordinary
forward sibling calls; distinguish the selected loader's four reserved bundle
slots from finite bundle-byte/discovery accounting. I have not treated an
unwritten or unread clarification-02 as applied or checked. The first retained
CHANGELOG clarification accurately changes the overly broad static-shadow
wording to runtime bindings that shadow active static names.

For additional precision, the type-model sentence `Those keep one input
Q<A> -> Q<A>` can refer to the operation providers used by Meaning/certified/
FunctionEquality contracts. A declared Meaning is a Basis-level specification,
not itself a runtime quantum-owner function. The following apply_contract
paragraph already preserves the declared-Meaning specification route. This is
a clarity recommendation; I found no implementation widening from that route.

## Scope comparison

The mandatory original-AST judgment runs before each adapter's concrete
eligibility and before selected declaration projection. Current mutable Project
ASTs are rechecked; the selected route retains immutable originals and one
projection result per DefId. The common code visits private/unused definitions,
branch arms and zero-fold bodies, retains original lexical identities, derives
principal effects from bodies, then validates pending source associations before
its consumer callback. All four ordinary bundles are source inputs, not sealed
algorithm names. The proposed limits and source/concrete/native distinction do
not advertise every bundled specialization as natively accepted.

The direct-runtime clarification is reflected precisely: original ordinary
Name/Specialize/transparent Repeat targets use the complete nonempty quantum
owner tree, exact grouped interface, once-only input evaluation and checked
same-DefId Nat decrease. Local Op formals, primitives and other constructors
continue through the strict opaque-basis route. Current selected host/static
provider checks remain unary; runtime_provider_type is a distinct concrete
route. Conservative transparent-provider inverse access requires every actual
Op's Apply and Adjoint, and control also requires Controlled, including unused
arguments. The proposal does not grant access from an effect annotation.

RuntimeGroupProvider and FunctionEquality are retained located pending
associations, not transformation equality, matrix equality, injectivity,
all-input clean return, provider correspondence or source-preservation proofs.
The declared finite Meaning route and unsupported requested selected Meaning
projection remain distinct. No canonical generic std API, new primitive,
accepted-handle constructor, fallback, guarantee or Issue completion is claimed
by the inspected proposed prose. Subject to the concrete reference repair and
already requested clarifications above, I found no additional semantic widening
in these scopes. This review does not predict the ongoing final validation's
results or provide release approval.

## Inspected identities

These are selected inputs to this document comparison, not a complete compiled
source attestation. Each was hashed from current bytes and rechecked before and
after writing this new note. No existing proposal/map was rewritten.

| Input | SHA-256 |
| --- | --- |
| `tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/doc-repairs-01/proposed.patch` | `53578d2a13da45fd34ba7e85d1026aa025676a8c29c426e27b6e8538bf1996a1` |
| `tests/fixtures/frontend_v030/common-original-ast-design/implementation-01/doc-repairs-01/proposal-clarification/clarification.patch` | `bfc908ca3b1d4818126955fafc9e9a4d8c99e7f661177a6686f50479b6159a0f` |
| `tests/fixtures/frontend_v030/common-original-ast-design/runtime-group-clarification-01.md` | `b87f71d5d84f6082fd6d0ba3aac67a06378c2e6e2e9e1db21af914c0b535a1a1` |
| `src/frontend/check.rs` | `cbe9bf52967f7200181079ff9a11a6ec499cfd6f0445f822566553abeb05ae3d` |
| `src/frontend/check/body/operations.rs` | `17b25a718940954ce743ef92c662879197a22c43e55e20a6f119fbe5a47d9943` |
| `src/frontend/check/body/special.rs` | `d4c7acfe85e0f0eab22bee9497d8331df1ce43e94ddca71a49476eba31fb396d` |
| `src/frontend/check/primitive.rs` | `38caedf63ce840caccfabd94f522fef79f9e408c3eb139f22d5df25b3f195c11` |
| `src/frontend/compile/mod.rs` | `cc70a9c5a9fa5fe445cf7299c08f454dc624bec36a3f07561675075aa45e64bd` |
| `src/frontend/sized.rs` | `366007e2fe05a4877c9baf954b8034a95fdaa70857d644dbee6949d6758cbd99` |
| `src/frontend/sized/check.rs` | `be72b25e2000eca319d9b4fe554804270d0f297620ace9a29d961cfc2a85d000` |
| `src/frontend/sized/elaborate.rs` | `b65fe34f7bffabc03e07534f7665905378cb30ecf067cf43057c232acbba4490` |
| `src/frontend/sized/parser.rs` | `9bd9baffd118a4850c068df06e104a0077f32c8303d4b701c81f7e53e6ae754f` |
| `src/frontend/sized/primitive.rs` | `60456760d69d05a438456dd98baaa54de49a8b9f4edd111a7f22744c55f424e4` |
