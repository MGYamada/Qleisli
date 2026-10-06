# Public source routes and concrete eligibility

This is a non-normative read-only supplement to `../audit-01`, not an adopted
solution. It prepares one ordinary before-code #32/#317 contract. No compiler,
test, CLI, native process, fixture driver, metadata command, Git or GitHub action
was executed. No production source, existing fixture, stdlib or documentation
was changed. `inputs.json` binds the selected files read here; it is not a whole
build/runtime attestation. The earlier constitutional continuity check in this
same running review passed against `faa5cfb5e7ea1cf3b39a43b80f7f2345e89197c2`.
This audit admits no interpretation, guarantee or proof and earns no Issue
completion credit. I authored the finite consumer and parts of selected runtime
group support; this is a source-route audit, not independent validation of my
implementation or of the earlier QFT oracle. The existing audit's 55-caller
migration inventory is retained rather than copied into another backlog.

## The two real public routes

| Route | Actual consumer | Original-source judgment | Concrete scope |
| --- | --- | --- | --- |
| Public directory `check_project` / `compile_project`, diagnostic/policy/kernel variants; ordinary CLI `check`, `run`, `sample` | `compile/mod.rs::process_loaded_project_details` | Fresh `check::program_with` over every current `Project` original AST | Every declaration must pass the finite profile. All Basis/Meaning declarations are concretely constructed in dependency order. Every runtime declaration without static parameters is lowered and natively checked, including private/unused/bundled declarations. Static Op instances are constructed on actual calls. |
| Public `QrateSource::{check_with_kernel,compile_with_kernel,check_with_policy,compile_with_policy}`; ordinary CLI `--qrate` | Held directory identity → the same finite consumer | The same complete judgment | The same finite concrete duties; qrate selection does not select a sized target. |
| Selected module map `ParsedProgram::{parse,load}` → `instantiate_with_types` → `elaborate`; CLI selected flags | `sized.rs`, `sized/check.rs`, `sized/elaborate.rs`, `source_plan.rs::prepare` | Complete judgment of all supplied originals plus all four bundles, before temporary projection | A projection `Result` is retained by DefId for every declaration. Unsupported projections reject when requested by entry/provider/dependency materialization; projection limit errors reject preparation globally. Native checking covers the chosen specialization, not all unused bundled specializations. |

Both loaders add the exact four ordinary `BundledRegistry` sources and fixed
manifest. No name grants permission to substitute a body or skip checking.
Public finite `Project` fields remain mutable; the fresh common judgment must
continue to reconstruct facts from their current ASTs on each operation.

The concrete finite loop is important: `compile/mod.rs:716` applies
`profile::check` to **all** declarations after common judgment, before that
function selects/clones its kernel. Its later `:803` loop lowers every closed
runtime definition. `compile/lower/mod.rs::lower_function_inner` builds its real
body/signature/owner frame and calls `accept_raw_with_budget` (`:1444`). This is
an actual native verification duty, not a source flag. The ordinary CLI creates
a kernel configuration earlier in `source_commands.rs::execute`; that difference
does not remove the all-declaration finite profile refusal.

`project/manifest.rs::QrateSource::select` holds the selected directory identity.
`load_with_policy` checks replacement before and after `Project::load_anchored`;
on Unix reads/discovery remain relative to that held root. It does not promise a
filesystem-content snapshot. A future discovered-source bridge must not replace
this with path re-canonicalization or an invented immutable-file guarantee.

## Exact CLI selection, not a nonexistent plan function

There is no current `build_execution_plan` function. The actual selected plan
function is `src/bin/qleisli/source_plan.rs::prepare` (`:245`). Main dispatches
to this route before parsing ordinary directory/qrate options.

`source_plan/options.rs::selected` treats `--ir-profile=auto|raw|hierarchy` as a
selected-form flag, even when the rest of the input is incomplete. `parse`
requires exactly **one positional command**, a nonempty explicit `--entry`, and
a nonempty explicit `--module=name=PATH` map. It has no `--qrate` branch or
directory-source positional operand. Thus these are source-read predictions,
not newly executed CLI observations:

- `qleisli check DIRECTORY --ir-profile=auto` reaches selected parsing and fails
  usage: it has an extra positional argument and no entry/module map.
- Adding `--ir-profile=auto` to the ordinary qrate form still fails selected
  parsing; `--qrate` is unknown there. It does not discover that qrate's modules.
- `qleisli check --ir-profile=auto` also fails without entry/modules.
- A complete selected invocation must supply `--entry=module::function` and
  `--module=...`, with any required explicit Nat/Basis/Op bindings. `finite` is
  not a valid `--ir-profile` value; finite public APIs and selected Raw transport
  are different routes.

`prepare` loads the explicit collection, closes bindings and elaborates actual
entry/callees **before** target choice. Auto asks `hierarchy_eligibility` about
the elaborated root/steps; only an explicit profile mismatch selects Raw.
Other failures propagate. Full Raw/hierarchy capability checks still run, and
a lowerer failure is final. An independent request forces hierarchy, never a
request-free retry. `emit-proposal` remains untrusted and performs no native
check; the executing/checking paths must perform their actual native gate.

## Why embedding generic QFT alone breaks finite projects

`compile/profile.rs` rejects a static Nat formal, Bits types, size premises,
static conditions/folds and symbolic specializations. Putting the canonical
generic QFT body into a registry source therefore makes **every finite project**
refuse that unused declaration after complete common checking. An unused import
is not required to trigger this; the bundle is already part of the collection.

Removing that single profile refusal would not implement generic execution.
Finite operation arguments reject Natural/Type/Specialize forms in
`compile/lower/operations.rs::operation`; finite static binding handles actual
Op providers and still checks exact basis, Meaning and required access, including
unused supplied providers. Finite lowering has no general Nat/Bits/register
materializer. Opaque/static/host providers remain exactly unary `Q<A>`; runtime
owner groups do not implicitly pack into that owner.

The selected route has the conditional symbolic interfaces and actual Nat
specialization path: `sized/check.rs::instantiate` validates all closed bindings
before requested projection eligibility, then Builder's `function_inner` and
`arguments_inner` consume actual DefId/static kinds and build concrete calls.
An unsupported entry, specified provider or called dependency fails at its
original location. Unrequested projection results do not grant source approval
or native certification; approval comes only from the mandatory common judgment.
Selected `raw.rs::{supported,check_profile}` refuses Bits and Q bases other than Bit, including
`Q<Bits<0>>`. Generic QFT cannot become selected Raw by renaming its register or
flattening its owner. Hierarchy can carry quantum register interfaces, but real
step, phase, evidence, root-effect, port and capacity checks remain mandatory.

The retained local candidate is
`authoring_sessions/qft-family-v030/attempt-01/transform.qli`, not an embedded
canonical std API. Its body uses ordinary static stages, H, positive dyadic
controlled phases, register extraction/insertion and included reversal. Its
contract is `exp(+2πixy/2^N)/sqrt(2^N)`, axis0 least significant. N=0 returns the
same single `Q<Bits<0>>` owner with scalar +1; it is not zero owners or `Q<Unit>`.
The earlier bounded N=0..3 numerical/exact-request packets retain their original
source and gate scopes. This review did not replay the candidate through the
current checker and makes no new success claim. Current concrete register/Basis
width and dyadic phase domains stop at 8; current work/call/type limits may stop
instances earlier. A source family for arbitrary Nat does not make all its
specializations materializable, prove the family equation, or supply source
preservation. No rounding, Fourier name match, owner-label waiver or new
primitive is justified by this audit.

## Decisions required in one ordinary before-code contract

1. Specify the public discovered-directory/qrate input and entry/binding forms
   that actually reach the shared collection and selected materializer. Retain
   held qrate identity, original bytes/provenance, edition, visibility, collision
   and loader limits. An explicit module map alone does not cover this route.
2. Specify conditional generic declarations versus concrete obligations after
   complete common judgment. Unsupported unrequested generic materialization
   must not poison unrelated concrete entry use merely because it is bundled;
   **unused closed finite definitions must still undergo their current real
   native checks**, and requested unsupported instances must fail locatably.
   This is a required policy decision, not an implemented skip rule here.
3. Specify the finite public API boundary explicitly. `compile_project` returns
   ordinary native `AcceptedProgram`; a hierarchy proposal/handle is a different
   type and scope. Redirecting that implementation to the selected CLI planner
   does not preserve the Rust contract by itself. Raw is also not a synonym for
   the existing finite project API.
4. Preserve all actual specialized interface/type/owner/effect/access/evidence
   gates and independent native checks. Neither a source-check success nor an
   eligible projection may become an accepted executable handle or discharge a
   pending Meaning, clean, injectivity, provider or preservation obligation.
5. Before implementation, freeze small source controls for unrelated main plus
   unused valid generic, invalid unused/dead generic body, unused closed finite
   negative, and actual canonical calls at N=0..3. Compare both directory/qrate
   and explicit-map paths, exact tuple/register owner shape, phase and axes,
   requests and materialization refusals. These are proposed bounded controls,
   not executed results or permission to generate maximum-size cases.

QS/PR/quantitative RS and EXACT proof/enforcement remain pending. Existing scoped
ordinary QLV1 guarantees, native modes/matchers, edition 2026 and all first
sources/licenses stay unchanged. The next contract must connect source selection
and materialization; neither this note nor a namespace migration completes #32,
#317, general acceptance, family proofs, constitutional adoption or release CI.
