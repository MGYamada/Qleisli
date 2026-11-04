import QleisliKernel.SourceTypes.SourceRuntimeTrace
import QleisliKernel.Qirf

/-! Reuse of exact original setup does not reuse closed body results. Fresh
and prepared traversals retain different actual run witnesses. Even a
well-typed same-signature canonical summary with stale use/effect/owner data
must fail the independent named-body replay. No native result is supplied.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceRuntimeSetup
open QleisliKernel Finite SourceTypes
open QleisliKernel.SourceTypes.SourceRuntimeValues (valueOwners owners typeOf ordinary transport)

private def work := Qirf.WorkProfile.qmatch.limit

private def source : String := "#![no_implicit_prelude]\nunitary fn once(q:Q<Bit>)->Q<Bit>{h(q)}pub unitary fn route(q:Q<Bit>)->Q<Bit>{once(q)}"
private def publicSource := source.replace "unitary fn once" "pub observe fn once"
private def pairSource : String := "#![no_implicit_prelude]\nunitary fn once(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){(h(a),b)}pub unitary fn route(a:Q<Bit>,b:Q<Bit>)->(Q<Bit>,Q<Bit>){once(a,b)}"

private def origins : WorkM (Bool × Bool × List Nat × Nat) := do
  let signature ← SourceRuntimeContext.readSignature #[ ("main",source) ] "main" "route" {}
  let caller ← SourceRuntimeTrace.readBodyWithSignature signature
  let fresh := match caller.checked.traversed with | .fresh _ => true | .prepared .. => false
  let [.named event] := caller.checked.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody event
  let prepared := match callee.checked.traversed with | .fresh _ => false | .prepared .. => true
  return (fresh,prepared,(valueOwners callee.checked.summary.value).map (·.ordinal),callee.checked.events.length)

#guard origins.run work |>.1.toOption == some (true,true,[0],1)

private def staleUse : WorkM Unit := do
  let signature ← SourceRuntimeContext.readSignature #[ ("main",source) ] "main" "route" {}
  let caller ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.named event] := caller.checked.events | throw .request
  if annotated : event.target.signature.original.parsedHeader.effect.isSome = true then
    let canonical : SourceRuntimeContext.Summary event.target.signature :=
      {event.canonical with quantumUse := !event.canonical.quantumUse, publicQuantum := by intro _ _; exact annotated}
    let stale : SourceRuntimeContext.NamedEvent _ _ := {event with canonical := canonical}
    let _ ← SourceRuntimeTrace.readNamedBody stale
    return ()
  else throw .invalid

#guard (staleUse.run work).1 matches .error .request

private def staleEffect : WorkM Unit := do
  let signature ← SourceRuntimeContext.readSignature #[ ("main",publicSource) ] "main" "route" {}
  let caller ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.named event] := caller.checked.events | throw .request
  if allowed : SourceEffect.permits event.target.signature.original.parsedHeader.effect .observe = true then
    let canonical : SourceRuntimeContext.Summary event.target.signature :=
      {event.canonical with inferredEffect := .observe, asserted := allowed}
    let stale : SourceRuntimeContext.NamedEvent _ _ := {event with canonical := canonical}
    let _ ← SourceRuntimeTrace.readNamedBody stale
    return ()
  else throw .invalid

-- A conservative same-module public annotation is still retained. The body
-- replay independently infers Unit and refuses the poisoned closed effect.
#guard (staleEffect.run work).1 matches .error .request

private def staleOwners : WorkM Unit := do
  let signature ← SourceRuntimeContext.readSignature #[ ("main",pairSource) ] "main" "route" {}
  let caller ← SourceRuntimeTrace.readBodyWithSignature signature
  let [.named event] := caller.checked.events | throw .request
  let [.tuple 2,.owner first,.owner second] := event.canonical.value | throw .invalid
  let swapped : QleisliKernel.SourceTypes.SourceRuntimeValues.Value := [.tuple 2,.owner second,.owner first]
  if balanced : (owners event.canonical.initial ++ event.canonical.allocated).Perm
      (valueOwners swapped ++ event.canonical.consumed) then
    if typed : typeOf swapped = event.target.signature.result.tree then
      let canonical : SourceRuntimeContext.Summary event.target.signature :=
        {event.canonical with value := swapped, balanced := balanced, typed := typed}
      match transported : transport ⟨"main",event.target.callerName,event.call.calleeOffset⟩
          event.ownerMap (event.arguments.flatMap ordinary) swapped with
      | .error _ => throw .invalid
      | .ok value =>
        let stale : SourceRuntimeContext.NamedEvent _ _ :=
          {event with canonical := canonical, value := value, transported := transported}
        let _ ← SourceRuntimeTrace.readNamedBody stale
        return ()
    else throw .invalid
  else throw .invalid

-- Equal-width owners and a correctly transported, balanced stale summary do
-- not replace the owner result computed again from the actual original body.
#guard (staleOwners.run work).1 matches .error .request

/-- A retained catalogue rechecks the actual generic tree. Relevance and
effect agree with cold discovery, including for a conservatively annotated
static declaration. An unrelated module contributes no source row. -/
private def retainedGeneric : WorkM Bool := do
  let modules := #[("main","#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q} pub observe fn route[const N:Nat](q:Q<Bit>)->Q<Bit>{keep(q)}"),
    ("unrelated","#![no_implicit_prelude]\nunitary fn idle(q:Q<Bit>)->Q<Bit>{q}")]
  let catalogue ← GenericCatalogue.read modules
  let signature ← SourceRuntimeContext.readSignature modules "main" "route" ⟨[],[("N",1)],[]⟩ .external (some catalogue)
  let tokens := signature.original.occurrence.body
  let tree ← lift ((SourceSyntax.read (tokens.length+1) 0 true tokens).mapError fun _ => Error.request)
  let cold ← GenericTypeTrace.readWithTree signature.instantiation tree
    (some catalogue.modulesContext) (some catalogue.meaningsContext)
  let observed ← RuntimeGenericAnalysis.read signature.instantiation tree (some catalogue)
  let .retained .. := observed | throw .invalid
  let oldRows ← SourceTrace.retainStaticRows cold.sourceRows
  let newRows ← SourceTrace.retainStaticRows observed.sourceRows
  return observed.inferredEffect == cold.inferredEffect && observed.quantumUse == cold.quantumUse &&
    observed.outcome.references == cold.root.outcome.references && oldRows == newRows &&
    newRows.map Prod.fst == ["main"]

#guard (retainedGeneric.run work).1.toOption == some true

example {sources owner name} (fuel : Nat) (active : List SourceCallStack.Frame)
    (signature : SourceRuntimeContext.Signature sources owner name) :
    SourceRuntimeTrace.readNested sources fuel active signature =
      SourceRuntimeTrace.readNestedWithSetup sources fuel active signature none := rfl

end QleisliKernel.Tests.SourceRuntimeSetup
