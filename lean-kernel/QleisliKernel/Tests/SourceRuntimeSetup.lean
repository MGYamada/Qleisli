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
  let fresh := match caller.checked.traversed with | .fresh _ => true | _ => false
  let [.named event] := caller.checked.events | throw .request
  let callee ← SourceRuntimeTrace.readNamedBody event
  let prepared := match callee.checked.traversed with | .prepared .. => true | _ => false
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
  let modules := #[("main",pairSource)]
  let catalogue ← GenericCatalogue.read modules
  let signature ← SourceRuntimeContext.readSignature modules "main" "route" {} .external (some catalogue)
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

/-- Both catalogue paths agree with cold discovery for a conservatively
annotated declaration. The exact parser receipt permits cheaper generic
reuse, preserving the same ordered rows before deduplication. -/
private def retainedGeneric : WorkM Bool := do
  let modules := #[("main","#![no_implicit_prelude]\nunitary fn keep(q:Q<Bit>)->Q<Bit>{q} pub observe fn route[const N:Nat](q:Q<Bit>)->Q<Bit>{keep(q)}"),
    ("unrelated","#![no_implicit_prelude]\nunitary fn idle(q:Q<Bit>)->Q<Bit>{q}")]
  let catalogue ← GenericCatalogue.read modules
  let signature ← SourceRuntimeContext.readSignature modules "main" "route" ⟨[],[("N",1)],[]⟩ .external (some catalogue)
  let tokens := signature.original.occurrence.body
  match parsed : SourceSyntax.read (tokens.length+1) 0 true tokens with
  | .error _ => throw .request
  | .ok tree =>
    let cold ← GenericTypeTrace.readWithTree signature.instantiation tree
      (some catalogue.modulesContext) (some catalogue.meaningsContext)
    let (.ok replayed,replayLeft) :=
      (RuntimeGenericAnalysis.read signature.instantiation tree (some catalogue)).run work | throw .invalid
    let (.ok observed,reuseLeft) :=
      (RuntimeGenericAnalysis.readParsed signature.instantiation tree parsed (some catalogue)).run work | throw .invalid
    let .retained .. := replayed | throw .invalid
    let .catalogued .. := observed | throw .invalid
    let oldRows ← SourceTrace.retainStaticRows cold.sourceRows
    let newRows ← SourceTrace.retainStaticRows observed.sourceRows
    return reuseLeft > replayLeft && observed.inferredEffect == cold.inferredEffect &&
      observed.quantumUse == cold.quantumUse && observed.outcome.references == cold.root.outcome.references &&
      observed.sourceRows == replayed.sourceRows && oldRows == newRows && newRows.map Prod.fst == ["main"]

#guard (retainedGeneric.run work).1.toOption == some true

example {sources owner name} (fuel : Nat) (active : List SourceCallStack.Frame)
    (signature : SourceRuntimeContext.Signature sources owner name) :
    SourceRuntimeTrace.readNested sources fuel active signature =
      SourceRuntimeTrace.readNestedWithSetup sources fuel active signature none := rfl

open SourceRuntimeContext SourceRuntimeContext.RuntimeCalleeTrace

private def foldSource : Sources := #[
  ("main", "#![no_implicit_prelude]\nunitary fn leaf(q:Q<Bit>)->Q<Bit>{h(q)}" ++
    "unitary fn flip(q:Q<Bit>)->Q<Bit>{adjoint(leaf)(q)}" ++
    "pub unitary fn route[const n:Nat](q:Q<Bits<n>>)->Q<Bits<n>>{" ++
    "qfor static i in 0..n carry r=q{let(bit,tail)=take_bit[n,i](r);" ++
    "yield put_bit[n,i](flip(flip(bit)),tail);}}")]

private def forwardH {owner : String} {events : List (Event foldSource owner)}
    (trace : Sequence foldSource owner events) : Bool :=
  match trace with
  | .cons (.transform transformation leaf _ _) (.nil _) =>
    match leaf.events with
    | [.primitive primitive] => primitive.kind == .h && transformation.written.access == .adjoint
    | _ => false
  | _ => false

private def foldedIteration {events : List (Event foldSource "main")}
    (trace : Sequence foldSource "main" events) : Option (List Nat × List Nat × List Nat) := do
  let .cons (.local (.registerPrimitive take))
      (.cons (.named first _ _ firstChild)
        (.cons (.named second _ _ secondChild)
          (.cons (.local (.registerPrimitive put)) (.nil _)))) := trace | none
  if !(forwardH firstChild && forwardH secondChild) then none
  else some (take.application.arguments.map (·.value), put.application.arguments.map (·.value),
    [first.call.calleeOffset,second.call.calleeOffset])

private def checkFold {events : List (Event foldSource "main")}
    (trace : Sequence foldSource "main" events) : Option Bool := do
  let .cons (.fold fold _ (.cons first (.cons second (.nil _)))) (.nil _) := trace | none
  let (firstTake,firstPut,firstCalls) ← foldedIteration first
  let (secondTake,secondPut,secondCalls) ← foldedIteration second
  return fold.iterations.map (·.coordinate) == [0,1] && firstTake == [2,0] && firstPut == [2,0] &&
    secondTake == [2,1] && secondPut == [2,1] && firstCalls == secondCalls && firstCalls[0]? != firstCalls[1]?

private def checkFoldTrace : WorkM (Option Bool) := do
  let signature ← SourceRuntimeContext.readSignature foldSource "main" "route" {naturals := [("n",2)]}
  let checked ← SourceRuntimeTrace.readNestedTraced foldSource (SourceTrace.sourceFuel foldSource) [] signature none
  return checkFold checked.sequence

#guard (checkFoldTrace.run work).1.toOption == some (some true)

private def checkRetained : WorkM Bool := do
  let signature ← SourceRuntimeContext.readSignature foldSource "main" "route" {naturals := [("n",2)]}
  let original ← SourceRuntimeTrace.readBodyWithSignature signature
  let observed : Option (Event foldSource "main") := original.checked.events[0]?
  match head : observed with
  | some (Event.staticFold event iterations) =>
    let parent : Path original.checked.events (.staticFold event iterations) := .direct 0 head
    let firstEvent : Option (Event foldSource "main") := iterations.flatten[1]?
    let secondEvent : Option (Event foldSource "main") := iterations.flatten[5]?
    match first : firstEvent, second : secondEvent with
    | some (Event.named firstCall),some (Event.named secondCall) =>
      let before ← SourceRuntimeTrace.readRetainedNamed original.checked (.folded parent 1 first)
      let after ← SourceRuntimeTrace.readRetainedNamed original.checked (.folded parent 5 second)
      let fresh ← SourceRuntimeTrace.readNamedBody firstCall
      return firstCall.call.calleeOffset == secondCall.call.calleeOffset &&
        before.checked.summary.value == fresh.checked.summary.value &&
        forwardH before.checked.traced.sequence && forwardH after.checked.traced.sequence
    | _,_ => return false
  | _ => return false

#guard (checkRetained.run work).1.toOption == some true


end QleisliKernel.Tests.SourceRuntimeSetup
