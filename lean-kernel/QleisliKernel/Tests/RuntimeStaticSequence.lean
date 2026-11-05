import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyDiscovery
import QleisliKernel.Qirf.RuntimeBodyGraph

/-! Selected original primitives share the authentic enclosing event step.
The frozen one-qubit source keeps a distinct zero-width spectator. These
component controls do not admit a wire/handle or all equivalent decompositions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticSequence
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\n" ++
  "pub unitary fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Q<Bit>,Q<Unit>){\n" ++
  "    let q=if static n==0{q}else{let q=phase[1,1](q);h(q)};\n    (q,u)\n}\n"

private abbrev SelectedIndex := Nat × Nat × Nat × Nat × Nat × Nat

/-- Project the source and position at each stored ordinal in the actual
returned receipt. The outer position names the static expression; its body
supplies the independent inner source index and native slice. -/
private def selectedIndex {dependencies program block} :
    RuntimePureBody.Node dependencies program block → Option SelectedIndex
  | .primitive _ written => do
    let location ← written.location
    let .selected source outerPositions outer body _ positions _ inner := location.origin | none
    let parent ← source.events[outer.ordinal]?
    let parentPosition ← outerPositions[outer.ordinal]?
    let event ← body.result.events[inner.ordinal]?
    let position ← positions[inner.ordinal]?
    if parent.offset == parentPosition.offset && position == location.position &&
        event.offset == written.event.offset && event.offset == position.offset then
      return (outer.ordinal,parent.offset,inner.ordinal,event.offset,position.start,position.count)
    else none
  | _ => none

private def actual (n exponent : Nat) (wrongOrder wrongOwner single : Bool) :
    WorkM (List Nat × List Nat × List Nat × Nat) := do
  let text := if single then source.replace "let q=phase[1,1](q);h(q)" "phase[1,1](q)" else source
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let z : Semantics.Raw.Op := .applyUnitary (if wrongOwner then 0 else 1) 2
    [if wrongOwner then ⟨[],.monomial [] [0] [exponent]⟩ else ⟨[],.monomial [0] [0,1] [0,exponent]⟩]
  let operations : List Semantics.Observation.Op := if n == 0 then [] else if single then
    [.pure z,.pure (.applyUnitary 2 3 [⟨[],.monomial [0] [0,1] [0,0]⟩])] else if wrongOrder then
    [.pure (.gate .h 1 2),.pure (.applyUnitary 2 3 [⟨[],.monomial [0] [0,1] [0,exponent]⟩])] else
    [.pure z,.pure (.gate .h (if wrongOwner then 1 else 2) 3)]
  let outputs := if n == 0 then [1,0] else if wrongOwner then [3,2] else [3,0]
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],operations,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let tokens ← lift ((lexLocated text).mapError fun _ => Error.request)
  let some keyword := tokens.find? (·.text == "if") | throw .request
  let context : RuntimeContextRequest.Context := .mk [⟨keyword.span.startByte,0,operations.length⟩] [] [] [] []
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {naturals := [("n",n)]} context
  let fresh ← RuntimeBodyDiscovery.prepare #[0] headers
  let body := headers.source.body
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs body prepared
    [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨bit,[.bit]⟩]]
  let checked ← RuntimePureBody.checkPrepared artifact fresh.root body fresh.root.program context inputs.owners.bindings prepared
  let expectedIndices : List SelectedIndex :=
    if n == 0 then [] else if single then [(0,107,0,129,0,2)]
    else [(0,107,0,135,0,1),(0,107,1,149,1,1)]
  guard (checked.result.actions.mapM selectedIndex == some expectedIndices) .invalid
  return (checked.result.history.issued.map (·.ordinal),checked.result.bindings.map (·.owner.ordinal),
    checked.result.bindings.map (·.port.token),checked.result.actions.length)

#guard (actual 0 4 false false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[1,0],0)
#guard (actual 1 4 false false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[3,0],2)

-- Local exact equations, not an overall instruction count or phase label,
-- reject a wrong phase, reversed noncommuting order and a changed spectator.
#guard (match (actual 1 0 false false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 4 true false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 4 false true false).run 10000000 with | (.error _,_) => true | _ => false)

-- A single source event still accepts its previously supported multi-op
-- literal interval. The new compound eligibility does not narrow that route.
#guard (actual 1 4 false false true).run 10000000 |>.1.toOption == some ([0,1],[1,0],[3,0],1)

private def ordinaryPrefix : WorkM (List Nat × List Nat × Nat) := do
  let text := "#![no_implicit_prelude]\n" ++
    "pub unitary fn route[const n:Nat](c:Bit,u:Q<Unit>,q:Q<Bit>)->(Bit,Q<Bit>,Q<Unit>){" ++
    "let d=not c;let q=if static n==0{q}else{let q=phase[1,1](q);h(q)};(d,q,u)}"
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let program : Semantics.Observation.Program := ⟨[unit,bit],[5],
    [.not 5 6,.pure (.applyUnitary 1 2 [⟨[],.monomial [0] [0,1] [0,4]⟩]),.pure (.gate .h 2 3)],
    [3,0],[6],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let arguments : StaticTypes.Arguments := {naturals := [("n",1)]}
  let signature ← SourceRuntimeContext.readSignature artifact.sources "main" "route" arguments
  let tokens ← lift ((lexLocated text).mapError fun _ => Error.request)
  let some keyword := tokens.find? (·.text == "if") | throw .request
  let context : RuntimeContextRequest.Context := .mk [⟨keyword.span.startByte,1,2⟩] [] [] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",signature.parameters.map (·.tree),
      [[.ordinary [.bit] (.bit 5)],[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨bit,[.bit]⟩]],
      [[false],[true]],signature.result.tree,
      [.tuple 3,.ordinary [.bit] (.bit 6),.quantum ⟨⟨3,[0],1⟩,[.bit]⟩,.quantum ⟨unit,[.unit]⟩],.unitary,arguments⟩
  let checked ← RuntimeBodyGraph.prepareRuntime artifact #[0] "main" "route" arguments context runtime
  return (checked.derivation.result.ordinary.table.map Prod.fst,
    checked.derivation.result.bindings.map (·.port.token),checked.derivation.result.steps.length)

-- The shared gap advancement consumes the real classical prefix once, and
-- the existing all-input final storage gate checks the same resulting SSA.
#guard ordinaryPrefix.run 10000000 |>.1.toOption == some ([5,6],[3,0],3)

end QleisliKernel.Tests.RuntimeStaticSequence
