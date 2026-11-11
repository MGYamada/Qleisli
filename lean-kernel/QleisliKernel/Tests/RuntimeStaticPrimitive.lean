import QleisliKernel.Qirf.RuntimePureBody
import QleisliKernel.Qirf.RuntimeBodyDiscovery

/-! The frozen one-qubit/static-phase experiment through the same common
body and discovery path. A separate Q<Unit> spectator keeps its logical role.
These controls grant no wire, handle, whole-static-body or equation coverage
beyond the retained component checks. Work remains fixed at 10M.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeStaticPrimitive
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf

private def source := "#![no_implicit_prelude]\n" ++
  "pub unitary fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Q<Bit>,Q<Unit>){\n" ++
  "    let q=if static n==0{q}else{phase[1,1](q)};\n    (q,u)\n}\n"

private def actual (n exponent : Nat) (wrongOwner hadamard : Bool) :
    WorkM (List Nat × List Nat × List Nat × Nat) := do
  let text := if hadamard then source.replace "phase[1,1](q)" "h(q)" else source
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let operations : List Semantics.Observation.Op := if n == 0 then [] else if hadamard then
    [.pure (.gate .h 1 2)] else
    [.pure (.applyUnitary (if wrongOwner then 0 else 1) 2
      [if wrongOwner then ⟨[],.monomial [] [0] [exponent]⟩ else ⟨[],.monomial [0] [0,1] [0,exponent]⟩])]
  let outputs := if n == 0 then [1,0] else if wrongOwner then [1,2] else [2,0]
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],operations,outputs,[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  -- This is proposal data only. Discovery independently binds it to the
  -- freshly read original source event, before the one native root is made.
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
  return (checked.result.history.issued.map (·.ordinal),checked.result.bindings.map (·.owner.ordinal),
    checked.result.bindings.map (·.port.token),checked.result.actions.length)

-- The original static identity produces no fictitious Raw action or owner.
#guard (actual 0 4 false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[1,0],0)

-- The selected primitive uses the same block/dependencies and exact Bit role.
#guard (actual 1 4 false false).run 10000000 |>.1.toOption == some ([0,1],[1,0],[2,0],1)
#guard (actual 1 4 false true).run 10000000 |>.1.toOption == some ([0,1],[1,0],[2,0],1)

-- Both mutated programs remain unitary Raw. Source phase and the held
-- zero-width owner are nevertheless independently checked by the continuation.
#guard (match (actual 1 0 false false).run 10000000 with | (.error _,_) => true | _ => false)
#guard (match (actual 1 4 true false).run 10000000 with | (.error _,_) => true | _ => false)

private def inactiveObservation : WorkM Unit := do
  let text := "#![no_implicit_prelude]\n" ++
    "pub unitary fn route[const n:Nat](u:Q<Unit>,q:Q<Bit>)->(Q<Bit>,Q<Unit>){" ++
    "let q=if static n==0{q}else{let r=basis unit(()) as x{0};let b=measure_z(r);q};(q,u)}"
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],[],[1,0],[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let tokens ← lift ((lexLocated text).mapError fun _ => Error.request)
  let some keyword := tokens.find? (·.text == "if") | throw .request
  let _ ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {naturals := [("n",0)]}
    (.mk [⟨keyword.span.startByte,0,0⟩] [] [] [] [])
  pure ()

-- An inactive original observation cannot borrow the selected pure branch.
#guard (match inactiveObservation.run 10000000 with | (.error .request,_) => true | _ => false)

private def compound (exponent : Nat) (change : List SourceSequence.Position → List SourceSequence.Position) :
    WorkM (List Nat × Nat) := do
  let text := source.replace "phase[1,1](q)" "let q=phase[1,1](q);h(q)"
  let unit : Semantics.Raw.Port := ⟨0,[],0⟩
  let bit : Semantics.Raw.Port := ⟨1,[0],1⟩
  let operations : List Semantics.Observation.Op :=
    [.pure (.applyUnitary 1 2 [⟨[],.monomial [0] [0,1] [0,exponent]⟩]),
      .pure (.gate .h 2 3),.pure (.gate .h 3 4),.pure (.gate .h 4 5)]
  let program : Semantics.Observation.Program := ⟨[unit,bit],[],operations,[5,0],[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",text)],0,none⟩
  let tokens ← lift ((lexLocated text).mapError fun _ => Error.request)
  let some keyword := tokens.find? (·.text == "if") | throw .request
  let some phase := tokens.find? (·.text == "phase") | throw .request
  let some h := tokens.find? (·.text == "h") | throw .request
  let parent : SourceSequence.Position := ⟨keyword.span.startByte,0,4⟩
  let children := change [⟨phase.span.startByte,0,1⟩,⟨h.span.startByte,1,3⟩]
  let intervals := if children.isEmpty then [] else [(parent,children)]
  let context : RuntimeContextRequest.Context := .withReferences [parent] [] [] [] [] [] intervals
  let headers ← RuntimeBodyDiscovery.readHeaders artifact "main" "route" {naturals := [("n",1)]} context
  let fresh ← RuntimeBodyDiscovery.prepare #[0] headers
  let body := headers.source.body
  let prepared ← RuntimeInterval.prepare fresh.root.dependencies fresh.root.program
  let inputs ← RuntimeSourceBoundary.readInputs body prepared
    [[.quantum ⟨unit,[.unit]⟩],[.quantum ⟨bit,[.bit]⟩]]
  let checked ← RuntimePureBody.checkPrepared artifact fresh.root body fresh.root.program context inputs.owners.bindings prepared
  return (checked.result.bindings.map (·.port.token),checked.result.actions.length)

-- One original H may occupy three exact Raw H actions in a compound arm.
#guard (compound 4 id).run 10000000 |>.1.toOption == some ([5,0],2)
#guard (compound 0 id).run 10000000 |>.1.toOption.isNone
#guard (compound 4 List.reverse).run 10000000 |>.1.toOption.isNone
#guard (compound 4 (fun _ => [])).run 10000000 |>.1.toOption.isNone
#guard (compound 4 (fun children => children ++ children)).run 10000000 |>.1.toOption.isNone

end QleisliKernel.Tests.RuntimeStaticPrimitive
