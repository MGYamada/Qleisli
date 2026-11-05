import QleisliKernel.SourceTypes.GenericOperationSubstitute
import QleisliKernel.SourceTypes.GenericCatalogue

/-! One original call-binding step over real catalogue occurrences.
Closed classification here is pending metadata, never a Meaning equation or
access proof. No Raw execution, matrix or native handle is produced.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericOperationSubstitute
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.Finite
open GenericOperation GenericOperationSubstitute

private def sourcePrelude := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn sign(q:Q<Bit>)->Q<Bit>{phase[1,1](q)}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn need[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){invoke[checked_op(U,Identity)](q)}\n"

private def transported (caller : String) : WorkM
    (List Key × Option String × List (String × String)) := do
  let catalogue ← GenericCatalogue.read #[("main",sourcePrelude ++ caller)]
  let some inner := catalogue.records.find? (·.name == "need") | throw .request
  let some outer := catalogue.records.find? (·.name == "caller") | throw .request
  let some application := outer.outcome.applications.find? (·.name == "need") | throw .request
  let some duty := inner.outcome.duties.find? (fun duty => match duty.requirement with
    | .meaning _ => true | _ => false) | throw .request
  let checked ← GenericOperationSubstitute.readDuty application duty
  let subject := checked.subject.result.subject
  let status ← GenericOperation.close subject.description
  let suppliers := subject.suppliers.map fun (_,origin) => (origin.state.owner,origin.state.name)
  match status with
  | .conditional keys _ _ => pure (keys,none,suppliers)
  | .closed closed =>
    let some (.provider owner name _ _ _) := closed.data.description.nodes[closed.data.description.root]?
      | throw .request
    pure ([],some (owner ++ "::" ++ name),suppliers)

-- The original callee assertion is abstract. This exact original caller
-- supplies sign, so a native consumer must now check its false Identity duty.
#guard (transported "unitary fn caller[const n:Nat](q:Q<Bit>)->Q<Bit>{need[sign](q)}").run 10000000
  |>.1.toOption == some ([],some "main::sign",[("main","caller")])

-- Substitution retains a genuinely open caller key and its supplier context.
#guard (transported "unitary fn caller[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){need[V](q)}").run
  10000000 |>.1.toOption == some ([.operation ⟨"main","caller",0⟩],none,[("main","caller")])

private def mixedSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{q}\n" ++
  "unitary fn middle[const A:Basis,const n:Nat](q:Q<A>)->Q<A>{adjoint(leaf[A,n])(q)}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{middle[type(Bit),2](q)}"

private def mixed : WorkM (List OperationDescription.Node × Nat × Nat × List (String × String)) := do
  let catalogue ← GenericCatalogue.read #[("main",mixedSource)]
  let some inner := catalogue.records.find? (·.name == "middle") | throw .request
  let some outer := catalogue.records.find? (·.name == "caller") | throw .request
  let some application := outer.outcome.applications.find? (·.name == "middle") | throw .request
  let some duty := inner.outcome.duties.head? | throw .request
  let checked ← GenericOperationSubstitute.readDuty application duty
  let subject := checked.subject.result.subject
  let .closed closed ← GenericOperation.close subject.description | throw .request
  pure (closed.data.description.nodes,
    (checked.subject.result.steps.map (·.result.bases.length)).sum,
    (checked.subject.result.steps.map (·.result.naturals.length)).sum,
    subject.suppliers.map fun (_,origin) => (origin.state.owner,origin.state.name))

-- Basis and Nat are transported at their original mixed ordinals. The leaf's
-- original internal supplier remains middle; it is not impersonated by caller.
#guard mixed.run 10000000 |>.1.toOption == some
  ([.provider "main" "leaf" [("A",[.bit])] [("n",2)] []],1,1,[("main","middle")])

private def recursiveSource := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "meaning Identity:Bit=reference(keep);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn need[const n:Nat,const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){" ++
  "if static n>0{need[n-1,U](q)}else{invoke[checked_op(U,Identity)](q)}}"

private def recursiveKey : WorkM (List Key × Nat) := do
  let catalogue ← GenericCatalogue.read #[("main",recursiveSource)]
  let some body := catalogue.records.find? (·.name == "need") | throw .request
  let some application := body.outcome.applications.find? (·.name == "need") | throw .request
  let some duty := body.outcome.duties.find? (fun duty => match duty.requirement with
    | .meaning _ => true | _ => false) | throw .request
  let checked ← GenericOperationSubstitute.readDuty application duty
  let .conditional keys _ _ ← GenericOperation.close checked.subject.result.subject.description | throw .request
  pure (keys,checked.subject.result.steps.length)

-- Caller and callee have the same original key in a self-call. The inserted
-- actual U stays untouched instead of recursively substituting U into itself.
#guard recursiveKey.run 10000000 |>.1.toOption == some ([.operation ⟨"main","need",1⟩],1)

private def guardedSource := "#![no_implicit_prelude]\n" ++
  "unitary fn leaf[const n:Nat](q:Q<Bit>)->Q<Bit>{q}\n" ++
  "unitary fn middle[const n:Nat](q:Q<Bit>)->Q<Bit>{if static n>0{adjoint(leaf[n-1])(q)}else{q}}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{middle[0](q)}"

private def inactiveForm : WorkM (Int × List Int × String) := do
  let catalogue ← GenericCatalogue.read #[("main",guardedSource)]
  let some inner := catalogue.records.find? (·.name == "middle") | throw .request
  let some outer := catalogue.records.find? (·.name == "caller") | throw .request
  let some application := outer.outcome.applications.find? (·.name == "middle") | throw .request
  let some duty := inner.outcome.duties.head? | throw .request
  let checked ← GenericOperationSubstitute.readDuty application duty
  let description := checked.subject.result.subject.description
  let some (.provider _ _ _ [(_,form)] _ _) := description.nodes[description.root]? | throw .request
  pure (form.constant,form.coefficients,duty.origin.state.name)

-- Transport preserves the original false guard and exact signed affine form.
-- The native expansion must retain an inactive numeric receipt, rather than
-- prematurely closing -1 or using the guard to erase a fixed independent M.
#guard inactiveForm.run 10000000 |>.1.toOption == some (-1,[],"middle")

-- These are metadata controls, not a Meaning equation, DutyAt/Invocation link,
-- native occurrence association or accepted-handle test. The first source is
-- preserved externally under generics-agent-first/meaning-marker-retention-first.
private def markerSource := sourcePrelude ++
  "unitary fn outer[const V:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(V){invoke[V](q)}\n" ++
  "unitary fn middle[const W:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(W){outer[power(then_op(checked_op(W,Identity),checked_op(W,Identity)),0)](q)}\n" ++
  "unitary fn caller[const W:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(W){middle[W](q)}"

private abbrev Marker := Nat × Nat × String × String × List String × List String

private def requestedMarkers {sources} (subject : Subject sources) : List Marker :=
  subject.suppliers.filterMap fun (index,origin) => match subject.description.nodes[index]? with
    | some (.requested ..) => some (index,origin.offset,origin.state.owner,origin.state.name,
        origin.scope,origin.tokens.map (·.text))
    | _ => none

private structure MarkerControls where
  sourceMarkers : List Marker
  insertedMarkers : List Marker
  forwardedMarkers : List Marker
  insertionSteps : Nat
  remainingKeys : List Key
  root : Nat
  childIndices : List (List Nat)
  childDuties : List (Nat × List GenericOperation.Node × List Nat)
  deriving BEq

private def markerControls : WorkM MarkerControls := do
  let catalogue ← GenericCatalogue.read #[("main",markerSource)]
  let some outer := catalogue.records.find? (·.name == "outer") | throw .request
  let some middle := catalogue.records.find? (·.name == "middle") | throw .request
  let some caller := catalogue.records.find? (·.name == "caller") | throw .request
  let some templateApplication := outer.outcome.applications.find? (·.name == "invoke") | throw .request
  let some template := templateApplication.operationActuals.head? | throw .request
  let some insertion := middle.outcome.applications.find? (·.name == "outer") | throw .request
  let some original := insertion.operationActuals.head? | throw .request
  let sourceSubject : Subject _ := ⟨original.subject,original.suppliers⟩
  -- Insert the complete actual into outer.V without traversing it as a callee
  -- template. In particular, both requested-root origins remain middle's.
  let inserted ← GenericOperationSubstitute.read insertion template.subject template.suppliers
  let some forwarding := caller.outcome.applications.find? (·.name == "middle") | throw .request
  let forwarded ← GenericOperationSubstitute.read forwarding
    inserted.result.subject.description inserted.result.subject.suppliers
  let subject := forwarded.result.subject
  let .conditional keys _ _ ← GenericOperation.close subject.description | throw .request
  let duties := middle.outcome.duties.filter (·.kind == .checkedMeaning)
  return ⟨requestedMarkers sourceSubject,requestedMarkers inserted.result.subject,requestedMarkers subject,
    inserted.result.steps.length,keys,subject.description.root,subject.description.nodes.map (·.children),
    duties.map fun duty => (duty.origin.offset,duty.subject.nodes,duty.suppliers.map (·.1))⟩

private def expectedMarkers : List Marker :=
  [(1,524,"main","middle",["W","q"],["checked_op","(","W",",","Identity",")"]),
    (3,547,"main","middle",["W","q"],["checked_op","(","W",",","Identity",")"])]

-- Binary copying and power zero retain both original written offsets on the
-- actual requested roots. Caller.W remains caller's key under simultaneous
-- substitution. Each separate Meaning duty STILL concerns its child formal
-- and the unchanged child supplier index, rather than the assertion wrapper.
#guard markerControls.run 10000000 |>.1.toOption == some {
  sourceMarkers := expectedMarkers
  insertedMarkers := expectedMarkers
  forwardedMarkers := expectedMarkers
  insertionSteps := 1
  remainingKeys := [.operation ⟨"main","caller",0⟩]
  root := 5
  childIndices := [[],[0],[],[2],[1,3],[4]]
  childDuties := [(524,[.formal ⟨"main","middle",0⟩],[0]),(547,[.formal ⟨"main","middle",0⟩],[0])]
}

end QleisliKernel.Tests.GenericOperationSubstitute
