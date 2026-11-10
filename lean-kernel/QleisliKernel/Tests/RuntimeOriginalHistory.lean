import QleisliKernel.Qirf.RuntimeBodyOperations

/-! Small original-body checks for exact primitive intervals and ordered
observing histories. The two X operations give the same literal primitive
more than one Raw step while preserving its mathematical action.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOriginalHistory
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes QleisliKernel.Qirf
open _root_.QleisliKernel.Semantics.Exact (Matrix Scalar)

private def bodySource (useH : Bool) : String :=
  "#![no_implicit_prelude]\npub unitary fn apply(q: Q<Bit>) -> Q<Bit> { " ++
    (if useH then "h" else "global_phase_eighth") ++ "(q) }\n"

private def rotateOps (useH : Bool) (first second last : Nat) (wrongPhase : Bool := false) :
    List Semantics.Observation.Op :=
  [ .pure (if useH then .gate .h 1 first
      else .applyUnitary 1 first [⟨[],.monomial [] [0] [if wrongPhase then 7 else 1]⟩]),
    .pure (.gate .x first second),.pure (.gate .x second last) ]

private def input : Semantics.Raw.Port := ⟨1,[0],1⟩
private def output : Semantics.Raw.Port := ⟨4,[0],1⟩

private def offset (tokens : List LocatedToken) (name : String) : WorkM Nat := do
  let some token := tokens.find? (·.text == name) | throw .request
  return token.span.startByte

private structure PrimitiveSummary where
  before : RuntimeOwnerMap.Map
  after : RuntimeOwnerMap.Map
  ordinary : RuntimeOrdinaryBody.State
  expected : Matrix
  physical : Matrix
  count : Nat

private def primitive (useH : Bool) : WorkM PrimitiveSummary := do
  let source := bodySource useH
  let tokens ← lift ((lexLocated source).mapError fun _ => .request)
  let start ← offset tokens (if useH then "h" else "global_phase_eighth")
  let program : Semantics.Observation.Program := ⟨[input],[],rotateOps useH 2 3 4,[4],[],.unitary⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",source)],0,none⟩
  let context : RuntimeContextRequest.Context := .mk [⟨start,0,3⟩] [] [] [] []
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","apply",[Semantics.RuntimeType.owner [.bit]],[[.quantum ⟨input,[.bit]⟩]],[[]],
      Semantics.RuntimeType.owner [.bit],[.quantum ⟨output,[.bit]⟩],.unitary,{}⟩
  let prepared ← RuntimeBodyOperations.prepare artifact "main" "apply" {} context
  let body ← RuntimeBodyOperations.read prepared #[0] runtime
  let [.pure (.primitive action original)] := body.checked.result.steps | throw .request
  return ⟨original.history.bindings,body.checked.result.history.bindings,body.checked.result.ordinary,
    action.expected,action.physical,action.interval.operations.length⟩

private def differentOperators : WorkM Bool := do
  let hadamard ← primitive true
  let scalar ← primitive false
  return decide (hadamard.before = scalar.before ∧ hadamard.after = scalar.after) &&
    hadamard.ordinary.table == scalar.ordinary.table &&
    hadamard.ordinary.measurements.isEmpty && scalar.ordinary.measurements.isEmpty &&
    hadamard.count == 3 && scalar.count == 3 &&
    hadamard.expected != scalar.expected && hadamard.physical != scalar.physical

private def routeSource := "#![no_implicit_prelude]\n" ++
  "unitary fn rotate(q: Q<Bit>) -> Q<Bit> { h(q) }\n" ++
  "unitary fn shift(q: Q<Bit>) -> Q<Bit> { global_phase_eighth(q) }\n" ++
  "pub observe fn route(c: Bit, q: Q<Bit>) -> Bit {\n" ++
  "    let y = if c { rotate(q) } else { shift(q) };\n" ++
  "    measure_z(y)\n}\n"

private def summarize {sources owner name signature dependencies program body prepared runtime inputs}
    {initial : @RuntimeOrdinaryInputs.Checked sources owner name signature dependencies program body prepared runtime inputs}
    {ssa bindings} : Nat →
    ({assignment : List (List Bool)} → RuntimeOrdinaryHistories.Rows initial ssa bindings assignment →
      WorkM (List (List (List Nat × Bool × Scalar)))) :=
  Nat.rec (fun {_} _ => throw .limit) (fun _ next {_} rows => match rows with
    | .nil => pure []
    | .cons row tail => do
      let here ← row.histories.mapM fun outcome => do
        let bit ← Raw.Instrument.lookup outcome.values 9
        return (outcome.hidden,bit,← outcome.operator 0 0)
      return here :: (← next tail))

private def observing (wrongPhase : Bool) : WorkM (List (List (List Nat × Bool × Scalar))) := do
  let tokens ← lift ((lexLocated routeSource).mapError fun _ => .request)
  let choose : SourceSequence.Position := ⟨← offset tokens "if",0,1⟩
  let measure : SourceSequence.Position := ⟨← offset tokens "measure_z",1,1⟩
  let [_,thenCall] := tokens.filter (·.text == "rotate") | throw .request
  let [_,elseCall] := tokens.filter (·.text == "shift") | throw .request
  let left : SourceSequence.Position := ⟨thenCall.span.startByte,0,3⟩
  let right : SourceSequence.Position := ⟨elseCall.span.startByte,0,3⟩
  let leftChild : RuntimeContextRequest.Context := .mk [⟨← offset tokens "h",0,3⟩] [] [] [] []
  let rightChild : RuntimeContextRequest.Context := .mk [⟨← offset tokens "global_phase_eighth",0,3⟩] [] [] [] []
  let context : RuntimeContextRequest.Context := .mk [choose,measure] [] []
    [(choose,.mk [left] [] [(left,leftChild)] [] [],.mk [right] [] [(right,rightChild)] [] [])] []
  let program : Semantics.Observation.Program := ⟨[input],[0],
    [.branch 0 (rotateOps true 2 3 4) (rotateOps false 5 6 7 wrongPhase) [⟨4,7,8,[1]⟩] [],
      .measure 8 9],[],[9],.observe⟩
  let artifact : Qirf.Artifact := ⟨#[program],#[],#[("main",routeSource)],0,none⟩
  let runtime : RuntimeFamily.Request :=
    ⟨.exported,"main","route",[Semantics.RuntimeType.ordinary [.bit],Semantics.RuntimeType.owner [.bit]],
      [[.ordinary [.bit] (.bit 0)],[.quantum ⟨input,[.bit]⟩]],[[false],[true]],Semantics.RuntimeType.ordinary [.bit],
      [.ordinary [.bit] (.bit 9)],.observe,{}⟩
  let prepared ← RuntimeBodyOperations.prepare artifact "main" "route" {} context
  let body ← RuntimeBodyOperations.read prepared #[0] runtime
  summarize 3 body.checked.ordinary.rows

-- Identical incoming and outgoing owner bindings and SSA tables do not
-- identify the primitive action, even with the same literal operation count.
#guard (differentOperators.run 20000000).1.toOption == some true

-- The false row selects the phase and the true row selects H. Keep the
-- zero-amplitude outcome in its original place and check the returned bit.
#guard ((observing false).run 20000000).1.toOption == some
  [[([0],false,Semantics.PrimitiveOperator.phase 1),([1],true,Scalar.zero)],
    [([0],false,Semantics.PrimitiveOperator.halfRoot),([1],true,Semantics.PrimitiveOperator.halfRoot)]]
#guard (match ((observing true).run 20000000).1 with | .error .equation => true | _ => false)

end QleisliKernel.Tests.RuntimeOriginalHistory
