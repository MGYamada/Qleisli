import QleisliKernel.Raw.Instrument

/-! Compute exact logical Kraus maps from the original physical histories and
independently checked code embeddings. Projection alone is insufficient: every
physical map is compared with its full lifted logical map, then the complete
logical Gram sum is checked. A producer supplies no replacement logical map.
This is typing/code-space evidence, not an external functional specification.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.CodeSpace
open Semantics.Exact Finite

/-- A certificate about the existing exact bounded computations. Their complex
denotation and source/runtime preservation remain separate proof boundaries. -/
def CompositionEquation (inputCode outputCode physical logical : Matrix) : Prop :=
  ∃ action a b c d,
    Exact.Matrix.compose physical inputCode a = (.ok action,b) ∧
    Exact.Matrix.compose outputCode logical c = (.ok action,d)

private structure Performed {α : Type} (action : WorkM α) where
  result : α
  before : Nat
  after : Nat
  ran : action.run before = (.ok result,after)

private def perform {α : Type} (action : WorkM α) : WorkM (Performed action) := fun before =>
  match ran : action.run before with
  | (.error error,after) => (.error error,after)
  | (.ok result,after) => (.ok ⟨result,before,after,ran⟩,after)

structure Map (inputCode outputCode physical : Matrix) where
  logical : Matrix
  physicalShape : physical.cols = inputCode.rows ∧ physical.rows = outputCode.rows
  logicalShape : logical.cols = inputCode.cols ∧ logical.rows = outputCode.cols
  equation : CompositionEquation inputCode outputCode physical logical

def readMap (inputCode outputCode physical : Matrix) :
    WorkM (Map inputCode outputCode physical) := do
  if physicalShape : physical.cols = inputCode.rows ∧ physical.rows = outputCode.rows then
    let actual ← perform (exactWork (Exact.Matrix.composeWork physical inputCode))
    let projection ← exactWork (Exact.Matrix.adjointWork outputCode)
    let logical ← exactWork (Exact.Matrix.composeWork projection actual.result)
    let specified ← perform (exactWork (Exact.Matrix.composeWork outputCode logical))
    exactWork (Exact.charge (actual.result.entries.length+1))
    if equal : actual.result = specified.result then
      if logicalShape : logical.cols = inputCode.cols ∧ logical.rows = outputCode.cols then
        return ⟨logical,physicalShape,logicalShape,by
          refine ⟨actual.result,actual.before,actual.after,specified.before,specified.after,?_,?_⟩
          · exact exactWork_success _ _ _ _ actual.ran
          · rw [equal]; exact exactWork_success _ _ _ _ specified.ran⟩
      else throw .request
    else throw .equation
  else throw .request

private def sumGram (dimension : Nat) (operators : List Matrix) : WorkM Matrix := do
  guard (dimension ≤ 64) .limit
  let zero ← lift (arithmetic (Exact.Matrix.make dimension dimension
    (List.replicate (dimension*dimension) Scalar.zero)))
  operators.foldlM (fun sum operator => Raw.Instrument.addGram sum ⟨[],[],operator⟩) zero

inductive Maps (inputCode outputCode : Matrix) : List Raw.Instrument.History → Type
  | nil : Maps inputCode outputCode []
  | cons {history rest} (head : Map inputCode outputCode history.operator)
      (tail : Maps inputCode outputCode rest) : Maps inputCode outputCode (history :: rest)

private def logicalsFor {inputCode outputCode} : Nat →
    ({histories : List Raw.Instrument.History} → Maps inputCode outputCode histories → List Matrix) :=
  Nat.rec (fun {_} _ => []) (fun _ next {_} maps => match maps with
    | .nil => [] | .cons head tail => head.logical :: next tail)

def Maps.logicals {inputCode outputCode histories} (maps : Maps inputCode outputCode histories) : List Matrix :=
  logicalsFor (histories.length+1) maps

private theorem logicalsFor_length {inputCode outputCode histories}
    (maps : Maps inputCode outputCode histories) (fuel : Nat) (enough : histories.length < fuel) :
    (logicalsFor fuel maps).length = histories.length := by
  induction maps generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons head tail ih =>
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ enough).elim
    | succ fuel =>
      have smaller := Nat.lt_of_succ_lt_succ enough
      simpa only [logicalsFor,List.length_cons] using congrArg Nat.succ (ih fuel smaller)

theorem Maps.logicals_length {inputCode outputCode histories} (maps : Maps inputCode outputCode histories) :
    maps.logicals.length = histories.length :=
  logicalsFor_length maps (histories.length+1) (Nat.lt_succ_self _)

private def readMaps (inputCode outputCode : Matrix) : Nat →
    (histories : List Raw.Instrument.History) → WorkM (Maps inputCode outputCode histories) :=
  Nat.rec (fun _ => throw .limit) (fun _ recurse histories => do
    match histories with
    | [] => pure .nil
    | first :: rest =>
      let head ← readMap inputCode outputCode first.operator
      let tail ← recurse rest
      return .cons head tail)

structure Checked (inputCode outputCode : Matrix) (histories : List Raw.Instrument.History) where
  maps : Maps inputCode outputCode histories
  total : Matrix
  gram : ∃ before after, (sumGram inputCode.cols maps.logicals).run before = (.ok total,after)
  identity : Exact.Matrix.identity inputCode.cols = .ok total

def read (inputCode outputCode : Matrix) (histories : List Raw.Instrument.History) :
    WorkM (Checked inputCode outputCode histories) := do
  let _ ← matrixRead inputCode
  let _ ← matrixRead outputCode
  guard (!histories.isEmpty) .request
  let maps ← readMaps inputCode outputCode (histories.length+1) histories
  let total ← perform (sumGram inputCode.cols maps.logicals)
  match computed : Exact.Matrix.identity inputCode.cols with
  | .error _ => throw .request
  | .ok identity =>
    if same : identity = total.result then
      return ⟨maps,total.result,⟨total.before,total.after,total.ran⟩,
        computed.trans (congrArg Except.ok same)⟩
    else throw .equation

theorem Maps.every_history {inputCode outputCode histories}
    (maps : Maps inputCode outputCode histories) {history : Raw.Instrument.History}
    (member : history ∈ histories) : Nonempty (Map inputCode outputCode history.operator) := by
  induction maps with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst history; exact ⟨head⟩
    · exact ih later

end QleisliKernel.CodeSpace
