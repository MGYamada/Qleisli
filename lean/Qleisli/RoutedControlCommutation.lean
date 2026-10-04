import Qleisli.SharedControlCommutation
import Qleisli.HierarchicalWiring
/-! Bounded actual hierarchy-body exchange for issue #303.
The original definition records, typed interfaces, fresh wiring summaries,
computed inverse permutations and original provider evaluations stay explicit.
Literal coordinate decompositions contain no proposed operator equations.
No source-access contract, optimizer, acceptance rule or guarantee is added.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RoutedControlCommutation
open QleisliKernel.Hierarchical
open Artifact HierarchicalOperators HierarchicalUnitary HierarchicalSemantics
open Qleisli.CoordinateOperators (Bits)
open scoped BigOperators Matrix

noncomputable def firstFactor (n m r : Nat) (U : Matrix (Bits n) (Bits n) ℂ) :
    Matrix (Bool × (Bits n × (Bits m × Bits r))) (Bool × (Bits n × (Bits m × Bits r))) ℂ :=
  ControlledPowers.block fun b => Matrix.kronecker (if b then U else 1) 1

noncomputable def secondFactor (n m r : Nat) (V : Matrix (Bits m) (Bits m) ℂ) :
    Matrix (Bool × (Bits n × (Bits m × Bits r))) (Bool × (Bits n × (Bits m × Bits r))) ℂ :=
  ControlledPowers.block fun b => Matrix.kronecker 1 (Matrix.kronecker (if b then V else 1) 1)

theorem factors_commute (n m r : Nat) (U : Matrix (Bits n) (Bits n) ℂ)
    (V : Matrix (Bits m) (Bits m) ℂ) :
    firstFactor n m r U * secondFactor n m r V = secondFactor n m r V * firstFactor n m r U := by
  unfold firstFactor secondFactor
  rw [← ControlledPowers.block_mul, ← ControlledPowers.block_mul]
  congr 1
  funext b
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp

theorem permutation_sandwich {I : Type} [Fintype I] [DecidableEq I]
    (route : I ≃ I) (M : Matrix I I ℂ) :
    permutation route.symm * M * permutation route = M.submatrix route route := by
  ext output input
  simp [Matrix.mul_apply,permutation,Matrix.submatrix,Equiv.eq_symm_apply]

/-- The literal routed list has a control head, then its ordered target and rest. -/
theorem tensor_control_entry (joint : Interface) (n k N : Nat) (step rest : Operator)
    (U : Matrix (Bits n) (Bits n) ℂ)
    (ji : width joint.inputs = N) (jo : width joint.outputs = N)
    (ci : step.inputWidth = n+1) (co : step.outputWidth = n+1)
    (stepMatrix : matrixAt (n+1) (n+1) step = HierarchicalRoutedPower.controlled n U)
    (restMatrix : matrixAt k k rest = 1)
    (output input : Bits N) (b c : Bool) (x y : Bits n) (z w : Bits k)
    (outBits : List.ofFn output = b :: (List.ofFn x ++ List.ofFn z))
    (inBits : List.ofFn input = c :: (List.ofFn y ++ List.ofFn w)) :
    matrixAt N N (apply joint .tensor [step,rest]) output input =
      (if b = c then (if c then U x y else if x = y then 1 else 0) else 0) *
        (if z = w then 1 else 0) := by
  have sizes : n+k+1 = N := by
    have h := congrArg List.length outBits
    simpa using h.symm
  have hs := congrFun (congrFun stepMatrix (Fin.cons b x)) (Fin.cons c y)
  have hr := congrFun (congrFun restMatrix z) w
  simp only [matrixAt,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ,
    HierarchicalRoutedPower.controlled,Matrix.submatrix,Fin.consEquiv_symm_apply,
    ControlledPowers.controlled,ControlledPowers.block] at hs
  simp only [matrixAt,Matrix.one_apply] at hr
  simp only [matrixAt,apply,bounded,raw,ji,jo,ci,co,outBits,inBits]
  simp only [List.length_cons,List.length_append,List.length_ofFn,sizes,and_self,ite_true,
    List.take_succ_cons,List.drop_succ_cons,List.take_left',List.drop_left']
  rw [hs,hr]
  by_cases same : b = c <;> cases c <;> simp_all [Matrix.one_apply]

theorem tensor_first_frame (joint : Interface) (n m r k N : Nat) (step rest : Operator)
    (U : Matrix (Bits n) (Bits n) ℂ)
    (ji : width joint.inputs = N) (jo : width joint.outputs = N)
    (ci : step.inputWidth = n+1) (co : step.outputWidth = n+1)
    (stepMatrix : matrixAt (n+1) (n+1) step = HierarchicalRoutedPower.controlled n U)
    (restMatrix : matrixAt k k rest = 1)
    (route : Bits N ≃ Bits N) (frame : Bits N ≃ Bool × (Bits n × (Bits m × Bits r)))
    (tail : Bits k ≃ Bits m × Bits r)
    (coordinates : ∀ bits, List.ofFn (route bits) = (frame bits).1 ::
      (List.ofFn (frame bits).2.1 ++ List.ofFn (tail.symm (frame bits).2.2))) :
    (matrixAt N N (apply joint .tensor [step,rest])).submatrix route route =
      (firstFactor n m r U).submatrix frame frame := by
  ext output input
  rw [Matrix.submatrix_apply,tensor_control_entry joint n k N step rest U ji jo ci co stepMatrix restMatrix
    (route output) (route input) _ _ _ _ _ _ (coordinates output) (coordinates input)]
  simp only [firstFactor,Matrix.submatrix,ControlledPowers.block,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Equiv.symm_apply_eq,Equiv.apply_symm_apply]
  by_cases same : (frame output).1 = (frame input).1
  · cases h : (frame input).1 <;> simp [same,h,Matrix.one_apply]
  · simp [same]

theorem tensor_second_frame (joint : Interface) (n m r k N : Nat) (step rest : Operator)
    (V : Matrix (Bits m) (Bits m) ℂ)
    (ji : width joint.inputs = N) (jo : width joint.outputs = N)
    (ci : step.inputWidth = m+1) (co : step.outputWidth = m+1)
    (stepMatrix : matrixAt (m+1) (m+1) step = HierarchicalRoutedPower.controlled m V)
    (restMatrix : matrixAt k k rest = 1)
    (route : Bits N ≃ Bits N) (frame : Bits N ≃ Bool × (Bits n × (Bits m × Bits r)))
    (tail : Bits k ≃ Bits n × Bits r)
    (coordinates : ∀ bits, List.ofFn (route bits) = (frame bits).1 ::
      (List.ofFn (frame bits).2.2.1 ++ List.ofFn (tail.symm ((frame bits).2.1,(frame bits).2.2.2)))) :
    (matrixAt N N (apply joint .tensor [step,rest])).submatrix route route =
      (secondFactor n m r V).submatrix frame frame := by
  ext output input
  rw [Matrix.submatrix_apply,tensor_control_entry joint m k N step rest V ji jo ci co stepMatrix restMatrix
    (route output) (route input) _ _ _ _ _ _ (coordinates output) (coordinates input)]
  simp only [secondFactor,Matrix.submatrix,ControlledPowers.block,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Equiv.symm_apply_eq,Equiv.apply_symm_apply,Prod.mk.injEq]
  by_cases same : (frame output).1 = (frame input).1
  · by_cases a : (frame output).2.1 = (frame input).2.1 <;>
      by_cases r : (frame output).2.2.2 = (frame input).2.2.2 <;>
      cases h : (frame input).1 <;> simp [same,h,a,r,Matrix.one_apply]
  · simp [same]

theorem permutation_mul {I : Type} [Fintype I] [DecidableEq I] (a b : I ≃ I) :
    permutation (a.trans b) = permutation b * permutation a := by
  ext output input
  simp [permutation,Matrix.mul_apply,Equiv.trans_apply]

theorem spine_product {I : Type} [Fintype I] [DecidableEq I]
    (a b : I ≃ I) (A B : Matrix I I ℂ) :
    permutation (a.trans b).symm * (B * (permutation b * (A * permutation a))) =
      B.submatrix (a.trans b) (a.trans b) * A.submatrix a a := by
  have bridge : permutation b = permutation (a.trans b) * permutation a.symm := by
    rw [← permutation_mul]
    congr 1
    apply Equiv.ext
    intro bits
    simp
  rw [bridge]
  calc
    _ = (permutation (a.trans b).symm * B * permutation (a.trans b)) *
        (permutation a.symm * A * permutation a) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [permutation_sandwich,permutation_sandwich]

theorem wiring_matrix {N : Nat} {axes inverse : List Nat} (op : Operator)
    (ready : HierarchicalWiring.At N axes op)
    (routing : QleisliKernel.Layout.Permutation N axes inverse) :
    matrixAt N N op = permutation (axisEquiv routing) := by
  ext output input
  rw [matrixAt,ready.2.2.2.2 _ _ (by simp) (by simp)]
  simp only [HierarchicalWiring.select,← axisEquiv_list routing,List.ofFn_inj]
  rfl

/-- Actual definition records and dependency indices, including owner-changing
identity renames. This view does not erase the original interfaces or owners. -/
structure Stage where
  provider : Nat
  control : Nat
  rename : Nat
  step : Nat
  rest : Nat
  tensor : Nat
  controlDef : Definition
  stepDef : Definition
  tensorDef : Definition

def Stage.Bound (s : Stage) (artifact : Artifact) : Prop :=
  artifact.definitions[s.control]? = some s.controlDef ∧
  s.controlDef.body = .control s.provider true ∧
  artifact.definitions[s.step]? = some s.stepDef ∧
  s.stepDef.body = .sequence #[s.control,s.rename] ∧
  artifact.definitions[s.tensor]? = some s.tensorDef ∧
  s.tensorDef.body = .tensor s.step s.rest

noncomputable def Stage.stepOperator (s : Stage) (provider rename : Operator) : Operator :=
  apply s.stepDef.interface .sequence [apply s.controlDef.interface (.control true) [provider],rename]

noncomputable def Stage.operator (s : Stage) (provider rename rest : Operator) : Operator :=
  apply s.tensorDef.interface .tensor [s.stepOperator provider rename,rest]

def Stage.Widths (s : Stage) (n N : Nat) : Prop :=
  width s.controlDef.interface.inputs = n+1 ∧ width s.controlDef.interface.outputs = n+1 ∧
  width s.stepDef.interface.inputs = n+1 ∧ width s.stepDef.interface.outputs = n+1 ∧
  width s.tensorDef.interface.inputs = N ∧ width s.tensorDef.interface.outputs = N

theorem stage_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (s : Stage) (fuel : Nat) (provider rename rest : Operator)
    (bound : s.Bound artifact)
    (hp : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.provider = some provider)
    (hn : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.rename = some rename)
    (hr : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.rest = some rest) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) s.tensor =
      some (s.operator provider rename rest) := by
  have control := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact fuel s.control s.controlDef
    (.control true) [s.provider] bound.1 (by simp [physicalCode,bound.2.1])
  have renameMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.rename rename hn (fuel+1) (by omega)
  have restMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.rest rest hr (fuel+2) (by omega)
  have step := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1) s.step s.stepDef
    .sequence [s.control,s.rename] bound.2.2.1 (by simp [physicalCode,bound.2.2.2.1])
  have tensor := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+2) s.tensor s.tensorDef
    .tensor [s.step,s.rest] bound.2.2.2.2.1 (by simp [physicalCode,bound.2.2.2.2.2])
  simp only [HierarchicalFiniteEvaluation.physical] at *
  simp [hp] at control
  simp [control,renameMore] at step
  simpa [step,restMore,Stage.operator,Stage.stepOperator] using tensor

theorem step_matrix (s : Stage) (n N : Nat) (provider rename : Operator)
    (widths : s.Widths n N) (ready : HierarchicalWiring.At (n+1) (List.range (n+1)) rename) :
    matrixAt (n+1) (n+1) (s.stepOperator provider rename) =
      HierarchicalRoutedPower.controlled n (matrixAt n n provider) := by
  unfold Stage.stepOperator
  rw [HierarchicalFourier.apply_sequence_matrix _ (n+1) _ widths.2.2.1 widths.2.2.2.1]
  · simp only [List.foldl_cons,List.foldl_nil,Matrix.mul_one,
      HierarchicalFourierRoot.identity_matrix _ rename ready,Matrix.one_mul]
    exact HierarchicalRoutedPower.apply_control_matrix _ n provider widths.1 widths.2.1
  · intro child inside
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl
    · exact ⟨widths.1,widths.2.1⟩
    · exact ⟨ready.2.2.1,ready.2.2.2.1⟩

structure Spine where
  root : Nat
  rootDef : Definition
  first : Stage
  second : Stage
  enter : Nat
  middle : Nat
  leave : Nat

def Spine.Bound (s : Spine) (artifact : Artifact) : Prop :=
  artifact.definitions[s.root]? = some s.rootDef ∧
  s.rootDef.body = .sequence #[s.enter,s.first.tensor,s.middle,s.second.tensor,s.leave] ∧
  s.first.Bound artifact ∧ s.second.Bound artifact

noncomputable def Spine.operator (s : Spine) (U V renameA restA renameB restB enter middle leave : Operator) : Operator :=
  apply s.rootDef.interface .sequence
    [enter,s.first.operator U renameA restA,middle,s.second.operator V renameB restB,leave]

theorem spine_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (s : Spine) (fuel : Nat)
    (U V renameA restA renameB restB enter middle leave : Operator)
    (bound : s.Bound artifact)
    (hu : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.first.provider = some U)
    (hv : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.second.provider = some V)
    (hna : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.first.rename = some renameA)
    (hra : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.first.rest = some restA)
    (hnb : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.second.rename = some renameB)
    (hrb : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.second.rest = some restB)
    (he : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.enter = some enter)
    (hm : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.middle = some middle)
    (hl : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.leave = some leave) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+4) s.root =
      some (s.operator U V renameA restA renameB restB enter middle leave) := by
  have first := stage_evaluates leaves artifact s.first fuel U renameA restA bound.2.2.1 hu hna hra
  have second := stage_evaluates leaves artifact s.second fuel V renameB restB bound.2.2.2 hv hnb hrb
  have enterMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.enter enter he (fuel+3) (by omega)
  have middleMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.middle middle hm (fuel+3) (by omega)
  have leaveMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.leave leave hl (fuel+3) (by omega)
  have root := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+3) s.root s.rootDef
    .sequence [s.enter,s.first.tensor,s.middle,s.second.tensor,s.leave] bound.1
    (by simp [physicalCode,bound.2.1])
  simp only [HierarchicalFiniteEvaluation.physical] at *
  simpa [Spine.operator,first,second,enterMore,middleMore,leaveMore] using root

theorem spine_matrix (s : Spine) (N n m : Nat)
    (U V renameA restA renameB restB enter middle leave : Operator)
    (fi : width s.rootDef.interface.inputs = N) (fo : width s.rootDef.interface.outputs = N)
    (wa : s.first.Widths n N) (wb : s.second.Widths m N)
    (enterAxes middleAxes leaveAxes enterInverse middleInverse leaveInverse : List Nat)
    (enterAt : HierarchicalWiring.At N enterAxes enter)
    (middleAt : HierarchicalWiring.At N middleAxes middle)
    (leaveAt : HierarchicalWiring.At N leaveAxes leave)
    (pe : QleisliKernel.Layout.Permutation N enterAxes enterInverse)
    (pm : QleisliKernel.Layout.Permutation N middleAxes middleInverse)
    (pl : QleisliKernel.Layout.Permutation N leaveAxes leaveInverse)
    (inverse : axisEquiv pl = ((axisEquiv pe).trans (axisEquiv pm)).symm) :
    matrixAt N N (s.operator U V renameA restA renameB restB enter middle leave) =
      (matrixAt N N (s.second.operator V renameB restB)).submatrix
        ((axisEquiv pe).trans (axisEquiv pm)) ((axisEquiv pe).trans (axisEquiv pm)) *
      (matrixAt N N (s.first.operator U renameA restA)).submatrix (axisEquiv pe) (axisEquiv pe) := by
  unfold Spine.operator
  rw [HierarchicalFourier.apply_sequence_matrix _ N _ fi fo]
  · simp only [List.foldl_cons,List.foldl_nil,Matrix.mul_one,
      wiring_matrix enter enterAt pe,wiring_matrix middle middleAt pm,wiring_matrix leave leaveAt pl,inverse]
    exact spine_product _ _ _ _
  · intro child inside
    simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl
    · exact ⟨enterAt.2.2.1,enterAt.2.2.2.1⟩
    · exact ⟨wa.2.2.2.2.1,wa.2.2.2.2.2⟩
    · exact ⟨middleAt.2.2.1,middleAt.2.2.2.1⟩
    · exact ⟨wb.2.2.2.2.1,wb.2.2.2.2.2⟩
    · exact ⟨leaveAt.2.2.1,leaveAt.2.2.2.1⟩

/-- Proof premises for one original artifact. Fresh typing and wiring calls are
kept separate from provider evaluation; this record is not an acceptance API. -/
structure Premises (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (s : Spine) (N n m k l : Nat) where
  bound : s.Bound artifact
  rootEntry : s.root = artifact.entry.implementation
  typingOrder : Array Nat
  typed : NodeTyping.Typed
  typing : NodeTyping.checkAll artifact typingOrder = .ok typed
  rootInput : width s.rootDef.interface.inputs = N
  rootOutput : width s.rootDef.interface.outputs = N
  firstWidths : s.first.Widths n N
  secondWidths : s.second.Widths m N
  wiringOrder : Array Nat
  remaining : Nat
  state : Wiring.State
  wiring : Wiring.inspect artifact wiringOrder remaining = .ok state
  enterAxes : List Nat
  middleAxes : List Nat
  leaveAxes : List Nat
  enterFound : (state.cache[s.enter]?).bind id = some enterAxes
  middleFound : (state.cache[s.middle]?).bind id = some middleAxes
  leaveFound : (state.cache[s.leave]?).bind id = some leaveAxes
  renameAFound : (state.cache[s.first.rename]?).bind id = some (List.range (n+1))
  restAFound : (state.cache[s.first.rest]?).bind id = some (List.range k)
  renameBFound : (state.cache[s.second.rename]?).bind id = some (List.range (m+1))
  restBFound : (state.cache[s.second.rest]?).bind id = some (List.range l)
  enterPermutation : QleisliKernel.Layout.Permutation N enterAxes (Ports.inverse N enterAxes.toArray)
  middlePermutation : QleisliKernel.Layout.Permutation N middleAxes (Ports.inverse N middleAxes.toArray)
  leavePermutation : QleisliKernel.Layout.Permutation N leaveAxes (Ports.inverse N leaveAxes.toArray)
  inverse : axisEquiv leavePermutation =
    ((axisEquiv enterPermutation).trans (axisEquiv middlePermutation)).symm
  U : Operator
  V : Operator
  providerFuel : Nat
  firstEvaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact providerFuel s.first.provider = some U
  secondEvaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact providerFuel s.second.provider = some V
  firstInput : U.inputWidth = n
  firstOutput : U.outputWidth = n
  secondInput : V.inputWidth = m
  secondOutput : V.outputWidth = m

/-- Complete same-artifact typing survives the proof view; the algebra below
uses ordered coordinates, while these conditions retain the actual owner data. -/
theorem typed_definition {leaves : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifact : Artifact} {s : Spine} {N n m k l : Nat}
    (p : Premises leaves artifact s N n m k l) (index : Nat) (d : Definition)
    (found : artifact.definitions[index]? = some d) : NodeTyping.conditions artifact d = true := by
  have inside : index < artifact.definitions.size := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨actual,ha,typed⟩ := (NodeTyping.checkAll_conditions artifact p.typingOrder p.typed p.typing).2.2.2 index inside
  have same : actual = d := Option.some.inj (ha.symm.trans found)
  simpa [same] using typed

structure Realization (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (s : Spine) (N n m k l : Nat)
    (p : Premises leaves artifact s N n m k l) where
  renameA : Operator
  restA : Operator
  renameB : Operator
  restB : Operator
  enter : Operator
  middle : Operator
  leave : Operator
  renameAAt : HierarchicalWiring.At (n+1) (List.range (n+1)) renameA
  restAAt : HierarchicalWiring.At k (List.range k) restA
  renameBAt : HierarchicalWiring.At (m+1) (List.range (m+1)) renameB
  restBAt : HierarchicalWiring.At l (List.range l) restB
  enterAt : HierarchicalWiring.At N p.enterAxes enter
  middleAt : HierarchicalWiring.At N p.middleAxes middle
  leaveAt : HierarchicalWiring.At N p.leaveAxes leave
  fuel : Nat
  evaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.root =
    some (s.operator p.U p.V renameA restA renameB restB enter middle leave)

theorem realizes {leaves : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifact : Artifact} {s : Spine} {N n m k l : Nat}
    (p : Premises leaves artifact s N n m k l) : Nonempty (Realization leaves artifact s N n m k l p) := by
  have wire (index : Nat) (axes : List Nat) (w : Nat)
      (found : (p.state.cache[index]?).bind id = some axes) (size : axes.length = w) :
      ∃ fuel op, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some op ∧
        HierarchicalWiring.At w axes op := by
    simpa only [size] using HierarchicalWiring.inspect_evaluates leaves artifact p.wiringOrder p.remaining p.state
      index axes p.wiring found
  obtain ⟨fe,enter,he,ae⟩ := wire s.enter p.enterAxes N p.enterFound p.enterPermutation.1
  obtain ⟨fm,middle,hm,am⟩ := wire s.middle p.middleAxes N p.middleFound p.middlePermutation.1
  obtain ⟨fl,leave,hl,al⟩ := wire s.leave p.leaveAxes N p.leaveFound p.leavePermutation.1
  obtain ⟨fna,renameA,hna,ana⟩ := wire s.first.rename (List.range (n+1)) (n+1) p.renameAFound (by simp)
  obtain ⟨fra,restA,hra,ara⟩ := wire s.first.rest (List.range k) k p.restAFound (by simp)
  obtain ⟨fnb,renameB,hnb,anb⟩ := wire s.second.rename (List.range (m+1)) (m+1) p.renameBFound (by simp)
  obtain ⟨frb,restB,hrb,arb⟩ := wire s.second.rest (List.range l) l p.restBFound (by simp)
  let fuel := p.providerFuel+fe+fm+fl+fna+fra+fnb+frb
  have more {old index : Nat} {op : Operator}
      (h : HierarchicalFiniteEvaluation.physical algebra leaves artifact old index = some op)
      (enough : old ≤ fuel) : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some op :=
    HierarchicalFiniteEvaluation.evaluate_more algebra (HierarchicalFiniteEvaluation.definition leaves artifact)
      old index op h fuel enough
  refine ⟨⟨renameA,restA,renameB,restB,enter,middle,leave,ana,ara,anb,arb,ae,am,al,fuel+4,?_⟩⟩
  exact spine_evaluates leaves artifact s fuel p.U p.V renameA restA renameB restB enter middle leave p.bound
    (more p.firstEvaluated (by dsimp [fuel]; omega)) (more p.secondEvaluated (by dsimp [fuel]; omega))
    (more hna (by dsimp [fuel]; omega)) (more hra (by dsimp [fuel]; omega))
    (more hnb (by dsimp [fuel]; omega)) (more hrb (by dsimp [fuel]; omega))
    (more he (by dsimp [fuel]; omega)) (more hm (by dsimp [fuel]; omega)) (more hl (by dsimp [fuel]; omega))

theorem evaluated_spine_matrix {leaves : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifact : Artifact} {s : Spine} {N n m k l : Nat}
    (p : Premises leaves artifact s N n m k l)
    (v : Realization leaves artifact s N n m k l p) (fuel : Nat) (actual : Operator)
    (evaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.root = some actual) :
    matrixAt N N actual =
      (matrixAt N N (s.second.operator p.V v.renameB v.restB)).submatrix
        ((axisEquiv p.enterPermutation).trans (axisEquiv p.middlePermutation))
        ((axisEquiv p.enterPermutation).trans (axisEquiv p.middlePermutation)) *
      (matrixAt N N (s.first.operator p.U v.renameA v.restA)).submatrix
        (axisEquiv p.enterPermutation) (axisEquiv p.enterPermutation) := by
  have same := HierarchicalFiniteEvaluation.evaluate_unique algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel v.fuel s.root actual _ evaluated v.evaluated
  rw [same]
  exact spine_matrix s N n m p.U p.V v.renameA v.restA v.renameB v.restB v.enter v.middle v.leave
    p.rootInput p.rootOutput p.firstWidths p.secondWidths p.enterAxes p.middleAxes p.leaveAxes _ _ _
    v.enterAt v.middleAt v.leaveAt p.enterPermutation p.middlePermutation p.leavePermutation p.inverse

def Premises.firstRoute {leaves : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifact : Artifact} {s : Spine} {N n m k l : Nat}
    (p : Premises leaves artifact s N n m k l) : Bits N ≃ Bits N := axisEquiv p.enterPermutation

def Premises.secondRoute {leaves : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifact : Artifact} {s : Spine} {N n m k l : Nat}
    (p : Premises leaves artifact s N n m k l) : Bits N ≃ Bits N :=
  p.firstRoute.trans (axisEquiv p.middlePermutation)

/-- Four literal coordinate decompositions, one per actual local frame. The
routes themselves remain distinct, and the untouched factor may be reordered
inside each identity rest. No operator or provider meaning occurs in these laws. -/
structure Frames {leavesA leavesB : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifactA artifactB : Artifact} {a b : Spine} {N n m ka la kb lb : Nat}
    (p : Premises leavesA artifactA a N n m ka la)
    (q : Premises leavesB artifactB b N m n kb lb) (r : Nat) where
  common : Bits N ≃ Bool × (Bits n × (Bits m × Bits r))
  firstTail : Bits ka ≃ Bits m × Bits r
  secondTail : Bits la ≃ Bits n × Bits r
  reverseFirstTail : Bits kb ≃ Bits n × Bits r
  reverseSecondTail : Bits lb ≃ Bits m × Bits r
  first : ∀ bits, List.ofFn (p.firstRoute bits) = (common bits).1 ::
    (List.ofFn (common bits).2.1 ++ List.ofFn (firstTail.symm (common bits).2.2))
  second : ∀ bits, List.ofFn (p.secondRoute bits) = (common bits).1 ::
    (List.ofFn (common bits).2.2.1 ++ List.ofFn (secondTail.symm ((common bits).2.1,(common bits).2.2.2)))
  reverseFirst : ∀ bits, List.ofFn (q.firstRoute bits) = (common bits).1 ::
    (List.ofFn (common bits).2.2.1 ++ List.ofFn (reverseFirstTail.symm ((common bits).2.1,(common bits).2.2.2)))
  reverseSecond : ∀ bits, List.ofFn (q.secondRoute bits) = (common bits).1 ::
    (List.ofFn (common bits).2.1 ++ List.ofFn (reverseSecondTail.symm (common bits).2.2))

/-- Equality of the original, independently evaluated entry bodies. The two
provider equations compare their original evaluations, not whole-body claims.
Source access and acceptance/work preservation are deliberately outside scope. -/
theorem actual_exchange {leavesA leavesB : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifactA artifactB : Artifact} {a b : Spine} {N n m ka la kb lb : Nat}
    (p : Premises leavesA artifactA a N n m ka la)
    (q : Premises leavesB artifactB b N m n kb lb) (r : Nat) (frames : Frames p q r)
    (sameU : matrixAt n n p.U = matrixAt n n q.V)
    (sameV : matrixAt m m p.V = matrixAt m m q.U)
    (fuelA fuelB : Nat) (actualA actualB : Operator)
    (evaluatedA : HierarchicalFiniteEvaluation.physical algebra leavesA artifactA fuelA
      artifactA.entry.implementation = some actualA)
    (evaluatedB : HierarchicalFiniteEvaluation.physical algebra leavesB artifactB fuelB
      artifactB.entry.implementation = some actualB) :
    matrixAt N N actualA = matrixAt N N actualB := by
  obtain ⟨v⟩ := realizes p
  obtain ⟨w⟩ := realizes q
  have af := tensor_first_frame a.first.tensorDef.interface n m r ka N
    (a.first.stepOperator p.U v.renameA) v.restA (matrixAt n n p.U)
    p.firstWidths.2.2.2.2.1 p.firstWidths.2.2.2.2.2 p.firstWidths.2.2.1 p.firstWidths.2.2.2.1
    (step_matrix a.first n N p.U v.renameA p.firstWidths v.renameAAt)
    (HierarchicalFourierRoot.identity_matrix ka v.restA v.restAAt)
    p.firstRoute frames.common frames.firstTail frames.first
  have as := tensor_second_frame a.second.tensorDef.interface n m r la N
    (a.second.stepOperator p.V v.renameB) v.restB (matrixAt m m p.V)
    p.secondWidths.2.2.2.2.1 p.secondWidths.2.2.2.2.2 p.secondWidths.2.2.1 p.secondWidths.2.2.2.1
    (step_matrix a.second m N p.V v.renameB p.secondWidths v.renameBAt)
    (HierarchicalFourierRoot.identity_matrix la v.restB v.restBAt)
    p.secondRoute frames.common frames.secondTail frames.second
  have bf := tensor_second_frame b.first.tensorDef.interface n m r kb N
    (b.first.stepOperator q.U w.renameA) w.restA (matrixAt m m q.U)
    q.firstWidths.2.2.2.2.1 q.firstWidths.2.2.2.2.2 q.firstWidths.2.2.1 q.firstWidths.2.2.2.1
    (step_matrix b.first m N q.U w.renameA q.firstWidths w.renameAAt)
    (HierarchicalFourierRoot.identity_matrix kb w.restA w.restAAt)
    q.firstRoute frames.common frames.reverseFirstTail frames.reverseFirst
  have bs := tensor_first_frame b.second.tensorDef.interface n m r lb N
    (b.second.stepOperator q.V w.renameB) w.restB (matrixAt n n q.V)
    q.secondWidths.2.2.2.2.1 q.secondWidths.2.2.2.2.2 q.secondWidths.2.2.1 q.secondWidths.2.2.2.1
    (step_matrix b.second n N q.V w.renameB q.secondWidths w.renameBAt)
    (HierarchicalFourierRoot.identity_matrix lb w.restB w.restBAt)
    q.secondRoute frames.common frames.reverseSecondTail frames.reverseSecond
  rw [evaluated_spine_matrix p v fuelA actualA (by simpa [p.rootEntry] using evaluatedA),
    evaluated_spine_matrix q w fuelB actualB (by simpa [q.rootEntry] using evaluatedB)]
  change _ * _ = _ * _
  change (matrixAt N N (a.first.operator p.U v.renameA v.restA)).submatrix
    (axisEquiv p.enterPermutation) (axisEquiv p.enterPermutation) = _ at af
  change (matrixAt N N (a.second.operator p.V v.renameB v.restB)).submatrix
    ((axisEquiv p.enterPermutation).trans (axisEquiv p.middlePermutation))
    ((axisEquiv p.enterPermutation).trans (axisEquiv p.middlePermutation)) = _ at as
  change (matrixAt N N (b.first.operator q.U w.renameA w.restA)).submatrix
    (axisEquiv q.enterPermutation) (axisEquiv q.enterPermutation) = _ at bf
  change (matrixAt N N (b.second.operator q.V w.renameB w.restB)).submatrix
    ((axisEquiv q.enterPermutation).trans (axisEquiv q.middlePermutation))
    ((axisEquiv q.enterPermutation).trans (axisEquiv q.middlePermutation)) = _ at bs
  rw [af,as,bf,bs,← sameU,← sameV,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
  exact congrArg (fun M => M.submatrix frames.common frames.common)
    (factors_commute n m r (matrixAt n n p.U) (matrixAt m m p.V)).symm

/-- The same exact entry equality retains every external reference amplitude,
including correlated control/target/reference states. No reference dimension or
separability premise is introduced. -/
theorem actual_exchange_reference {R : Type}
    {leavesA leavesB : HierarchicalFiniteEvaluation.Leaves Operator}
    {artifactA artifactB : Artifact} {a b : Spine} {N n m ka la kb lb : Nat}
    (p : Premises leavesA artifactA a N n m ka la)
    (q : Premises leavesB artifactB b N m n kb lb) (r : Nat) (frames : Frames p q r)
    (sameU : matrixAt n n p.U = matrixAt n n q.V)
    (sameV : matrixAt m m p.V = matrixAt m m q.U)
    (fuelA fuelB : Nat) (actualA actualB : Operator)
    (evaluatedA : HierarchicalFiniteEvaluation.physical algebra leavesA artifactA fuelA
      artifactA.entry.implementation = some actualA)
    (evaluatedB : HierarchicalFiniteEvaluation.physical algebra leavesB artifactB fuelB
      artifactB.entry.implementation = some actualB)
    (ψ : Bits N → R → ℂ) (output : Bits N) (reference : R) :
    (matrixAt N N actualA *ᵥ (fun input => ψ input reference)) output =
      (matrixAt N N actualB *ᵥ (fun input => ψ input reference)) output := by
  rw [actual_exchange p q r frames sameU sameV fuelA fuelB actualA actualB evaluatedA evaluatedB]

end Qleisli.RoutedControlCommutation
