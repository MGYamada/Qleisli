import Qleisli.HierarchicalDiagonal
import QleisliKernel.Hierarchical.Gradient

/-! Actual recursive phase-gradient inspection implies exact complex semantics.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
No whole-graph interpretation or producer matrix is assumed. This component
is not yet the complete named Fourier schema or a production authority gate. -/

namespace Qleisli.HierarchicalGradient
open QleisliKernel.Hierarchical
open Artifact HierarchicalSemantics HierarchicalOperators HierarchicalUnitary HierarchicalDiagonal
open scoped BigOperators Matrix

/-- Independent little-endian integer interpretation. Peel the highest axis;
this is arithmetic on basis labels, not a circuit evaluator. -/
def number : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n+1, bits => number n (fun i => bits i.castSucc) +
      if bits (Fin.last n) then 2^n else 0

theorem phase_add (a b precision : Nat) :
    phase (a+b) precision = phase a precision * phase b precision := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_axis (precision n : Nat) (enough : n ≤ precision) :
    phase 1 (precision-n) = phase (2^n) precision := by
  have h := phase_precision 1 precision (precision-n) (by omega)
  rw [phase_power] at h
  simpa [Nat.sub_sub_self enough] using h.symm

theorem tensor_bit_at (interface : Interface) (n : Nat) (first second : Operator)
    (a : Bool → ℂ) (b : (Fin n → Bool) → ℂ)
    (hi : width interface.inputs = n+1) (ho : width interface.outputs = n+1)
    (ha : At 1 first (fun bits => a (bits 0))) (hb : At n second b) :
    At (n+1) (apply interface .tensor [first,second])
      (fun bits => a (bits 0) * b (fun i => bits i.succ)) := by
  refine ⟨hi,ho,?_⟩
  ext output input
  have left := congrFun (congrFun ha.2.2 (fun _ => output 0)) (fun _ => input 0)
  have right := congrFun (congrFun hb.2.2 (fun i => output i.succ)) (fun i => input i.succ)
  simp only [matrixAt, List.ofFn_succ, List.ofFn_zero] at left
  simp only [matrixAt] at right
  simp only [matrixAt,apply,bounded,raw,hi,ho,
    ha.1,ha.2.1,List.ofFn_succ,List.take_succ_cons,List.take_zero,List.drop_succ_cons,
    List.drop_zero,left,right,Matrix.diagonal_apply]
  by_cases same : output = input
  · subst output
    simp
  · have differing : output 0 ≠ input 0 ∨
        (fun i : Fin n => output i.succ) ≠ (fun i : Fin n => input i.succ) := by
      by_contra h
      simp only [not_or,not_not] at h
      apply same
      funext i
      exact Fin.cases h.1 (fun j => congrFun h.2 j) i
    rcases differing with head | tail
    · have heads : (fun _ : Fin 1 => output 0) ≠ (fun _ => input 0) :=
        fun equal => head (congrFun equal 0)
      simp_all
    · simp_all

theorem route_head (n : Nat) (bits : Fin (n+1) → Bool) :
    axisEquiv (Gradient.routing n) bits 0 = bits (Fin.last n) := by
  simp only [axisEquiv,Equiv.coe_fn_mk,QleisliKernel.Layout.reindex,Fin.val_zero,Gradient.high_zero]
  rfl

theorem route_tail (n : Nat) (bits : Fin (n+1) → Bool) :
    (fun i : Fin n => axisEquiv (Gradient.routing n) bits i.succ) =
      (fun i => bits i.castSucc) := by
  funext i
  simp only [axisEquiv,Equiv.coe_fn_mk,QleisliKernel.Layout.reindex,Fin.val_succ,Gradient.high_succ n i i.isLt]
  rfl

theorem register_widths (d : Definition) (n : Nat) (valid : Gradient.register d n = true) :
    width d.interface.inputs = n ∧ width d.interface.outputs = n := by
  simp only [Gradient.register,Bool.and_eq_true,beq_iff_eq] at valid
  exact ⟨valid.2,by rw [← valid.1.1.2]; exact valid.2⟩

theorem bit_widths (d : Definition) (owner : Nat) (valid : Gradient.bit d owner = true) :
    width d.interface.inputs = 1 ∧ width d.interface.outputs = 1 ∧ ownerAxis d.interface owner = 0 := by
  unfold Gradient.bit at valid
  cases hp : d.interface.inputs.quantum[0]? with
  | none => simp [hp] at valid
  | some p =>
    simp only [hp,bind,Option.bind,pure,Option.getD_some,
      Bool.and_eq_true,beq_iff_eq] at valid
    obtain ⟨⟨⟨_,_⟩,closed⟩,⟨⟨⟨ports,_⟩,ownerEq⟩,axes⟩⟩ := valid
    have hi : width d.interface.inputs = 1 := by simp [width,wires,ports,axes]
    exact ⟨hi,by rw [← closed]; exact hi,by simp [ownerAxis,ports,ownerEq]⟩

structure Geometry (precision n : Nat) (s : Gradient.Step) : Prop where
  rootInput : width s.root.interface.inputs = n+1
  rootOutput : width s.root.interface.outputs = n+1
  enterInput : width s.enter.interface.inputs = n+1
  enterOutput : width s.enter.interface.outputs = n+1
  actionInput : width s.action.interface.inputs = n+1
  actionOutput : width s.action.interface.outputs = n+1
  leaveInput : width s.leave.interface.inputs = n+1
  leaveOutput : width s.leave.interface.outputs = n+1
  phaseInput : width s.phase.interface.inputs = 1
  phaseOutput : width s.phase.interface.outputs = 1
  phaseAxis : ownerAxis s.phase.interface s.target = 0
  numerator : s.numerator = 1
  exponent : s.exponent = precision-n
  forward : Structural.axisMap s.enter.interface = Gradient.highAxes n
  backward : Structural.axisMap s.leave.interface = Gradient.lowAxes n

theorem shape_geometry (precision n : Nat) (s : Gradient.Step)
    (valid : Gradient.shape precision n s = true) : Geometry precision n s := by
  simp only [Gradient.shape,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at valid
  have root := register_widths s.root (n+1) (by tauto)
  have tail := register_widths s.tail n (by tauto)
  have phase := bit_widths s.phase s.target (by tauto)
  have ei : s.enter.interface.inputs = s.root.interface.inputs := by tauto
  have eo : s.enter.interface.outputs = NodeTyping.append s.phase.interface.inputs s.tail.interface.inputs := by tauto
  have action : s.action.interface = ⟨s.enter.interface.outputs,s.enter.interface.outputs⟩ := by tauto
  have leave : s.leave.interface = Structural.swapped s.enter.interface := by tauto
  have entry : width s.enter.interface.inputs = n+1 := by rw [ei,root.1]
  have exit : width s.enter.interface.outputs = n+1 := by
    rw [eo,HierarchicalTyping.width_append,phase.1,tail.1,Nat.add_comm]
  exact ⟨root.1,root.2,entry,exit,by simpa [action] using exit,by simpa [action] using exit,
    by simpa [leave,Structural.swapped] using exit,by simpa [leave,Structural.swapped] using entry,
    phase.1,phase.2.1,phase.2.2,by tauto,by tauto,by tauto,by tauto⟩

theorem sequence_three_matrix (interface : Interface) (n : Nat) (a b c : Operator)
    (hi : width interface.inputs = n) (ho : width interface.outputs = n)
    (ai : a.inputWidth = n) (ao : a.outputWidth = n)
    (bi : b.inputWidth = n) (bo : b.outputWidth = n)
    (ci : c.inputWidth = n) (co : c.outputWidth = n) :
    matrixAt n n (apply interface .sequence [a,b,c]) =
      matrixAt n n c * (matrixAt n n b * matrixAt n n a) := by
  have first := matrix_compose a (identity n)
  change matrixAt n a.outputWidth (compose a (identity n)) =
    matrixAt a.inputWidth a.outputWidth a * matrixAt n a.inputWidth (identity n) at first
  rw [ai,ao,matrix_identity,Matrix.mul_one] at first
  have middle := matrix_compose b (compose a (identity n))
  change matrixAt n b.outputWidth _ = matrixAt b.inputWidth b.outputWidth b *
    matrixAt n b.inputWidth (compose a (identity n)) at middle
  rw [bi,bo,first] at middle
  have last := matrix_compose c (compose b (compose a (identity n)))
  change matrixAt n c.outputWidth _ = matrixAt c.inputWidth c.outputWidth c *
    matrixAt n c.inputWidth (compose b (compose a (identity n))) at last
  rw [ci,co,middle] at last
  have same : matrixAt n n (apply interface .sequence [a,b,c]) =
      matrixAt n n (compose c (compose b (compose a (identity n)))) := by
    ext output input
    simp [matrixAt,apply,bounded,raw,hi,ho,HierarchicalOperators.sequence]
  rw [same,last]

theorem routed_sequence_at (root before after : Interface) (n : Nat)
    (forward backward : List Nat) (routing : QleisliKernel.Layout.Permutation n forward backward)
    (ri : width root.inputs = n) (ro : width root.outputs = n)
    (bi : width before.inputs = n) (bo : width before.outputs = n)
    (ai : width after.inputs = n) (ao : width after.outputs = n)
    (child : Operator) (values : (Fin n → Bool) → ℂ) (ready : At n child values) :
    At n (apply root .sequence [apply before (.rewire forward) [],child,apply after (.rewire backward) []])
      (fun bits => values (axisEquiv routing bits)) := by
  have inverse : QleisliKernel.Layout.Permutation n backward forward := by
    refine ⟨routing.2.1,routing.1,?_⟩
    intro i
    exact ⟨(routing.2.2 i).2.1,(routing.2.2 i).1,
      (routing.2.2 i).2.2.2,(routing.2.2 i).2.2.1⟩
  have same : axisEquiv inverse = (axisEquiv routing).symm := by
    apply Equiv.ext
    intro bits
    rfl
  refine ⟨ri,ro,?_⟩
  rw [sequence_three_matrix root n _ _ _ ri ro bi bo ready.1 ready.2.1 ai ao,
    rewire_matrix before n forward backward bi bo routing,
    rewire_matrix after n backward forward ai ao inverse,same,ready.2.2,
    ← Matrix.mul_assoc,conjugate_diagonal]

noncomputable def realize (s : Gradient.Step) (child : Operator) : Operator :=
  apply s.root.interface .sequence
    [apply s.enter.interface (.rewire (Structural.axisMap s.enter.interface)) [],
     apply s.action.interface .tensor
       [apply s.phase.interface (.phase s.target s.numerator s.exponent) [],child],
     apply s.leave.interface (.rewire (Structural.axisMap s.leave.interface)) []]

theorem step_at (precision n : Nat) (s : Gradient.Step) (child : Operator)
    (enough : n+1 ≤ precision) (valid : Gradient.shape precision n s = true)
    (ready : At n child (fun bits => phase (number n bits) precision)) :
    At (n+1) (realize s child) (fun bits => phase (number (n+1) bits) precision) := by
  have g := shape_geometry precision n s valid
  have p := phase_at s.phase.interface 1 s.target s.numerator s.exponent g.phaseInput g.phaseOutput
  have pe : (fun bits : Fin 1 → Bool =>
      if (List.ofFn bits)[ownerAxis s.phase.interface s.target]?.getD false
      then phase s.numerator s.exponent else 1) =
      (fun bits => if bits 0 then phase 1 (precision-n) else 1) := by
    funext bits
    simp [g.phaseAxis,g.numerator,g.exponent,List.ofFn_succ]
  rw [pe] at p
  have t := tensor_bit_at s.action.interface n _ child
    (fun bit => if bit then phase 1 (precision-n) else 1) _ g.actionInput g.actionOutput p ready
  have r := routed_sequence_at s.root.interface s.enter.interface s.leave.interface (n+1)
    (Gradient.highAxes n) (Gradient.lowAxes n) (Gradient.routing n)
    g.rootInput g.rootOutput g.enterInput g.enterOutput g.leaveInput g.leaveOutput _ _ t
  have re : (fun bits : Fin (n+1) → Bool =>
      (if axisEquiv (Gradient.routing n) bits 0 then phase 1 (precision-n) else 1) *
        phase (number n (fun i => axisEquiv (Gradient.routing n) bits i.succ)) precision) =
      (fun bits => phase (number (n+1) bits) precision) := by
    funext bits
    rw [route_head,route_tail,phase_axis precision n (by omega)]
    cases hb : bits (Fin.last n) <;> simp [number,hb,phase_add,mul_comm]
  rw [re] at r
  simpa only [realize,g.forward,g.backward] using r

theorem realize_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index : Nat) (s : Gradient.Step) (fuel : Nat) (child : Operator)
    (bound : Gradient.Bound artifact index s)
    (ready : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel s.tailIndex = some child) :
    HierarchicalFiniteEvaluation.physical algebra leaves artifact (fuel+3) index = some (realize s child) := by
  obtain ⟨root,rootBody,enter,action,leave,phase,_,enterBody,actionBody,leaveBody,phaseBody⟩ := bound
  have pcode : physicalCode s.phase = some (.phase s.target s.numerator s.exponent,[]) := by
    simp [physicalCode,phaseBody]
  have ecode : physicalCode s.enter = some (.rewire (Structural.axisMap s.enter.interface),[]) := by
    simp [physicalCode,enterBody]
  have lcode : physicalCode s.leave = some (.rewire (Structural.axisMap s.leave.interface),[]) := by
    simp [physicalCode,leaveBody]
  have acode : physicalCode s.action = some (.tensor,[s.phaseIndex,s.tailIndex]) := by
    simp [physicalCode,actionBody]
  have rcode : physicalCode s.root = some (.sequence,[s.enterIndex,s.actionIndex,s.leaveIndex]) := by
    simp [physicalCode,rootBody]
  have childMore := HierarchicalFiniteEvaluation.evaluate_more algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) fuel s.tailIndex child ready (fuel+1) (by omega)
  have peval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact fuel s.phaseIndex s.phase _ [] phase pcode
  have aeval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1) s.actionIndex s.action _ _ action acode
  have eeval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1) s.enterIndex s.enter _ [] enter ecode
  have leval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+1) s.leaveIndex s.leave _ [] leave lcode
  have reval := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact (fuel+2) index s.root _ _ root rcode
  simp only [HierarchicalFiniteEvaluation.physical] at *
  simp only [List.mapM_nil,bind,Option.bind,pure] at peval eeval leval
  simp [peval,childMore] at aeval
  simp [eeval,leval,aeval] at reval
  exact reval

theorem empty_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (index precision : Nat) (d : Definition)
    (found : artifact.definitions[index]? = some d) (valid : Gradient.base d = true) :
    ∃ actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact 1 index = some actual ∧
      At 0 actual (fun bits => phase (number 0 bits) precision) := by
  cases body : d.body <;> simp only [Gradient.base,body,Bool.and_eq_true,Bool.false_eq_true,and_false] at valid
  rename_i map
  have widths := register_widths d 0 valid.1
  have axes : map.axes = #[] := Array.empty_of_isEmpty (by tauto)
  have code : physicalCode d = some (.rewire [],[]) := by simp [physicalCode,body,axes]
  have evaluated := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact 0 index d _ [] found code
  simp only [List.mapM_nil,bind,Option.bind,pure] at evaluated
  refine ⟨_,evaluated,widths.1,widths.2,?_⟩
  ext output input
  simp [algebra,matrixAt,apply,bounded,raw,widths.1,widths.2,number,phase,
    Matrix.diagonal_apply]
  exact Subsingleton.elim output input

theorem matched_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision n index : Nat) (enough : n ≤ precision)
    (matched : Gradient.Matches artifact precision n index) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual ∧
      At n actual (fun bits => phase (number n bits) precision) := by
  induction matched with
  | empty index d found valid =>
    obtain ⟨actual,evaluated,diagonal⟩ := empty_evaluates leaves artifact index precision d found valid
    exact ⟨1,actual,evaluated,diagonal⟩
  | step n index s bound valid _ ih =>
    obtain ⟨fuel,child,evaluated,diagonal⟩ := ih (by omega)
    exact ⟨fuel+3,realize s child,realize_evaluates leaves artifact index s fuel child bound evaluated,
      step_at precision n s child enough valid diagonal⟩

/-- Successful inspection binds the actual definition graph to the independent
little-endian integer phase. No finite-leaf or whole-graph semantic premise is
needed: this gradient consists entirely of checked structural and phase nodes. -/
theorem inspect_evaluates (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision n index remaining : Nat) (pending : Gradient.Pending)
    (accepted : Gradient.inspect artifact precision n index remaining = .ok pending) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual ∧
      At n actual (fun bits => phase (number n bits) precision) := by
  obtain ⟨_,_,_,_,enough,matched⟩ := Gradient.inspect_sound artifact precision n index remaining pending accepted
  exact matched_evaluates leaves artifact precision n index enough matched

/-- The result constrains any successful evaluation of the same actual graph,
independently of chosen fuel and arbitrary entangled reference columns. -/
theorem inspect_joint_amplitude (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision n index remaining fuel : Nat) (pending : Gradient.Pending)
    (accepted : Gradient.inspect artifact precision n index remaining = .ok pending)
    (actual : Operator)
    (evaluated : HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel index = some actual)
    {R : Type} (joint : (Fin n → Bool) → R → ℂ) (output : Fin n → Bool) (reference : R) :
    (∑ input, matrixAt n n actual output input * joint input reference) =
      phase (number n output) precision * joint output reference := by
  obtain ⟨more,value,computed,diagonal⟩ := inspect_evaluates leaves artifact precision n index remaining pending accepted
  have equal := HierarchicalFiniteEvaluation.evaluate_unique algebra
    (HierarchicalFiniteEvaluation.definition leaves artifact) more fuel index value actual computed evaluated
  subst value
  exact joint_amplitude diagonal joint output reference

/-- Bind the actual controlled repetition to an inspected gradient, removing
the previous theorem's assumed child diagonal. Finite H gates are elsewhere. -/
theorem inspect_controlled_power (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (precision n index remaining root repeated : Nat) (pending : Gradient.Pending)
    (accepted : Gradient.inspect artifact precision n index remaining = .ok pending)
    (controlled powered : Definition)
    (hc : artifact.definitions[root]? = some controlled)
    (hcb : controlled.body = .control repeated true)
    (hp : artifact.definitions[repeated]? = some powered)
    (hpb : powered.body = .repeatOp (2^(precision-(n+1))) index)
    (hi : width powered.interface.inputs = n) (ho : width powered.interface.outputs = n)
    (ci : width controlled.interface.inputs = n+1) (co : width controlled.interface.outputs = n+1)
    (enough : n+1 ≤ precision) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel root = some actual ∧
      At (n+1) actual (fun bits => if bits 0 = true then
        phase (number n (fun i => bits i.succ)) (n+1) else 1) := by
  obtain ⟨fuel,child,evaluated,diagonal⟩ := inspect_evaluates leaves artifact precision n index remaining pending accepted
  obtain ⟨actual,computed,ready⟩ := physical_controlled_gradient leaves artifact root repeated index fuel n precision
    controlled powered child (number n) hc hcb hp hpb evaluated hi ho ci co enough diagonal
  exact ⟨fuel+2,actual,computed,ready⟩

/-- The top QFT stage omits a literal repetition when its count is one. -/
theorem inspect_controlled (leaves : HierarchicalFiniteEvaluation.Leaves Operator)
    (artifact : Artifact) (n index remaining root : Nat) (pending : Gradient.Pending)
    (accepted : Gradient.inspect artifact (n+1) n index remaining = .ok pending)
    (controlled : Definition) (hc : artifact.definitions[root]? = some controlled)
    (hcb : controlled.body = .control index true)
    (ci : width controlled.interface.inputs = n+1) (co : width controlled.interface.outputs = n+1) :
    ∃ fuel actual, HierarchicalFiniteEvaluation.physical algebra leaves artifact fuel root = some actual ∧
      At (n+1) actual (fun bits => if bits 0 = true then
        phase (number n (fun i => bits i.succ)) (n+1) else 1) := by
  obtain ⟨fuel,child,evaluated,diagonal⟩ := inspect_evaluates leaves artifact (n+1) n index remaining pending accepted
  have code : physicalCode controlled = some (.control true,[index]) := by simp [physicalCode,hcb]
  have computed := HierarchicalFiniteEvaluation.physical_step algebra leaves artifact fuel root controlled _ _ hc code
  simp only [List.mapM_cons,List.mapM_nil,evaluated,bind,Option.bind,pure] at computed
  exact ⟨fuel+1,_,computed,control_at controlled.interface n true child _ ci co diagonal⟩

end Qleisli.HierarchicalGradient
