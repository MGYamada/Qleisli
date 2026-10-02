import Protocol.Hierarchical
import Protocol.FiniteCodec
import QleisliKernel.Hierarchical.FiniteBinding
import Protocol.Qirf

/-! Unproved decoding adapter for fresh VM-27 independent finite requests.
No Rust matrix, equality decision or producer receipt crosses this boundary.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Protocol.HierarchicalFinite
open QleisliKernel.Hierarchical

def basis (atoms : Artifact.Basis) : QleisliKernel.Finite.WorkM Semantics.Finite.Basis := do
  atoms.toList.mapM fun atom => match atom with
    | .unit => pure .unit | .bit => pure .bit
    | .tuple 2 => pure .pair | .tuple arity => pure (.tuple arity)
    | .bits _ => throw .request

def checkLeaf (program : ByteArray) (interface : Artifact.Interface)
    (required : Semantics.Exact.Matrix) : QleisliKernel.Finite.WorkM Unit := do
  QleisliKernel.Finite.guard (Finite.unary interface) .request
  let input ← QleisliKernel.Finite.lift (QleisliKernel.Finite.readOption interface.inputs.quantum[0]?)
  let output ← QleisliKernel.Finite.lift (QleisliKernel.Finite.readOption interface.outputs.quantum[0]?)
  let signature ← basis input.basis
  let (artifact,order) ← Qirf.read program
  let _ ← QleisliKernel.Qirf.check artifact order signature
    ⟨input.owner,input.axes.toList,Semantics.Finite.width signature⟩
    ⟨output.owner,output.axes.toList,Semantics.Finite.width signature⟩ required
  pure ()

def matrix (bytes : ByteArray) : QleisliKernel.Finite.WorkM Semantics.Exact.Matrix := do
  let text ← QleisliKernel.Finite.lift (match String.fromUTF8? bytes with
    | some text => .ok text | none => .error .invalid)
  FiniteCodec.readMatrix text

def checkRequest (request : Finite.Request) : QleisliKernel.Finite.WorkM Unit := do
  let required ← matrix request.description
  checkLeaf request.program request.physical.interface required

/-- All finite proofs, including non-root proofs, use their original QIRF1/2
bytes. No Rust import, extracted circuit or producer matrix is a premise. -/
def checkLeaves (requests : Array Finite.Request) : QleisliKernel.Finite.WorkM Unit :=
  requests.toList.foldlM (fun _ request => checkRequest request) ()

def checkHadamard (artifact : Artifact.Artifact) (expected : Semantics.Exact.Matrix)
    (index : Nat) : QleisliKernel.Finite.WorkM Unit := do
  let definition ← QleisliKernel.Finite.lift (QleisliKernel.Finite.readOption artifact.definitions[index]?)
  let program ← QleisliKernel.Finite.lift (match definition.body with
    | .leaf program => .ok program | _ => .error .invalid)
  QleisliKernel.Finite.guard (definition.effect == .unitary)
  checkLeaf program definition.interface expected

def hadamard : Semantics.Exact.Matrix :=
  let r := QleisliKernel.Finite.halfRoot
  ⟨2,2,[r,r,r,⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩]⟩

/-- H is fixed mathematically, including global phase; the producer's finite
description cannot redefine the Fourier or QPE Hadamard role. -/
def checkHadamards (artifact : Artifact.Artifact) (indices : List Nat) :
    QleisliKernel.Finite.WorkM Unit := do
  let r := QleisliKernel.Finite.halfRoot
  let negative ← QleisliKernel.Finite.lift (QleisliKernel.Finite.arithmetic (Exact.Scalar.neg r))
  let expected : Semantics.Exact.Matrix := ⟨2,2,[r,r,r,negative]⟩
  indices.foldlM (fun _ index => checkHadamard artifact expected index) ()

def checkPair (artifact : Artifact.Artifact) (request : Root.Request)
    (pairs : Array Root.Pair) (index : Nat) : QleisliKernel.Finite.WorkM Unit := do
  let pair ← QleisliKernel.Finite.lift (match Root.finitePair artifact request pairs index with
    | some pair => .ok pair | none => .error .invalid)
  let actual ← matrix pair.left
  let required ← matrix pair.right
  let left ← QleisliKernel.Finite.lift (FiniteBinding.check actual required (← get))
  set left

/-- The structural pass independently derives this complete obligation list.
Both descriptions are read from the immutable native packet, not host values. -/
def checkPairs (artifact : Artifact.Artifact) (request : Root.Request)
    (pairs : Array Root.Pair) (indices : List Nat) : QleisliKernel.Finite.WorkM Unit := do
  QleisliKernel.Finite.guard (indices == Root.obligations artifact request pairs)
  indices.foldlM (fun _ index => checkPair artifact request pairs index) ()

open QleisliKernel.Finite in
theorem fold_each {A : Type} (items : List A) (check : A → WorkM Unit) (work left : Nat)
    (ok : (items.foldlM (fun _ item => check item) ()).run work = (.ok (),left)) :
    ∀ item ∈ items, ∃ a b, (check item).run a = (.ok (),b) := by
  induction items generalizing work with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldlM_cons] at ok
    obtain ⟨value,middle,checked,remaining⟩ := bind_success _ _ _ _ _ ok
    cases value
    intro actual member
    rcases List.mem_cons.mp member with same | inside
    · subst actual; exact ⟨work,middle,checked⟩
    · exact ih middle remaining actual inside

theorem checkLeaves_each (requests : Array Finite.Request) (work left : Nat)
    (ok : (checkLeaves requests).run work = (.ok (),left)) :
    ∀ request ∈ requests.toList, ∃ a b, (checkRequest request).run a = (.ok (),b) :=
  fold_each _ _ _ _ ok

open QleisliKernel.Finite in
theorem checkLeaf_conditions (program : ByteArray) (interface : Artifact.Interface)
    (required : Semantics.Exact.Matrix) (work left : Nat)
    (ok : (checkLeaf program interface required).run work = (.ok (),left)) :
    ∃ input output signature artifact order a b c d,
      Finite.unary interface = true ∧ interface.inputs.quantum[0]? = some input ∧
      interface.outputs.quantum[0]? = some output ∧
      (basis input.basis).run a = (.ok signature,b) ∧
      (Qirf.read program).run b = (.ok (artifact,order),c) ∧
      (QleisliKernel.Qirf.reconstruct artifact order signature
        ⟨input.owner,input.axes.toList,Semantics.Finite.width signature⟩
        ⟨output.owner,output.axes.toList,Semantics.Finite.width signature⟩).run c = (.ok required,d) := by
  obtain ⟨_,w₁,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨input,w₂,hi,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨output,w₃,ho,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨signature,w₄,hb,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨decoded,w₅,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₆,hc,_⟩ := bind_success _ _ _ _ _ h
  obtain ⟨same,y,hr⟩ := QleisliKernel.Qirf.check_reconstruct _ _ _ _ _ _ _ _ _ hc
  have presentInput : interface.inputs.quantum[0]? = some input := by
    have found := (lift_success _ _ _ _ hi).1
    cases hf : interface.inputs.quantum[0]? <;> simp_all [readOption]
  have presentOutput : interface.outputs.quantum[0]? = some output := by
    have found := (lift_success _ _ _ _ ho).1
    cases hf : interface.outputs.quantum[0]? <;> simp_all [readOption]
  exact ⟨input,output,signature,decoded.1,decoded.2,w₃,w₄,w₅,y,
    (guard_success _ _ _ _ hg).1,presentInput,presentOutput,hb,hd,by simpa only [same] using hr⟩

open QleisliKernel.Finite in
theorem checkRequest_conditions (request : Finite.Request) (work left : Nat)
    (ok : (checkRequest request).run work = (.ok (),left)) :
    ∃ required middle, (matrix request.description).run work = (.ok required,middle) ∧
      (checkLeaf request.program request.physical.interface required).run middle = (.ok (),left) := by
  obtain ⟨required,middle,decoded,checked⟩ := bind_success _ _ _ _ _ ok
  exact ⟨required,middle,decoded,checked⟩

open QleisliKernel.Finite in
theorem checkPair_conditions (artifact : Artifact.Artifact) (request : Root.Request)
    (pairs : Array Root.Pair) (index work left : Nat)
    (ok : (checkPair artifact request pairs index).run work = (.ok (),left)) :
    ∃ pair actual a b c,
      Root.finitePair artifact request pairs index = some pair ∧
      (matrix pair.left).run a = (.ok actual,b) ∧
      (matrix pair.right).run b = (.ok actual,c) := by
  obtain ⟨pair,w₁,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨actual,w₂,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₃,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₄,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hb,_⟩ := bind_success _ _ _ _ _ h
  have found := (lift_success _ _ _ _ hp).1
  have present : Root.finitePair artifact request pairs index = some pair := by
    cases hf : Root.finitePair artifact request pairs index <;> simp_all
  have equal := (FiniteBinding.check_conditions _ _ _ _ (lift_success _ _ _ _ hb).1).1
  exact ⟨pair,actual,w₁,w₂,w₃,present,ha,by simpa only [equal] using hr⟩

open QleisliKernel.Finite in
theorem checkPairs_each (artifact : Artifact.Artifact) (request : Root.Request)
    (pairs : Array Root.Pair) (indices : List Nat) (work left : Nat)
    (ok : (checkPairs artifact request pairs indices).run work = (.ok (),left)) :
    indices = Root.obligations artifact request pairs ∧
      ∀ index ∈ indices, ∃ a b, (checkPair artifact request pairs index).run a = (.ok (),b) := by
  obtain ⟨_,middle,hg,h⟩ := bind_success _ _ _ _ _ ok
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hg).1,fold_each _ _ _ _ h⟩

open QleisliKernel.Finite in
theorem checkHadamard_conditions (artifact : Artifact.Artifact) (expected : Semantics.Exact.Matrix)
    (index work left : Nat) (ok : (checkHadamard artifact expected index).run work = (.ok (),left)) :
    ∃ definition program a,
      artifact.definitions[index]? = some definition ∧ definition.body = .leaf program ∧
      definition.effect = .unitary ∧ (checkLeaf program definition.interface expected).run a = (.ok (),left) := by
  obtain ⟨definition,w₁,hd,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨program,w₂,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hg,h⟩ := bind_success _ _ _ _ _ h
  have found := (lift_success _ _ _ _ hd).1
  have present : artifact.definitions[index]? = some definition := by
    cases hf : artifact.definitions[index]? <;> simp_all [readOption]
  have raw := (lift_success _ _ _ _ hp).1
  have body : definition.body = .leaf program := by
    cases hb : definition.body <;> simp_all
  have unitary : definition.effect = .unitary := by
    have effect := (guard_success _ _ _ _ hg).1
    cases he : definition.effect with
    | unitary => rfl
    | iso => rw [he] at effect; change false = true at effect; contradiction
    | observe => rw [he] at effect; change false = true at effect; contradiction
  exact ⟨definition,program,w₃,present,body,unitary,h⟩

open QleisliKernel.Finite in
theorem checkHadamards_each (artifact : Artifact.Artifact) (indices : List Nat) (work left : Nat)
    (ok : (checkHadamards artifact indices).run work = (.ok (),left)) :
    ∀ index ∈ indices, ∃ a b, (checkHadamard artifact hadamard index).run a = (.ok (),b) := by
  obtain ⟨negative,middle,hn,h⟩ := bind_success _ _ _ _ _ ok
  have exactNegative : negative = ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩ := by
    have actual := arithmetic_success _ _ (lift_success _ _ _ _ hn).1
    have fixed : Exact.Scalar.neg QleisliKernel.Finite.halfRoot =
        .ok ⟨.integer 0,⟨-1,1⟩,.integer 0,.integer 0⟩ := by rfl
    exact (Except.ok.inj (fixed.symm.trans actual)).symm
  subst negative
  exact fold_each _ _ _ _ h

def errorCode : QleisliKernel.Finite.Error → String
  | .limit | .arithmetic .workLimit | .arithmetic .arithmeticCapacity => "limit"
  | .invalid => "format"
  | _ => "contract"

end QleisliKernel.Protocol.HierarchicalFinite
