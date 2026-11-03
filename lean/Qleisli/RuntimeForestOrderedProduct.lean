import Qleisli.RuntimeForestProduct

/-! Complete ordered runtime-forest product code. Every owner contributes its
original carrier layout and ordered physical wires, including separate Unit,
Bits<0> and nominal singleton owners. Logical digits use actual cardinalities.
The complex joint amplitudes need not factor. Selected/spectator regrouping,
owner permutations, Raw program action, Gram transfer and acceptance remain
separate obligations. No joined matrix or maximum case is constructed here.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/

namespace Qleisli.RuntimeForestOrderedProduct
open QleisliKernel QleisliKernel.Semantics.Exact
open QleisliKernel.Semantics.FiniteCarrier
open QleisliKernel.Semantics.Finite (gather)
open QleisliKernel.Qirf QleisliKernel.Qirf.RuntimeForestCode
open Qleisli.Semantics.Exact
open Qleisli.RuntimeForestProduct

def layouts {bindings : RuntimeOwnerMap.Map} : OwnerCodes bindings → List Layout
  | .nil => []
  | .cons first rest => first.layout :: layouts rest

/-- A reference layout used only in the erased structural proof. The executable
code coordinates and coefficient product below do not allocate this label list. -/
def layoutProduct {bindings : RuntimeOwnerMap.Map} (owners : OwnerCodes bindings) : Layout :=
  (layouts owners).foldr tensor QleisliKernel.Semantics.FiniteCarrier.singleton

def sparseProduct {bindings : RuntimeOwnerMap.Map} : OwnerCodes bindings → Sparse
  | .nil => Sparse.singleton
  | .cons first rest => (Sparse.ofLayout first.layout).tensor (sparseProduct rest)

theorem layouts_length {bindings} (owners : OwnerCodes bindings) : (layouts owners).length = bindings.length := by
  induction owners with
  | nil => rfl
  | cons first rest ih => simpa only [layouts,List.length_cons] using congrArg Nat.succ ih

theorem product_agrees {bindings} (owners : OwnerCodes bindings) :
    Agrees (sparseProduct owners) (layoutProduct owners) := by
  induction owners with
  | nil => exact ofLayout_agrees _
  | cons first rest ih => exact tensor_agrees (ofLayout_agrees first.layout) ih

private theorem tensor_left (code : Layout) : tensor QleisliKernel.Semantics.FiniteCarrier.singleton code = code := by
  cases code
  simp [QleisliKernel.Semantics.FiniteCarrier.tensor,QleisliKernel.Semantics.FiniteCarrier.singleton]

private theorem tensor_right (code : Layout) : tensor code QleisliKernel.Semantics.FiniteCarrier.singleton = code := by
  cases code
  simp [QleisliKernel.Semantics.FiniteCarrier.tensor,QleisliKernel.Semantics.FiniteCarrier.singleton]

private theorem tensor_assoc (first second third : Layout) :
    tensor (tensor first second) third = tensor first (tensor second third) := by
  have labels : (tensor (tensor first second) third).labels = (tensor first (tensor second third)).labels := by
    dsimp only [QleisliKernel.Semantics.FiniteCarrier.tensor]
    simp only [List.map_flatMap,List.map_map,List.flatMap_assoc,List.flatMap_map,Function.comp_def]
    apply congrArg (fun f : Nat → List Nat => third.labels.flatMap f)
    funext high
    apply congrArg (fun f : Nat → List Nat => second.labels.flatMap f)
    funext middle
    apply congrArg (fun f : Nat → Nat => first.labels.map f)
    funext low
    rw [Nat.pow_add]
    ring
  exact congr (congrArg Layout.mk (Nat.add_assoc first.bits second.bits third.bits)) labels

private theorem foldl_tensor (codes : List Layout) (initial : Layout) :
    codes.foldl tensor initial = tensor initial (codes.foldr tensor QleisliKernel.Semantics.FiniteCarrier.singleton) := by
  induction codes generalizing initial with
  | nil => exact (tensor_right initial).symm
  | cons first rest ih =>
    change rest.foldl tensor (tensor initial first) =
      tensor initial (tensor first (rest.foldr tensor QleisliKernel.Semantics.FiniteCarrier.singleton))
    rw [ih]
    exact tensor_assoc initial first _

private theorem foldl_product (codes : List Layout) :
    codes.foldl tensor QleisliKernel.Semantics.FiniteCarrier.singleton =
      codes.foldr tensor QleisliKernel.Semantics.FiniteCarrier.singleton :=
  (foldl_tensor codes _).trans (tensor_left _)

/-- Each original owner tree pushes its own layout over the unchanged
continuation. No malformed owner can borrow another owner's source nodes. -/
theorem concat_original {bindings} (owners : OwnerCodes bindings) (suffix : List Layout) :
    (bindings.flatMap (fun binding => binding.owner.basis)).foldr layoutStep (some suffix) =
      some (layouts owners ++ suffix) := by
  induction owners generalizing suffix with
  | nil => rfl
  | @cons binding bindings first rest ih =>
    simp only [List.flatMap_cons,List.foldr_append,layouts]
    rw [ih]
    exact layout_continuation binding.owner.basis first.layout first.reference.1 (layouts rest ++ suffix)

/-- The complete original forest interpretation follows from the actual read
of every ordered owner. Tensor laws are proved above; no forest equality is a
supplied premise and no physical width identifies a source type. -/
theorem forest_original {bindings} (owners : OwnerCodes bindings) :
    QleisliKernel.Semantics.FiniteCarrier.layout (forestBasis bindings) = some (layoutProduct owners) := by
  cases owners with
  | nil => rfl
  | @cons firstBinding firstBindings first rest =>
    cases rest with
    | nil =>
      simpa only [forestBasis,carrierOwners,List.map_cons,List.map_nil,
        QleisliKernel.Semantics.CarrierInterface.forest,layoutProduct,layouts,List.foldr_cons,List.foldr_nil,tensor_right]
        using first.reference.1
    | @cons secondBinding secondBindings second tail =>
      cases tail with
      | nil =>
        simpa only [forestBasis,carrierOwners,List.map_cons,List.map_nil,
          QleisliKernel.Semantics.CarrierInterface.forest,layoutProduct,layouts,List.foldr_cons,List.foldr_nil,tensor_right]
          using layout_pair_reference firstBinding.owner.basis secondBinding.owner.basis
            first.layout second.layout first.reference.1 second.reference.1
      | @cons thirdBinding bindings third rest =>
        let all : OwnerCodes (firstBinding::secondBinding::thirdBinding::bindings) :=
          .cons first (.cons second (.cons third rest))
        have shape : forestBasis (firstBinding::secondBinding::thirdBinding::bindings) =
            .tuple (firstBinding::secondBinding::thirdBinding::bindings).length ::
              (firstBinding::secondBinding::thirdBinding::bindings).flatMap (fun binding => binding.owner.basis) := by
          simp only [forestBasis,carrierOwners,List.map_cons,QleisliKernel.Semantics.CarrierInterface.forest,
            List.length_map,List.flatMap_map,Function.comp_def,List.flatMap_cons]
        have stackRead :
            ((firstBinding::secondBinding::thirdBinding::bindings).flatMap (fun binding => binding.owner.basis)).foldr
              layoutStep (some []) = some (layouts all) := by
          simpa only [List.append_nil] using concat_original all []
        have rootRead : layoutStep (.tuple (firstBinding::secondBinding::thirdBinding::bindings).length)
            (some (layouts all)) =
              some [(layouts all).foldr tensor QleisliKernel.Semantics.FiniteCarrier.singleton] := by
          rw [← layouts_length all]
          simp only [layoutStep,children,bind,Option.bind,Nat.lt_irrefl,if_false,
            List.take_length,List.drop_length,foldl_product]
        change QleisliKernel.Semantics.FiniteCarrier.layout
          (forestBasis (firstBinding::secondBinding::thirdBinding::bindings)) = some (layoutProduct all)
        simp only [QleisliKernel.Semantics.FiniteCarrier.layout,shape,List.foldr_cons,stackRead,rootRead,
          bind,Option.bind,pure,layoutProduct]

/-- This same Frame's original whole-code receipt agrees with the product
derived from its complete retained ordered owner reads. -/
theorem frame_product_agrees {roles state checked} (frame : @Frame roles state checked) :
    Agrees frame.code (layoutProduct frame.owners) := by
  obtain ⟨layout,original,same⟩ := frame.originalCode
  have equal : layout = layoutProduct frame.owners :=
    Option.some.inj (original.symm.trans (forest_original frame.owners))
  subst layout
  exact same

private theorem agrees_entry {code : Sparse} {layout : Layout} (same : Agrees code layout)
    (physical logical : Nat) : sparseEntry code physical logical = sparseEntry (.ofLayout layout) physical logical := by
  exact congrArg (fun coordinate : Option Nat => if coordinate == some physical then Scalar.one else Scalar.zero)
    (same.labels logical)

private theorem layout_tensor_coefficient (left right : Layout) (valid : LayoutBounds left)
    (low high logical : Nat) (bound : low < 2^left.bits) :
    scalar (sparseEntry (.ofLayout (tensor left right)) (low+2^left.bits*high) logical) =
      scalar (sparseEntry (.ofLayout left) low (logical % left.labels.length)) *
        scalar (sparseEntry (.ofLayout right) high (logical / left.labels.length)) := by
  rw [← agrees_entry (tensor_agrees (ofLayout_agrees left) (ofLayout_agrees right))]
  exact tensor_coefficient left right valid low high logical bound

/-- Every mixed-radix digit uses this exact owner's logical cardinality. The
tail keeps all remaining identities and zero-width owner positions. -/
noncomputable def coefficients (frame : List Nat) {bindings : RuntimeOwnerMap.Map}
    (owners : OwnerCodes bindings) (physical logical : Nat) : ℂ :=
  match owners with
  | .nil => if logical = 0 then 1 else 0
  | @OwnerCodes.cons binding _ first rest =>
    entry (QleisliKernel.Semantics.FiniteCarrier.encoding first.layout)
      (gather physical (binding.port.wires.map frame.idxOf)) (logical % first.layout.labels.length) *
        coefficients frame rest physical (logical / first.layout.labels.length)

theorem product_coefficient (frame : List Nat) {bindings} (owners : OwnerCodes bindings)
    (physical logical : Nat) (bound : logical < (sparseProduct owners).dimension) :
    scalar (sparseEntry (.ofLayout (layoutProduct owners)) (gather physical (forestAxes frame bindings)) logical) =
      coefficients frame owners physical logical := by
  induction owners generalizing physical logical with
  | nil =>
    have zero : logical = 0 := by
      change logical < 1 at bound
      omega
    subst logical
    simp [layoutProduct,layouts,forestAxes,gather,sparseEntry,Sparse.ofLayout,
      QleisliKernel.Semantics.FiniteCarrier.singleton,coefficients,Qleisli.Exact.scalar_one_meaning]
  | @cons binding bindings first rest ih =>
    have axes : forestAxes frame (binding::bindings) =
        binding.port.wires.map frame.idxOf ++ forestAxes frame bindings := by
      simp only [forestAxes,List.flatMap_cons,List.map_append]
    have lowRow : gather physical (binding.port.wires.map frame.idxOf) < 2^first.layout.bits := by
      simpa only [List.length_map,first.reference.2.2] using
        gather_bound physical (binding.port.wires.map frame.idxOf)
    have lowCol : logical % first.layout.labels.length < first.layout.labels.length :=
      Nat.mod_lt _ (owner_bounds first).1
    have tailBound : logical / first.layout.labels.length < (sparseProduct rest).dimension :=
      Nat.div_lt_of_lt_mul bound
    change scalar (sparseEntry (.ofLayout (tensor first.layout (layoutProduct rest)))
        (gather physical (forestAxes frame (binding::bindings))) logical) = _
    rw [axes,gather_append,List.length_map,first.reference.2.2,
      layout_tensor_coefficient first.layout (layoutProduct rest) (owner_bounds first) _ _ logical lowRow,
      encoding_coefficient first.layout _ _ lowRow lowCol,ih physical _ tailBound]
    rfl

/-- Every factor refers to its own original owner and actual Raw wire order.
There is no supplied selected/spectator partition or tensor-state assumption. -/
theorem ordered_product_entry {roles state checked} (frame : @Frame roles state checked)
    (physical logical : Nat) (bound : logical < frame.code.dimension) :
    scalar (frame.embedding physical logical) = coefficients state.quantum.frame frame.owners physical logical := by
  change scalar (sparseEntry frame.code (gather physical (forestAxes state.quantum.frame checked.bindings)) logical) = _
  rw [agrees_entry (frame_product_agrees frame)]
  apply product_coefficient
  rw [(product_agrees frame.owners).dimension,← (frame_product_agrees frame).dimension]
  exact bound

/-- Sum the actual complete ordered coefficient product against an arbitrary
joint logical/reference family. No bounded arithmetic sum is rearranged. -/
theorem ordered_product_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    referenceAction frame joint physical reference =
      ((List.range frame.code.dimension).map fun logical =>
        coefficients state.quantum.frame frame.owners physical logical * joint logical reference).sum := by
  unfold referenceAction
  apply Qleisli.Exact.sum_map_congr
  intro logical member
  rw [ordered_product_entry frame physical logical (List.mem_range.mp member)]

theorem axes_length (frame : List Nat) {bindings} (owners : OwnerCodes bindings) :
    (forestAxes frame bindings).length = (sparseProduct owners).bits := by
  induction owners with
  | nil => rfl
  | @cons binding bindings first rest ih =>
    change (forestAxes frame (binding::bindings)).length = first.layout.bits+(sparseProduct rest).bits
    simp only [forestAxes,List.flatMap_cons,List.map_append,List.length_append,List.length_map] at ih ⊢
    rw [first.reference.2.2,ih]

/-- The physical coordinate bound is derived from every actual port-width
receipt; it does not ask for a promise about the joint input amplitudes. -/
theorem frame_axes_length {roles state checked} (frame : @Frame roles state checked) :
    (forestAxes state.quantum.frame checked.bindings).length = frame.code.bits :=
  (axes_length _ frame.owners).trans
    ((product_agrees frame.owners).bits.trans (frame_product_agrees frame).bits.symm)

/-- When this exact complete forest has a native ownerCode execution, retain
that successful receipt and derive its total-complex ordered product action.
This conditional theorem grants no joined-code availability at a larger width. -/
theorem ordered_native_action {Reference : Type} {roles state checked} (frame : @Frame roles state checked)
    (native : Matrix) (before after : Nat)
    (ran : (Carrier.ownerCode (carrierOwners checked.bindings)).run before = (.ok native,after))
    (joint : Nat → Reference → ℂ) (physical : Nat) (reference : Reference) :
    action native joint (gather physical (forestAxes state.quantum.frame checked.bindings)) reference =
      ((List.range frame.code.dimension).map fun logical =>
        coefficients state.quantum.frame frame.owners physical logical * joint logical reference).sum := by
  have bound : gather physical (forestAxes state.quantum.frame checked.bindings) < 2^frame.code.bits := by
    rw [← frame_axes_length frame]
    exact gather_bound _ _
  exact (ownerCode_reference_action frame native before after ran joint physical reference bound).trans
    (ordered_product_action frame joint physical reference)

#print axioms forest_original
#print axioms ordered_product_entry
#print axioms ordered_product_action
#print axioms ordered_native_action

end Qleisli.RuntimeForestOrderedProduct
