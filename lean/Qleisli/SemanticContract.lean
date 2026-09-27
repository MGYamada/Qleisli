import Qleisli.Kraus
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
General, exact algebra for semantic-contract composition. Matrices are meanings,
not an executable representation of the proposed symbolic evidence kernel.
The rules below manipulate equalities without evaluating matrix entries.

Rows index outputs and columns index inputs. Tensor indices are ordered pairs:
`(A ⊗ₖ B) (a,b) (a',b') = A a a' * B b b'`. There is no flattening here.
To match Rust's low-left convention, flatten `(a,b)` as `a + |A| * b`;
the usual high-left flattening is a different coordinate map. Control uses a
tagged sum of two copies, with `Sum.inl` inactive and `Sum.inr` active. Relating
these coordinates to Rust bit indices remains an implementation obligation.

These lemmas establish local mathematical rules, not Rust checker correctness,
source-to-IR preservation, an executable evidence format, or a release API.
Ownership, entry-state preparation, operation access, and actual IR binding
are separate premises outside this module.
-/

namespace Qleisli.SemanticContract

open scoped Matrix Kronecker

variable {A B C P Q R A' B' P' Q' Ref : Type*}

/-- Exact, phase-sensitive meaning on an explicitly encoded input space.
This equation alone does not assert isometry, ownership, or input preparation. -/
def Encoded [Fintype P] [Fintype B]
    (U : Matrix Q P ℂ) (Ein : Matrix P A ℂ)
    (Eout : Matrix Q B ℂ) (u : Matrix B A ℂ) : Prop :=
  U * Ein = Eout * u

/-- An isometry on the entire stated domain, including every reference extension. -/
def Isometry [Fintype B] [DecidableEq A] (U : Matrix B A ℂ) : Prop :=
  Uᴴ * U = 1

/-- A unitary between the stated finite interfaces; both inverse equations are explicit. -/
def Unitary [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Matrix B A ℂ) : Prop :=
  Isometry U ∧ U * Uᴴ = 1

theorem encoded_identity [Fintype P] [Fintype A]
    [DecidableEq P] [DecidableEq A] (E : Matrix P A ℂ) :
    Encoded 1 E E 1 := by
  simp [Encoded]

/-- The middle encoding is the same matrix with the same typed coordinates. -/
theorem encoded_seq [Fintype P] [Fintype Q] [Fintype A]
    [Fintype B] [Fintype C]
    (U₁ : Matrix Q P ℂ) (U₂ : Matrix R Q ℂ)
    (E₀ : Matrix P A ℂ) (E₁ : Matrix Q B ℂ) (E₂ : Matrix R C ℂ)
    (u₁ : Matrix B A ℂ) (u₂ : Matrix C B ℂ)
    (h₁ : Encoded U₁ E₀ E₁ u₁) (h₂ : Encoded U₂ E₁ E₂ u₂) :
    Encoded (U₂ * U₁) E₀ E₂ (u₂ * u₁) := by
  unfold Encoded at h₁ h₂ ⊢
  calc
    (U₂ * U₁) * E₀ = U₂ * (U₁ * E₀) := Matrix.mul_assoc _ _ _
    _ = U₂ * (E₁ * u₁) := by rw [h₁]
    _ = (U₂ * E₁) * u₁ := (Matrix.mul_assoc _ _ _).symm
    _ = (E₂ * u₂) * u₁ := by rw [h₂]
    _ = E₂ * (u₂ * u₁) := Matrix.mul_assoc _ _ _

theorem encoded_tensor [Fintype P] [Fintype P'] [Fintype B] [Fintype B']
    (U : Matrix Q P ℂ) (V : Matrix Q' P' ℂ)
    (Ein : Matrix P A ℂ) (Eout : Matrix Q B ℂ) (u : Matrix B A ℂ)
    (Fin : Matrix P' A' ℂ) (Fout : Matrix Q' B' ℂ) (v : Matrix B' A' ℂ)
    (hU : Encoded U Ein Eout u) (hV : Encoded V Fin Fout v) :
    Encoded (U ⊗ₖ V) (Ein ⊗ₖ Fin) (Eout ⊗ₖ Fout) (u ⊗ₖ v) := by
  unfold Encoded at hU hV ⊢
  rw [← Matrix.mul_kronecker_mul, hU, hV, Matrix.mul_kronecker_mul]

/-- Equality on a complete tensor space, with no product-state assumption. -/
theorem encoded_reference [Fintype P] [Fintype B]
    [Fintype Ref] [DecidableEq Ref]
    (U : Matrix Q P ℂ) (Ein : Matrix P A ℂ)
    (Eout : Matrix Q B ℂ) (u : Matrix B A ℂ)
    (h : Encoded U Ein Eout u) :
    Encoded (U ⊗ₖ (1 : Matrix Ref Ref ℂ)) (Ein ⊗ₖ (1 : Matrix Ref Ref ℂ))
      (Eout ⊗ₖ (1 : Matrix Ref Ref ℂ)) (u ⊗ₖ (1 : Matrix Ref Ref ℂ)) :=
  encoded_tensor U 1 Ein Eout u 1 1 1 h (encoded_identity 1)

theorem isometry_identity [Fintype A] [DecidableEq A] :
    Isometry (1 : Matrix A A ℂ) := by
  simp [Isometry]

theorem isometry_seq [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B]
    (U : Matrix B A ℂ) (V : Matrix C B ℂ)
    (hU : Isometry U) (hV : Isometry V) : Isometry (V * U) :=
  Qleisli.Kraus.isometry_comp U V hU hV

theorem isometry_tensor [Fintype B] [Fintype B']
    [DecidableEq A] [DecidableEq A']
    (U : Matrix B A ℂ) (V : Matrix B' A' ℂ)
    (hU : Isometry U) (hV : Isometry V) : Isometry (U ⊗ₖ V) := by
  unfold Isometry at hU hV ⊢
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]

theorem unitary_identity [Fintype A] [DecidableEq A] :
    Unitary (1 : Matrix A A ℂ) := by
  exact ⟨isometry_identity, by simp⟩

theorem unitary_seq [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (U : Matrix B A ℂ) (V : Matrix C B ℂ)
    (hU : Unitary U) (hV : Unitary V) : Unitary (V * U) := by
  refine ⟨isometry_seq U V hU.1 hV.1, ?_⟩
  rw [Matrix.conjTranspose_mul]
  calc
    (V * U) * (Uᴴ * Vᴴ) = V * (U * Uᴴ) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU.2, Matrix.mul_one, hV.2]

theorem unitary_tensor [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']
    (U : Matrix B A ℂ) (V : Matrix B' A' ℂ)
    (hU : Unitary U) (hV : Unitary V) : Unitary (U ⊗ₖ V) := by
  refine ⟨isometry_tensor U V hU.1 hV.1, ?_⟩
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU.2, hV.2,
    Matrix.one_kronecker_one]

theorem unitary_adjoint [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Matrix B A ℂ) (hU : Unitary U) : Unitary Uᴴ := by
  constructor
  · simpa [Isometry] using hU.2
  · simpa using hU.1

/-- The physical left-inverse and logical right-inverse are the crucial premises.
The stronger `Unitary` assumptions provide both; a logical isometry alone does not. -/
theorem encoded_adjoint [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
    [DecidableEq P] [DecidableEq Q] [DecidableEq A] [DecidableEq B]
    (U : Matrix Q P ℂ) (Ein : Matrix P A ℂ)
    (Eout : Matrix Q B ℂ) (u : Matrix B A ℂ)
    (h : Encoded U Ein Eout u) (hU : Unitary U) (hu : Unitary u) :
    Encoded Uᴴ Eout Ein uᴴ := by
  unfold Encoded at h ⊢
  calc
    Uᴴ * Eout = Uᴴ * Eout * (u * uᴴ) := by rw [hu.2, Matrix.mul_one]
    _ = Uᴴ * (Eout * u) * uᴴ := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * (U * Ein) * uᴴ := by rw [← h]
    _ = Ein * uᴴ := by rw [← Matrix.mul_assoc Uᴴ U Ein, hU.1, Matrix.one_mul]

/-- Coherent control over two tagged copies of the same target interface. -/
def control [DecidableEq P] (U : Matrix P P ℂ) : Matrix (P ⊕ P) (P ⊕ P) ℂ :=
  Matrix.fromBlocks 1 0 0 U

/-- The same exact encoding in both control sectors. -/
def controlEncoding (E : Matrix P A ℂ) : Matrix (P ⊕ P) (A ⊕ A) ℂ :=
  Matrix.fromBlocks E 0 0 E

theorem encoded_control [Fintype P] [Fintype A]
    [DecidableEq P] [DecidableEq A]
    (U : Matrix P P ℂ) (E : Matrix P A ℂ) (u : Matrix A A ℂ)
    (h : Encoded U E E u) :
    Encoded (control U) (controlEncoding E) (controlEncoding E) (control u) := by
  unfold Encoded at h ⊢
  simp only [control, controlEncoding, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, h]

theorem isometry_controlEncoding [Fintype P] [DecidableEq A]
    (E : Matrix P A ℂ) (hE : Isometry E) : Isometry (controlEncoding E) := by
  unfold Isometry at hE ⊢
  simp [controlEncoding, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, hE, Matrix.fromBlocks_one]

theorem unitary_control [Fintype P] [DecidableEq P]
    (U : Matrix P P ℂ) (hU : Unitary U) : Unitary (control U) := by
  rcases hU with ⟨hleft, hright⟩
  unfold Isometry at hleft
  constructor <;> simp [Isometry, control, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, hleft, hright, Matrix.fromBlocks_one]

/-- Abstract compute/use/uncompute factorization. To interpret this as zero
return, instantiate `E₀` with a specified zero-preparation encoding. -/
theorem compute_uncompute [Fintype P] [Fintype A] [DecidableEq P]
    (C W : Matrix P P ℂ) (E₀ : Matrix P A ℂ) (u : Matrix A A ℂ)
    (hC : Isometry C) (hW : Encoded W (C * E₀) (C * E₀) u) :
    Encoded (Cᴴ * W * C) E₀ E₀ u := by
  unfold Encoded at hW ⊢
  calc
    (Cᴴ * W * C) * E₀ = Cᴴ * (W * (C * E₀)) := by
      simp only [Matrix.mul_assoc]
    _ = Cᴴ * ((C * E₀) * u) := by rw [hW]
    _ = (Cᴴ * C) * E₀ * u := by simp only [Matrix.mul_assoc]
    _ = E₀ * u := by rw [hC, Matrix.one_mul]

/-- A designated zero-ancilla encoding with the data component first. -/
def zeroEncoding [DecidableEq A] [DecidableEq B] (zero : B) :
    Matrix (A × B) A ℂ :=
  fun output input => if output.2 = zero then (1 : Matrix A A ℂ) output.1 input else 0

theorem zeroEncoding_isometry [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (zero : B) :
    Isometry (zeroEncoding (A := A) zero) := by
  classical
  ext i j
  simp [zeroEncoding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, eq_comm]

/-- Exact zero return means every nonzero-ancilla output amplitude is zero,
for every logical input column. Reference extension is supplied above. -/
theorem encoded_zero_leakage [Fintype P] [Fintype A]
    [DecidableEq A] [DecidableEq B]
    (U : Matrix (A × B) P ℂ) (Ein : Matrix P A ℂ)
    (u : Matrix A A ℂ) (zero : B)
    (h : Encoded U Ein (zeroEncoding zero) u)
    (a : A) (b : B) (input : A) (hb : b ≠ zero) :
    (U * Ein) (a, b) input = 0 := by
  rw [h]
  simp [Matrix.mul_apply, zeroEncoding, hb]

theorem compute_uncompute_zero_leakage [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C W : Matrix (A × B) (A × B) ℂ) (u : Matrix A A ℂ) (zero : B)
    (hC : Isometry C)
    (hW : Encoded W (C * zeroEncoding zero) (C * zeroEncoding zero) u)
    (a : A) (b : B) (input : A) (hb : b ≠ zero) :
    ((Cᴴ * W * C) * zeroEncoding (A := A) zero) (a, b) input = 0 :=
  encoded_zero_leakage _ _ u zero (compute_uncompute C W _ u hC hW) a b input hb

section Derivation

variable [Fintype P] [Fintype A] [DecidableEq P] [DecidableEq A]

/-- A small proof-tree model for reuse, identity, sequencing, and qualified
adjoint at one shared encoding. This is not a serialized certificate checker.
Tensor and control change the interface and have separate theorems above. -/
inductive SameEncodingDerivation
    (Leaf : Matrix P P ℂ → Matrix A A ℂ → Prop) (E : Matrix P A ℂ) :
    Matrix P P ℂ → Matrix A A ℂ → Prop where
  | leaf {U u} : Leaf U u → SameEncodingDerivation Leaf E U u
  | identity : SameEncodingDerivation Leaf E 1 1
  | seq {U V u v} : SameEncodingDerivation Leaf E U u →
      SameEncodingDerivation Leaf E V v → SameEncodingDerivation Leaf E (V * U) (v * u)
  | adjoint {U u} : SameEncodingDerivation Leaf E U u → Unitary U → Unitary u →
      SameEncodingDerivation Leaf E Uᴴ uᴴ

/-- Induction discharges composite equalities from independently justified leaves.
It neither assumes the conclusion at composition nodes nor checks a Rust artifact. -/
theorem derivation_sound
    (Leaf : Matrix P P ℂ → Matrix A A ℂ → Prop) (E : Matrix P A ℂ)
    (leaf_sound : ∀ U u, Leaf U u → Encoded U E E u)
    {U : Matrix P P ℂ} {u : Matrix A A ℂ}
    (derivation : SameEncodingDerivation Leaf E U u) : Encoded U E E u := by
  induction derivation with
  | leaf h => exact leaf_sound _ _ h
  | identity => exact encoded_identity E
  | seq _ _ ih₁ ih₂ => exact encoded_seq _ _ E E E _ _ ih₁ ih₂
  | adjoint _ hU hu ih => exact encoded_adjoint _ E E _ ih hU hu

end Derivation

end Qleisli.SemanticContract
