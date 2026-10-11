import Qleisli.Raw
import Qleisli.Semantics.Raw

/-! Complete complex denotation of the actual bounded pure raw checker. Every
event, clean physical body, dependency action and final output permutation is
read from the original raw operations. No Rust checking/extraction is assumed.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Raw
open QleisliKernel.Semantics.Exact QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Raw
open QleisliKernel.Raw QleisliKernel.Finite Qleisli.Semantics.Exact Qleisli.Semantics.Raw

theorem circuit_denotes (dependencies : List Dependency) (bits : Nat) (steps : List Step)
    (actual : Matrix) (work left : Nat)
    (ok : (circuitMatrix dependencies (circuit bits steps)).run work = (.ok actual,left)) :
    CircuitMeaning dependencies bits steps actual := by
  have width_register (bits : Nat) : width (QleisliKernel.Semantics.Raw.registerBasis bits) = bits := by
    induction bits with
    | zero => rfl
    | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
        simp [QleisliKernel.Semantics.Raw.registerBasis,width] at ih ⊢
        omega
  simpa only [CircuitMeaning,BasisColumn,circuit,QleisliKernel.Raw.registerBasis,width_register] using
    Finite.circuitMatrix_trace dependencies (circuit bits steps) actual work left ok

theorem mapping_denotes (inputBits outputBits : Nat) (labels : List Nat) (actual : Matrix)
    (work left : Nat) (ok : (mapping inputBits outputBits labels).run work = (.ok actual,left)) :
    MapMeaning inputBits outputBits labels actual := by
  have shape := mapping_value _ _ _ _ _ _ ok
  have rows : actual.rows = 2^outputBits := congrArg Matrix.rows shape
  have cols : actual.cols = 2^inputBits := congrArg Matrix.cols shape
  exact ⟨rows,cols,fun row col hr hc => mapping_meaning _ _ _ _ _ _ ok row col (rows ▸ hr) (cols ▸ hc)⟩

theorem promote_denotes (bits : Nat) (axes : List Nat) (logical actual : Matrix)
    (work left : Nat) (ok : (promote bits axes logical).run work = (.ok actual,left)) :
    Embedded bits axes logical actual := by
  have shape := promote_value _ _ _ _ _ _ ok
  have rows : actual.rows = 2^bits := congrArg Matrix.rows shape
  have cols : actual.cols = 2^bits := congrArg Matrix.cols shape
  exact ⟨rows,cols,fun row col hr hc => promote_meaning _ _ _ _ _ _ ok row col (rows ▸ hr) (cols ▸ hc)⟩

theorem clean_denotes (dependencies : List Dependency) (sourceBits dataBits ancillaBits : Nat)
    (function : List Nat) (uses logicalSteps : List Step) (logical : Matrix) (work left : Nat)
    (ok : (clean dependencies sourceBits dataBits ancillaBits function uses logicalSteps).run work = (.ok logical,left)) :
    CleanMeaning dependencies sourceBits dataBits ancillaBits function uses logicalSteps logical := by
  rcases clean_conditions _ _ _ _ _ _ _ _ _ _ ok with ⟨encoding,physical,w₁,w₂,w₃,w₄,w₅,w₆,hl,he,hp⟩
  rcases zeroEncoding_value _ _ _ _ _ he with ⟨before,after,w₇,w₈,hm⟩
  have checked := Finite.check_encoded _ _ _ _ _ _ _ hp
  have physicalCircuit := QleisliKernel.Finite.check_conditions _ _ _ _ _ _ _ hp
  rcases physicalCircuit with ⟨_,_,_,_,_,_,cw,aw,_,_,_,_,hbody,_,_,_⟩
  refine ⟨circuit_denotes _ _ _ _ _ _ hl,encoding.map,physical,mapping_denotes _ _ _ _ _ _ hm,
    circuit_denotes _ _ _ _ _ _ hbody,?_⟩
  simpa only [before,after] using checked.2

theorem physicalUse_reference (sourceBits dataBits : Nat) (use : Use) :
    physicalUse sourceBits dataBits use = QleisliKernel.Semantics.Protected.physical sourceBits dataBits use := by
  cases use <;> rfl

theorem logicalUse_reference (sourceBits : Nat) (function : List Nat) (use : Use) :
    logicalUse sourceBits function use = QleisliKernel.Semantics.Protected.logical sourceBits function use := by
  cases use <;> rfl

theorem event_denotes (dependencies : List Dependency) (event : Event) (actual : Matrix)
    (work left : Nat) (ok : (eventMatrix dependencies event).run work = (.ok actual,left)) :
    EventMeaning dependencies event actual := by
  cases event with
  | circuit bits steps =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,middle,_,hc⟩
    exact circuit_denotes _ _ _ _ _ _ hc
  | init0 bits =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,middle,_,hm⟩
    exact mapping_denotes _ _ _ _ _ _ hm
  | liftBasis before after inputAxes outputAxes table =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,middle,_,hm⟩
    exact mapping_denotes _ _ _ _ _ _ hm
  | reorder bits axes =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,middle,_,hm⟩
    exact mapping_denotes _ _ _ _ _ _ hm
  | computed bits axes sourceBits ancillaBits function uses logicalSteps =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,w₁,_,h⟩
    rcases bind_success _ _ _ _ _ h with ⟨logical,w₂,hc,hp⟩
    exact ⟨logical,clean_denotes _ _ _ _ _ _ _ _ _ _ hc,promote_denotes _ _ _ _ _ _ hp⟩
  | protectedComputed bits axes sourceBits ancillaBits function uses =>
    rcases bind_success _ _ _ _ _ ok with ⟨_,w₁,_,h⟩
    rcases bind_success _ _ _ _ _ h with ⟨_,w₂,_,h⟩
    rcases bind_success _ _ _ _ _ h with ⟨logical,w₃,hc,hp⟩
    refine ⟨logical,Or.inl ?_,promote_denotes _ _ _ _ _ _ hp⟩
    simpa only [physicalUse_reference,logicalUse_reference] using
      clean_denotes _ _ _ _ _ _ _ _ _ _ hc

theorem events_denote (dependencies : List Dependency) (events : List Event) (initial actual : Matrix)
    (work left : Nat) (ok : (events.foldlM (evolve dependencies) initial).run work = (.ok actual,left)) :
    EventsMeaning dependencies events initial actual := by
  induction events generalizing initial work with
  | nil =>
    simp only [List.foldlM_nil] at ok
    rw [(pure_success _ _ _ _ ok).1]
    exact .nil _
  | cons event events ih =>
    simp only [List.foldlM_cons] at ok
    rcases bind_success _ _ _ _ _ ok with ⟨next,middle,hn,he⟩
    rcases evolve_conditions _ _ _ _ _ _ hn with ⟨localMap,before,hl,hc⟩
    exact .cons _ _ _ _ _ _ (event_denotes _ _ _ _ _ hl)
      (Exact.compose_meaning _ _ _ _ _ hc) (ih next middle he)

/-- Actual executable acceptance gives the complete original complex raw
denotation, rather than merely a Gram certificate for an extracted matrix. -/
theorem reconstruct_denotes (dependencies : List Dependency) (program : Program) (actual : Matrix)
    (work left : Nat) (ok : (reconstruct dependencies program).run work = (.ok actual,left)) :
    ProgramMeaning dependencies program actual := by
  rcases reconstruct_original _ _ _ _ _ ok with ⟨trace,initial,w₁,w₂,w₃,w₄,hr,hi,he,_⟩
  rcases Exact.identity_meaning _ _ hi with ⟨_,rows,cols,entries⟩
  exact ⟨trace,initial,hr,⟨rows,cols,fun row col hrow hcol => entries row col (rows ▸ hrow) (cols ▸ hcol)⟩,
    events_denote _ _ _ _ _ _ he⟩

end Qleisli.Raw
