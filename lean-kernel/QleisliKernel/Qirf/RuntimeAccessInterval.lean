import QleisliKernel.Qirf.RuntimePureInterval
import QleisliKernel.Qirf.ControlAccess
import QleisliKernel.SourceTypes.AccessSyntax

/-! Bind independently read access operands to an actual ordered local Raw
call. The caller supplies the lexical frame and static environment; binding
those and the extraction/restoration to the original enclosing body is separate.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeAccessInterval
open QleisliKernel Finite
open SourceTypes.AccessSyntax
open QleisliKernel.Semantics.SourceNatural (Names Calls)

def carrier : Semantics.Finite.Atom → Semantics.FiniteCarrier.Atom
  | .unit => .unit
  | .bit => .bit
  | .bits n => .bits n
  | .pair => .pair
  | .tuple n => .tuple n

def roles (places : List Place) : List Semantics.SourceOwners.Owner :=
  places.zipIdx.map fun (place,index) => ⟨index,place.basis.map carrier⟩

def controlAxes (places : List Place) : List Nat :=
  (places.foldl (fun (offset,axes) place =>
    (offset+place.axes.length, if place.role == .ctrl then
      axes ++ (List.range place.axes.length).map (offset+·) else axes)) (0,[])).2

structure Checked {tokens dependencies program} (call : CheckedCall tokens)
    (lookup : String → Option Owner) (names : Names) (calls : Calls)
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (inputs outputs : List Nat) where
  places : List Place
  written : call.places lookup names calls = some places
  frame : RuntimePureInterval.Checked block places.length start count inputs outputs (roles places)
  inputAxes : frame.selected.map (·.wires) = places.map (·.axes)
  outputAxes : frame.returned.map (·.wires) = places.map (·.axes)

/-- Bind the original ordered axes at both ends, check the complete local
owner return, and retain the actual enclosing spectators. Each position of
the local owner forest, including every empty owner, remains significant. -/
def read {tokens dependencies program} (call : CheckedCall tokens)
    (lookup : String → Option Owner) (names : Names) (calls : Calls)
    (block : RuntimeInterval.Block dependencies program) (start count : Nat)
    (inputs outputs : List Nat) : WorkM (Checked call lookup names calls block start count inputs outputs) := do
  exactWork (Exact.charge (32*(tokens.length+1)*(inputs.length+outputs.length+1)))
  match written : call.places lookup names calls with
  | none => throw .request
  | some places =>
    let frame ← RuntimePureInterval.check block places.length start count inputs outputs (roles places)
    let axes := places.map (·.axes)
    if inputAxes : frame.selected.map (·.wires) = axes then
      if outputAxes : frame.returned.map (·.wires) = axes then
        return ⟨places,written,frame,inputAxes,outputAxes⟩
      else throw .request
    else throw .request

def Checked.fragment {tokens dependencies program call lookup names calls block start count inputs outputs}
    (checked : @Checked tokens dependencies program call lookup names calls block start count inputs outputs) :
    Semantics.Observation.Program :=
  Semantics.Ownership.pureProgram (RuntimePureInterval.fragment checked.frame.selected checked.frame.operations outputs)

structure Sectors {tokens dependencies program call lookup names calls block start count inputs outputs}
    (checked : @Checked tokens dependencies program call lookup names calls block start count inputs outputs) where
  actual : Semantics.Exact.Matrix
  reconstructed : RuntimeInterval.Computed (Raw.BranchFunction.reconstruct dependencies checked.fragment) actual
  preserved : Semantics.ControlAccess.PreservesSectors actual (controlAxes checked.places)

/-- Reconstruct only this call's exact action. Its control axes are obtained
from the source-bound ordered ports, never an independently supplied mask. -/
def checkSectors {tokens dependencies program call lookup names calls block start count inputs outputs}
    (checked : @Checked tokens dependencies program call lookup names calls block start count inputs outputs) :
    WorkM (Sectors checked) := do
  let actual ← SourceTypes.NaturalAffine.witness (Raw.BranchFunction.reconstruct dependencies checked.fragment)
  let bits := (checked.frame.selected.map (·.bits)).sum
  let axes := controlAxes checked.places
  let passed ← SourceTypes.NaturalAffine.witness (ControlAccess.checkMatrix bits actual.val axes)
  have preserved : Semantics.ControlAccess.PreservesSectors actual.val axes := by
    obtain ⟨work,left,ok⟩ := passed.property
    have value : passed.val = () := Subsingleton.elim _ _
    exact ControlAccess.checkMatrix_sectors _ _ _ work left (by simpa only [value] using ok)
  return ⟨actual.val,by with_reducible exact actual.property,preserved⟩

/-- The compatibility result now speaks about the wire lists read from the
two actual intervals, even when structural routing lies between them. This is
the disjoint-support premise, separately from
the locality and semantic equations for those intervals. -/
theorem exclusive_actual_disjoint {tokensA tokensB dependencies program callA callB lookupA lookupB
    names calls block startA startB countA countB inputsA outputsA inputsB outputsB}
    (first : @Checked tokensA dependencies program callA lookupA names calls block startA countA inputsA outputsA)
    (second : @Checked tokensB dependencies program callB lookupB names calls block
      startB countB inputsB outputsB)
    (ok : compatible first.places second.places = true)
    (a b : Nat) (left : Place) (right : Place)
    (leftAt : first.places[a]? = some left) (rightAt : second.places[b]? = some right)
    (exclusive : left.role = .excl ∨ right.role = .excl) (axis : Nat)
    (present : axis ∈ ((first.frame.selected.map (·.wires))[a]?).getD []) :
    axis ∉ ((second.frame.selected.map (·.wires))[b]?).getD [] := by
  rw [first.inputAxes,List.getElem?_map,leftAt] at present
  rw [second.inputAxes,List.getElem?_map,rightAt]
  exact exclusive_disjoint _ _ ok left right (List.mem_of_getElem? leftAt)
    (List.mem_of_getElem? rightAt) exclusive axis present

end QleisliKernel.Qirf.RuntimeAccessInterval
