import QleisliKernel.Qirf.RuntimeOwnerMap
import QleisliKernel.SourceTypes.SourceRuntimeBranches

/-! Bind original logical branch phis to actual Raw phi operands.
Each side is looked up in that side's complete checked owner map. Equal widths,
equal basis trees, a selected constant arm or a convenient output permutation
cannot replace those identities. Ordinary conditions/phis, branch source-body
checking, operator histories and code equations remain enclosing obligations.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.RuntimeOwnerPhis
open QleisliKernel QleisliKernel.Finite RuntimeOwnerMap
abbrev SourcePhi := SourceTypes.SourceRuntimeBranches.Phi
abbrev RawPhi := Semantics.Observation.QuantumPhi

inductive Role (source : List SourcePhi) (spectators : List Owner) (left right : Owner) :
    Option Nat → Owner → Prop where
  | selected (index : Nat) (phi : SourcePhi) (original : source[index]? = some phi)
      (thenOwner : phi.thenOwner = left) (elseOwner : phi.elseOwner = right) :
      Role source spectators left right (some index) phi.output
  | spectator (same : left = right) (retained : left ∈ spectators) :
      Role source spectators left right none left

structure One (source : List SourcePhi) (spectators : List Owner)
    (left right : Map) (phi : RawPhi) where
  thenBinding : Binding
  thenMember : thenBinding ∈ left
  thenToken : thenBinding.port.token = phi.thenToken
  elseBinding : Binding
  elseMember : elseBinding ∈ right
  elseToken : elseBinding.port.token = phi.elseToken
  sourceIndex : Option Nat
  owner : Owner
  role : Role source spectators thenBinding.owner elseBinding.owner sourceIndex owner

def One.binding {source spectators left right phi} (one : One source spectators left right phi) : Binding :=
  ⟨one.owner,⟨phi.output,phi.wires,phi.wires.length⟩⟩

def readOne (source : List SourcePhi) (spectators : List Owner)
    (left right : Map) (phi : RawPhi) : WorkM (One source spectators left right phi) := do
  exactWork (Exact.charge (32*(Raw.OwnerFlow.fields (source.flatMap fun phi =>
    [phi.output,phi.thenOwner,phi.elseOwner])+Raw.OwnerFlow.fields spectators+1)*
    (source.length+left.length+right.length+1)))
  let some thenBinding := byToken left phi.thenToken | throw .request
  let some elseBinding := byToken right phi.elseToken | throw .request
  if actual : thenBinding ∈ left ∧ thenBinding.port.token = phi.thenToken ∧
      elseBinding ∈ right ∧ elseBinding.port.token = phi.elseToken then
    let candidates := source.zipIdx.filter fun (candidate,_) =>
      candidate.thenOwner == thenBinding.owner && candidate.elseOwner == elseBinding.owner
    match candidates with
    | [(candidate,index)] =>
      if original : source[index]? = some candidate ∧
          candidate.thenOwner = thenBinding.owner ∧ candidate.elseOwner = elseBinding.owner then
        return ⟨thenBinding,actual.1,actual.2.1,elseBinding,actual.2.2.1,actual.2.2.2,
          some index,candidate.output,.selected index candidate original.1 original.2.1 original.2.2⟩
      else throw .request
    | [] =>
      if retained : thenBinding.owner = elseBinding.owner ∧ thenBinding.owner ∈ spectators then
        return ⟨thenBinding,actual.1,actual.2.1,elseBinding,actual.2.2.1,actual.2.2.2,
          none,thenBinding.owner,.spectator retained.1 retained.2⟩
      else throw .request
    | _ => throw .request
  else throw .request

structure Bound {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (source : List SourcePhi) (spectators leftRoles rightRoles outputRoles : List Owner)
    (left : RuntimeOwnerMap.Checked leftRoles actual.thenState)
    (right : RuntimeOwnerMap.Checked rightRoles actual.elseState) where
  phis : List ((phi : RawPhi) × One source spectators left.bindings right.bindings phi)
  everyRaw : phis.map Sigma.fst = actual.quantum
  everySource : (phis.filterMap fun pair => pair.2.sourceIndex).Perm (List.range source.length)
  output : RuntimeOwnerMap.Checked outputRoles actual.interval.after
  outputDerived : RuntimeInterval.Computed (do
    let ordered ← RuntimeOwnerMap.order outputRoles (phis.map fun pair => pair.2.binding)
    RuntimeOwnerMap.check outputRoles actual.interval.after ordered) output

/-- Recursive original child checks must supply both complete boundary maps.
All actual Raw phis and all original result-owner phis are consumed once. The
remaining phis preserve exactly the original caller spectators. -/
def check {dependencies program block offset}
    (actual : @RuntimeInterval.Branch dependencies program block offset)
    (source : List SourcePhi) (spectators leftRoles rightRoles outputRoles : List Owner)
    (left : RuntimeOwnerMap.Checked leftRoles actual.thenState)
    (right : RuntimeOwnerMap.Checked rightRoles actual.elseState) :
    WorkM (Bound actual source spectators leftRoles rightRoles outputRoles left right) := do
  guard (source.length ≤ 128 && actual.quantum.length ≤ 128) .limit
  exactWork (Exact.charge (64*(source.length+actual.quantum.length+1)^2))
  let phis ← actual.quantum.mapM fun phi => do
    let bound ← readOne source spectators left.bindings right.bindings phi
    return (⟨phi,bound⟩ : (phi : RawPhi) × One source spectators left.bindings right.bindings phi)
  if everyRaw : phis.map Sigma.fst = actual.quantum then
    if everySource : (phis.filterMap fun pair => pair.2.sourceIndex).Perm (List.range source.length) then
      let output ← SourceTypes.NaturalAffine.witness (do
        let ordered ← RuntimeOwnerMap.order outputRoles (phis.map fun pair => pair.2.binding)
        RuntimeOwnerMap.check outputRoles actual.interval.after ordered)
      return ⟨phis,everyRaw,everySource,output.val,by with_reducible exact output.property⟩
    else throw .request
  else throw .request

theorem Role.sameType {source spectators left right index output}
    (role : Role source spectators left right index output) :
    left.basis = output.basis ∧ right.basis = output.basis := by
  cases role with
  | selected index phi original thenOwner elseOwner =>
    exact ⟨thenOwner ▸ phi.thenType,elseOwner ▸ phi.elseType⟩
  | spectator same retained => exact ⟨rfl,congrArg Owner.basis same.symm⟩

end QleisliKernel.Qirf.RuntimeOwnerPhis
