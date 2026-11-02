import QleisliKernel.SourceTypes.SourceEffectClosure

/-! Original runtime effect reachability, independent of chosen instances.
Unused provider eligibility is deliberately not a runtime dependency edge.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceEffectClosure
open QleisliKernel QleisliKernel.SourceTypes SourceEffectClosure

private def root : DefId := ("main","route")
private def helper : DefId := ("main","helper")
private def unrelated : DefId := ("main","unused")

private def result (entries : List Entry) :=
  ((SourceEffectClosure.read entries root).run 100000000).1.toOption

#guard (result [⟨root,⟨.unitary,[]⟩⟩,⟨unrelated,⟨.observe,[]⟩⟩]).map (·.inferred) = some .unitary
#guard (result [⟨root,⟨.unitary,[helper]⟩⟩,⟨helper,⟨.iso,[]⟩⟩]).map (·.inferred) = some .iso
#guard (result [⟨root,⟨.unitary,[helper]⟩⟩,⟨helper,⟨.observe,[]⟩⟩]).map (·.inferred) = some .observe
#guard (result [⟨root,⟨.unitary,[root]⟩⟩]).map (·.inferred) = some .unitary
#guard (result [⟨root,⟨.unitary,[helper]⟩⟩,⟨helper,⟨.observe,[root]⟩⟩]).map (·.inferred) = some .observe
#guard (result [⟨root,⟨.unitary,[helper]⟩⟩]).isNone
#guard (result [⟨helper,⟨.unitary,[]⟩⟩]).isNone
#guard (result [⟨root,⟨.unitary,[]⟩⟩,⟨root,⟨.observe,[]⟩⟩]).isNone
#guard (result [⟨root,⟨.unitary,[("external","pure")]⟩⟩,
  ⟨("external","pure"),⟨.unitary,[]⟩⟩]).isNone
-- A public external Observe contract contributes directly even when that
-- provider's internally inferred body is pure.
#guard (result [⟨root,⟨.observe,[]⟩⟩]).map (·.inferred) = some .observe

-- Unit-only allocation/release work still contributes quantum use through
-- the very same checked original internal-call closure.
#guard (result [⟨root,⟨.unitary,[helper]⟩⟩,⟨helper,⟨.unitary,[]⟩⟩]).map
  (fun checked => (checked.inferred,checked.quantumUse (fun id => id == helper))) = some (.unitary,true)
#guard (result [⟨root,⟨.unitary,[]⟩⟩,⟨unrelated,⟨.unitary,[]⟩⟩]).map
  (fun checked => checked.quantumUse (fun id => id == unrelated)) = some false

private def shared (entries : List Entry) (roots : List DefId) :
    Option (List (Semantics.Raw.Effect × List DefId × Bool)) :=
  let action : Finite.WorkM (List (Semantics.Raw.Effect × List DefId × Bool)) := do
    let prepared ← SourceEffectClosure.prepare entries
    roots.mapM fun selected => do
      let checked ← SourceEffectClosure.readPrepared prepared selected
      pure (checked.inferred,checked.ids,checked.quantumUse (fun id => id == helper))
  (action.run 10000000).1.toOption

-- One exact setup serves several independently walked roots. Unreachable
-- observation remains separate, while actual reachable quantum use survives.
#guard shared [⟨root,⟨.unitary,[helper]⟩⟩,⟨helper,⟨.iso,[]⟩⟩,⟨unrelated,⟨.observe,[]⟩⟩]
    [root,helper,unrelated] =
  some [(.iso,[root,helper],true),(.iso,[helper],true),(.observe,[unrelated],false)]
#guard shared [⟨root,⟨.unitary,[helper]⟩⟩] [root] = none
#guard shared [⟨root,⟨.unitary,[]⟩⟩,⟨root,⟨.observe,[]⟩⟩] [root] = none
#guard shared [⟨root,⟨.unitary,[("external","pure")]⟩⟩,
    ⟨("external","pure"),⟨.unitary,[]⟩⟩] [root] = none

-- This is a classical effect graph only, not a maximum quantum instance. The
-- source call count is not capped by the short root name/token list.
private def chain : List Entry := (List.range 140).map fun index =>
  let id : DefId := ("main",toString index)
  let dependencies := if index+1 < 140 then [("main",toString (index+1))] else []
  ⟨id,⟨if index == 139 then .observe else .unitary,dependencies⟩⟩
#guard (((SourceEffectClosure.read chain ("main","0")).run 100000000).1.toOption.map fun checked =>
  (checked.ids.length,checked.inferred)) = some (140,.observe)

#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.read
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.readPrepared
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.Checked.direct_bound
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.Checked.least
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.Checked.internal_bound
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.Checked.unitary_direct
#print axioms QleisliKernel.SourceTypes.SourceEffectClosure.Checked.quantumUse_reachable
end QleisliKernel.Tests.SourceEffectClosure
