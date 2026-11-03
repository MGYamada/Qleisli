import QleisliKernel.SourceTypes

/-! Sharing the exact original helper check does not share a type result.
Nominal source identity, full field trees and zero-width shapes are reread.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceTypeSharing
open QleisliKernel QleisliKernel.SourceTypes Finite Semantics.FiniteCarrier

private def text := "#![no_implicit_prelude] " ++
  "static fn next[const n:Nat]()->Nat{n+1}" ++
  "pub struct Box{field:Bits<next[0]()>}pub struct Empty{}pub enum One{Only}"
private def sources : Sources := #[("main",text)]

private def read (shared : Bool) (mutation : Nat := 0) : WorkM (Bool × Basis) := do
  let helpers ← NaturalHelpers.read sources
  let original ← typeExpressionWithCheckedHelpers sources helpers "main" ["Box"]
  let basis := original.basis.map fun atom => match atom with
    | .record origin fields => if mutation == 2 then .record {origin with source := origin.source ++ " "} fields
      else .record origin fields
    | .bits 1 => if mutation == 1 then .bit else .bits 1
    | atom => atom
  let checked ← SourceTypes.readMany sources [basis] (if shared then some helpers else none)
  let reused := match checked with | .fresh _ => false | .prepared _ _ => true
  return (reused,basis)

#guard ((read true).run 10000000).1.toOption ==
  some (true,[.record ⟨"main","Box",text⟩ ["field"],.bits 1])
#guard ((read false).run 10000000).1.toOption ==
  some (false,[.record ⟨"main","Box",text⟩ ["field"],.bits 1])
#guard (match (read true 1).run 10000000 with | (.error .request,_) => true | _ => false)
#guard (match (read true 2).run 10000000 with | (.error .request,_) => true | _ => false)

private def zero : WorkM Bool := do
  let helpers ← NaturalHelpers.read sources
  let empty ← typeExpressionWithCheckedHelpers sources helpers "main" ["Empty"]
  let one ← typeExpressionWithCheckedHelpers sources helpers "main" ["One"]
  let checked ← SourceTypes.readMany sources [empty.basis,one.basis] (some helpers)
  return match checked with | .fresh _ => false | .prepared _ _ => true
#guard (zero.run 10000000).1.toOption == some true

private def invalidHelper : WorkM Unit := do
  let bad : Sources := #[("main",text ++ "static fn bad[const n:Nat]()->Nat{n-1}")]
  let helpers ← NaturalHelpers.read bad
  let _ ← SourceTypes.readMany bad [[.bit]] (some helpers)
  return ()
#guard (invalidHelper.run 10000000).1.toOption.isNone

end QleisliKernel.Tests.SourceTypeSharing
