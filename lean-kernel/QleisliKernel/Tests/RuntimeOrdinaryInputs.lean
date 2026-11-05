import QleisliKernel.Qirf.RuntimeOrdinaryInputs

/-! Actual original input storage/ordinal/SSA binding at the fixed native work
budget. These ordinary-only fixtures claim no global source or std coverage.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.RuntimeOrdinaryInputs
open QleisliKernel QleisliKernel.Finite QleisliKernel.SourceTypes
open QleisliKernel.Qirf

private def tupleSource : String :=
  "#![no_implicit_prelude]\npub fn route(c:(Bit,Unit))->(Bit,Unit){c}"

private def recordSource : String :=
  "#![no_implicit_prelude]\npub struct Packet{bit:Bit,zero:Unit}pub fn route(c:Packet)->Packet{c}"

private def basis (record wrongZero : Bool) : Semantics.FiniteCarrier.Basis :=
  let zero := if wrongZero then Semantics.FiniteCarrier.Atom.bits 0 else .unit
  if record then [.record ⟨"main","Packet",recordSource⟩ ["bit","zero"],.bit,zero]
  else [.pair,.bit,zero]

private def stored (record reverseFields : Bool) : Semantics.OrdinaryValue.Storage :=
  if record then
    .record ⟨"main","Packet",recordSource⟩
      (if reverseFields then [("zero",.unit),("bit",.bit 2)] else [("bit",.bit 2),("zero",.unit)])
  else .pair (.bit 2) .unit

private def program : Semantics.Observation.Program := ⟨[],[2],[],[],[2],.unitary⟩

private def ordinals (record wrongZero reverseFields bit : Bool) : Option (List Nat × List Nat) :=
  ((do
    let text := if record then recordSource else tupleSource
    let sources : Sources := #[("main",text)]
    let signature ← SourceRuntimeContext.readSignature sources "main" "route" {}
    let body ← SourceRuntimeTrace.readBodyWithSignature signature
    let prepared ← RuntimeInterval.prepare [] program
    let input : Semantics.RuntimeStorage.Value := [.ordinary (basis record wrongZero) (stored record reverseFields)]
    let runtime : RuntimeFamily.Request :=
      ⟨.exported,"main","route",signature.parameters.map (·.tree),[input],[[false],[true]],
        signature.result.tree,input,.unitary,{}⟩
    let boundary ← RuntimeSourceBoundary.readInputs body prepared runtime.inputStorage
    let checked ← RuntimeOrdinaryInputs.read body prepared runtime boundary
    let row ← RuntimeOrdinaryInputs.readRow checked [bit]
    return (row.ordinals,checked.ssa.table.map Prod.fst) : WorkM _).run 10000000).1.toOption

-- A stored ordinary tuple block expands to the original two input fields;
-- the zero-width Unit field remains an independently bound source ordinal.
#guard ordinals false false false false = some ([0,0],[2])
#guard ordinals false false false true = some ([1,0],[2])
-- A record remains one nominal ordinary input with its complete field tree.
#guard ordinals true false false false = some ([0],[2])
#guard ordinals true false false true = some ([1],[2])
#guard (ordinals false true false false).isNone
#guard (ordinals true false true false).isNone

end QleisliKernel.Tests.RuntimeOrdinaryInputs
