import QleisliKernel.Semantics.RawOwnerFlow
import QleisliKernel.Finite

/-! Budgeted original-operation owner transport. This component does not read
source declarations, establish type/code equations or issue an accepted handle.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Raw.OwnerFlow
open Finite

def fields (owners : List Semantics.SourceOwners.Owner) : Nat :=
  owners.foldl (fun total owner => total + 1 + owner.basis.foldl (fun count atom =>
    count + 1 + match atom with
      | .enumeration origin names | .record origin names =>
        origin.moduleName.utf8ByteSize + origin.declarationName.utf8ByteSize +
          origin.source.utf8ByteSize + (names.map String.utf8ByteSize).sum
      | _ => 0) 0) 0

/-- Source identities must come from the enclosing original-source judgment.
No producer-supplied role map replaces this run over the literal Raw operations. -/
def check (inputs outputs : List Semantics.SourceOwners.Owner)
    (program : Semantics.Raw.Program) :
    WorkM (PLift (Semantics.RawOwnerFlow.Returns inputs program outputs)) := do
  exactWork (Exact.charge (8*(fields inputs+fields outputs+1) +
    128*(program.operations.length+1)*(inputs.length+outputs.length+1)^2))
  if returned : Semantics.RawOwnerFlow.run inputs program = some outputs then
    return ⟨returned⟩
  else throw .request

end QleisliKernel.Raw.OwnerFlow
