import QleisliKernel.SourceTypes.OperationAccess

/-! Small original path-demand regressions. Potential paths and deferred body
obligations are inspected separately from actual native implementation evidence.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.OperationAccess
open SourceTypes Semantics.FiniteCarrier OperationDescription

private def source :=
  "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn required[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Controllable(U){q} " ++
  "pub unitary fn only_apply[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){q}"

private def sources : Sources := #[("main",source)]
private def named (name : String) : Description := provider "main" name [] [] []

private def demands (description : Description) (requested : SourceTypes.StaticOperation.Paths) :
    Option (List (String × SourceTypes.StaticOperation.Paths)) :=
  (((do
    let graph ← SourceTypes.StaticOperation.check sources (.source "main") description
    let checked ← SourceTypes.OperationAccess.check graph requested
    pure (checked.providers.map fun (provider,paths) => (provider.declarationName,paths))) :
      Finite.WorkM _).run 10000000).1.toOption

-- Inverse formation demands its own J even under unused zero repetition.
#guard
  demands (((named "keep").unary .inverse).unary (fun child => .power child 0))
    SourceTypes.OperationAccess.empty = some [("keep",⟨false,true,false⟩)]

-- Final cancellation cannot erase the path used by the right inverse leaf.
#guard
  demands (Description.binary .thenOp (named "keep") ((named "keep").unary .inverse))
    SourceTypes.OperationAccess.applicable = some [("keep",⟨true,false,false⟩),("keep",⟨false,true,false⟩)]

-- Reverse/control of a provider retain ALL operation actual demands.
#guard
  demands (provider "main" "unused" [] [] [("U",named "keep")])
    SourceTypes.OperationAccess.adjointable = some [("keep",⟨true,true,false⟩),("unused",⟨false,true,false⟩)]
#guard
  demands (provider "main" "unused" [] [] [("U",named "keep")])
    SourceTypes.OperationAccess.controllable = some [("keep",⟨true,true,true⟩),("unused",⟨false,false,true⟩)]

-- An unused provider still checks each declared original prerequisite.
#guard
  demands (provider "main" "required" [] [] [("U",named "keep")])
    SourceTypes.OperationAccess.empty = some [("keep",⟨false,false,true⟩),("required",⟨false,false,false⟩)]

-- Controlled conjugation needs forward/reverse outer access and middle C.
#guard
  demands (Description.binary .conjugate (named "keep") (named "keep"))
    SourceTypes.OperationAccess.controllable = some [("keep",⟨true,true,false⟩),("keep",⟨false,false,true⟩)]

-- A stronger concrete actual cannot grant an undeclared formal path.
#guard
  demands (OperationDescription.formal "main" "only_apply" [] [] [("U",named "keep")] 0)
    SourceTypes.OperationAccess.controllable = none

end QleisliKernel.Tests.OperationAccess
