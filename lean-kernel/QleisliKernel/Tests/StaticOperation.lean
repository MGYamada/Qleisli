import QleisliKernel.SourceTypes.SourceOperation
import QleisliKernel.SourceTypes.QuantumSignature

/-! Small original static-transfer regressions. These inspect metadata and
generic obligations, separately from actual body/control equations and native
activation. No maximum-width graph or matrix is constructed.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.StaticOperation
open SourceTypes Semantics.FiniteCarrier OperationDescription

private def source :=
  "pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn bits(q:Q<Bits<1>>)->Q<Bits<1>>{q} " ++
  "pub observe fn observed(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub observe fn observed_impure(q:Q<Bit>)->Q<Bit>{let u=unit(());let b=basis u as _ {0};let _=discard(b);q} " ++
  "pub isometry fn weak(q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn unused[const U:Op<Bit>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn unused_pair[const V:Op<(Bit,Bit)>](q:Q<Bit>)->Q<Bit>{q} " ++
  "pub unitary fn generic[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Controllable(U){qmatch(s,q){0=>U,1=>U}} " ++
  "pub unitary fn no_control[const U:Op<Bit>](s:Q<Bit>,q:Q<Bit>)->(Q<Bit>,Q<Bit>) requires Applicable(U){qmatch(s,q){0=>U,1=>U}}"

private def sources : Sources := #[ ("main",source) ]

private def named (name : String) : Description := provider "main" name [] [] []

private def accepted (description : Description) (context : SourceTypes.StaticOperation.Context := .external) : Bool :=
  ((SourceTypes.StaticOperation.check sources context description).run 10000000).1.isOk

-- source provider has checked original ports
#guard
    ((SourceTypes.StaticOperation.check sources .external (named "keep")).run 10000000).1.toOption.map
      (fun checked => (checked.root.input,checked.root.output,checked.root.paths)) =
      some ([.bit],[.bit],⟨true,true,true⟩)

-- composed source operation checks both children
#guard
    accepted (Description.binary .thenOp (named "keep") (named "keep")) = true

-- equal width different original type cannot compose
#guard
    accepted (Description.binary .thenOp (named "keep") (named "bits")) = false

-- zero power keeps the external provider effect obligation
#guard
    accepted ((named "observed").unary (fun child => .power child 0)) = false

-- external observe cannot obtain control from a pure body
#guard
    accepted (named "observed") = false

-- same module observe retains an explicit internal body obligation
#guard
    ((SourceTypes.StaticOperation.check sources (.source "main") (named "observed")).run 10000000).1.toOption.map
      (fun checked => checked.providers.map fun provider =>
        (provider.signature.original.parsedHeader.effect,provider.expectedEffect,provider.internalInference)) =
      some [(some .observe,.unitary,true)]

-- An internal annotation cannot conceal actual observation, even when the
-- returned owner and input type are unchanged.
#guard accepted (named "observed_impure") (.source "main") = false

-- Public Iso stays Iso outside its original module. Forming controlled must
-- satisfy Unit even when its execution paths are unused/absent.
#guard accepted ((named "weak").unary .controlled) = false
#guard accepted ((named "weak").unary .controlled) (.source "main") = true

-- unrelated unused description node cannot hide a subject
#guard
    accepted ⟨[.provider "main" "bits" [] [] [],.provider "main" "keep" [] [] []],1⟩ = false

-- forward and self operation actual indices refuse
#guard
    accepted ⟨[.provider "main" "unused" [] [] [("U",0)]],0⟩ = false

-- unused operation actual keeps exact original type
#guard
    accepted (provider "main" "unused" [] [] [("U",named "bits")]) = false

-- unused operation actual keeps public effect
#guard
    accepted (provider "main" "unused" [] [] [("U",named "observed")]) = false

-- declared controllable formal keeps only its declared path
#guard
    ((SourceTypes.StaticOperation.check sources (.source "main")
      (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 0)).run 10000000).1.toOption.map
      (fun checked => checked.root.paths) = some ⟨false,false,true⟩

-- convenient actual does not supply an undeclared generic control path
#guard
    ((SourceTypes.StaticOperation.check sources (.source "main")
      (OperationDescription.formal "main" "no_control" [] [] [("U",named "keep")] 0)).run 10000000).1.toOption.map
      (fun checked => checked.root.paths) = some ⟨true,false,false⟩

-- formal ordinal cannot be a natural or later binder
#guard
    accepted (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 1) (.source "main") = false

-- A host descriptor cannot mint a lexical original formal scope.
#guard accepted (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 0) = false
#guard accepted (OperationDescription.formal "main" "generic" [] [] [("U",named "keep")] 0) (.source "other") = false

-- Forming controlled(U) is well kinded without acquiring an execution path.
#guard
    ((SourceTypes.StaticOperation.check sources (.source "main")
      ((OperationDescription.formal "main" "no_control" [] [] [("U",named "keep")] 0).unary .controlled)).run 10000000).1.toOption.map
      (fun checked => (checked.root.input,checked.root.output,checked.root.paths)) =
      some ([.pair,.bit,.bit],[.pair,.bit,.bit],⟨false,false,false⟩)

-- A formal with no access requirement may retain that unused description.
#guard
    accepted (provider "main" "unused_pair" [] [] [("V",
      (OperationDescription.formal "main" "no_control" [] [] [("U",named "keep")] 0).unary .controlled)]) (.source "main") = true

private def originalArrowEffect (access : String) : Option Semantics.Raw.Effect :=
  let action : Finite.WorkM Semantics.Raw.Effect := do
    let source := "#![no_implicit_prelude] pub unitary fn keep(q:Q<Bit>)->Q<Bit>{q} " ++
      "pub unitary fn unused[const A:Basis,const B:Basis,const U:Op<A->B>](q:Q<Bit>)->Q<Bit> " ++
      access ++ "{q}"
    let sources : Sources := #[("main",source)]
    let core ← QuantumSignatureCore.prepareWithArguments sources "main" "unused"
      {bases := [("A",[.bit]),("B",[.bit])],operations := [("U",named "keep")]}
    match core.instantiation with
    | .closed _ => throw .request
    | .static _ environment _ =>
      let some formal := environment.numeric.original.header.formals[2]? | throw .request
      pure (← SourceTypes.StaticOperation.formalContract environment formal).effect
  (action.run 10000000).1.toOption

-- Coinciding selected actuals do not equate two ORIGINAL opaque Basis binders.
#guard originalArrowEffect "" = some .iso
#guard originalArrowEffect "requires Adjointable(U)" = some .unitary
#guard originalArrowEffect "requires Controllable(U)" = none

end QleisliKernel.Tests.StaticOperation
