import QleisliKernel.SourceTypes.GenericOperation

/-! Original closure controls use no quantum execution or Meaning evidence.
They inspect exact formal dependencies and existing operation descriptions.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.GenericOperation
open QleisliKernel QleisliKernel.SourceTypes QleisliKernel.SourceTypes.GenericOperation
open Semantics.SourceAffine Semantics.SymbolicBasis

private def frame : NaturalFrames.Frame := ⟨[⟨⟨"main","dormant"⟩,0,"n"⟩]⟩
private def named : Description := provider frame "main" "sign" [] [] [] []
private def requested : Description := named.unary (fun child => .requested child "main" "Identity")

private def closed (description : Description) : Option OperationDescription.Description :=
  match (close description).run 10000000 with
  | (.ok (.closed checked),_) => some checked.data.description
  | _ => none

private def conditional (description : Description) : Option (List Key) :=
  match (close description).run 10000000 with
  | (.ok (.conditional keys _ _),_) => some keys
  | _ => none

-- The unrelated original n does not participate in this genuinely closed
-- subject. Closing neither chooses n=0 nor grants Identity to sign.
#guard closed requested = some
  ((OperationDescription.provider "main" "sign" [] [] []).unary
    (fun child => .requested child "main" "Identity"))

private def formal : Description := .singleton frame (.formal ⟨"main","outer",2⟩)
#guard conditional formal = some [.operation ⟨"main","outer",2⟩]
#guard conditional (formal.unary (fun child => .power child ⟨⟨0,[0]⟩,false⟩)) =
  some [.operation ⟨"main","outer",2⟩]

-- An unused actual is still a complete child and retains its original Op key.
#guard conditional (provider frame "main" "ignore" [] [] [("U",formal)] []) =
  some [.operation ⟨"main","outer",2⟩]

private def dependentWidth : Description := provider frame "main" "bits"
  [("A",[.bits ⟨0,[1]⟩])] [] [] []
#guard conditional dependentWidth = some [.natural ⟨"main","dormant",0⟩]
#guard conditional (provider frame "main" "opaque" [("A",[.parameter ⟨"other","original",1⟩])] [] [] []) =
  some [.basis ⟨"other","original",1⟩]

-- A proof-backed constant form closes; Bits<0> remains its own exact type.
#guard (closed (provider frame "main" "bits" [("A",[.bits ⟨0,[0]⟩])] [] [] [])).map
  (·.nodes) = some [.provider "main" "bits" [("A",[.bits 0])] [] []]

-- Zero power retains the requested child and cannot erase the false claim.
#guard (closed (requested.unary (fun child => .power child ⟨⟨0,[0]⟩,false⟩))).map (·.nodes) =
  some [.provider "main" "sign" [] [] [],.requested 0 "main" "Identity",.power 1 0]

-- Invalid closed values and malformed original frames refuse. Neither is
-- misclassified as a conditional obligation merely because closure failed.
#guard (match (close (provider frame "main" "huge" [] [("n",⟨4294967296,[0]⟩)] [] [])).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (close (provider frame "main" "stale" [] [("n",⟨1,[]⟩)] [] [])).run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.GenericOperation
