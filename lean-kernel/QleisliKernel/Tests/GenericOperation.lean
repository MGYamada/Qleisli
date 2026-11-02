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

private def otherFrame : NaturalFrames.Frame := ⟨[⟨⟨"other","original"⟩,0,"n"⟩]⟩
private def other : Description := provider otherFrame "main" "counted" [] [("n",⟨0,[1]⟩)] [] []

-- Equal frame widths and names do not permit rebinding another declaration's
-- coefficient to the left/parent frame during binary or provider assembly.
#guard (match (close (named.binary other .thenOp)).run 10000000 with
  | (.error .request,_) => true | _ => false)
#guard (match (close (provider frame "main" "outer" [] [] [("U",other)] [])).run 10000000 with
  | (.error .request,_) => true | _ => false)

-- The reservation follows actual prefix cells and compared key bytes, even
-- with the same number of operation nodes and Nat formals. Closure does not
-- walk a retained nominal declaration's complete original source snapshot.
private def typed (code : Code) : Description := provider frame "main" "typed" [("A",code)] [] [] []
#guard Meter.freeWork (typed (.fixed (.tuple 16) :: List.replicate 16 (.fixed .unit))) >
  Meter.freeWork (typed [.fixed .unit])
#guard Meter.rebuildWork (typed (.fixed (.tuple 16) :: List.replicate 16 (.fixed .unit))) >
  Meter.rebuildWork (typed [.fixed .unit])
#guard Meter.freeWork (typed [.parameter ⟨"long_original_module","long_original_function",0⟩]) >
  Meter.freeWork (typed [.parameter ⟨"m","f",0⟩])

private def closedPaths (description : Description) (paths : OperationPaths.Paths) :
    Option (List (List Nat × OperationPaths.Paths)) :=
  let action : Finite.WorkM (List (List Nat × OperationPaths.Paths)) := do
    let fragments ← readAccessFragments description paths
    return fragments.filterMap fun fragment => match fragment.status with
      | .closed _ => some (fragment.path,fragment.requested)
      | .conditional .. => none
  (action.run 10000000).1.toOption

private def openPair := formal.binary named .thenOp
private def forward : OperationPaths.Paths := ⟨true,false,false⟩
private def inverse : OperationPaths.Paths := ⟨false,true,false⟩
private def control : OperationPaths.Paths := ⟨false,false,true⟩
private def noPaths : OperationPaths.Paths := ⟨false,false,false⟩

-- A free left operand does not hide demanded access on the closed right
-- occurrence. The path records child edges rather than deduplicated indices.
#guard closedPaths openPair forward = some [([1],forward)]
#guard closedPaths (openPair.unary .controlled) forward = some [([0,1],control)]
#guard closedPaths (openPair.unary .inverse) noPaths = some [([0,1],inverse)]
#guard closedPaths (openPair.unary (fun child => .power child ⟨⟨0,[0]⟩,false⟩)) forward =
  some [([0,1],forward)]

-- A provider's original prerequisite applies to its unused actual even when
-- the containing provider itself receives no implementation-path demand.
#guard closedPaths (provider frame "main" "outer" [] [] [("U",formal),("V",named)]
  [("U",noPaths),("V",inverse)]) noPaths = some [([1],inverse)]

-- Two formal occurrences sharing one description node still have separate
-- selected-formal demands. Node-index equality cannot select both operands.
#guard (OperationPaths.Shape.formal [(7,noPaths),(7,noPaths)] (some 0)).children forward =
  [(7,forward),(7,noPaths)]

-- Missing original prerequisite metadata refuses rather than supplying an
-- empty access contract for a named actual.
#guard (match (readAccessFragments (provider frame "main" "stale" [] [] [("U",formal)] []) noPaths).run 10000000 with
  | (.error .request,_) => true | _ => false)

end QleisliKernel.Tests.GenericOperation
