import QleisliKernel.Qirf.SourceDutySlots

/-! Internal original-duty plan controls. These inspect source metadata and
forward expectations only; no native body, Meaning equality, path or handle is
constructed. Existing first sources and withholding tests remain unchanged.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Tests.SourceDutySlots
open QleisliKernel Finite SourceTypes
open GenericOperation Semantics.SourceAffine Semantics.SymbolicBasis

private def frame : NaturalFrames.Frame := ⟨[⟨⟨"main","outer"⟩,0,"n"⟩]⟩
private def named : Description := provider frame "main" "keep" [] [] [] []
private def formal : Description := .singleton frame (.formal ⟨"main","outer",1⟩)
private def nonePaths : OperationPaths.Paths := ⟨false,false,false⟩
private def forward : OperationPaths.Paths := ⟨true,false,false⟩

private def views (description : Description) (requested : OperationPaths.Paths) :
    Option (List (List Nat × OperationPaths.Paths × Bool)) :=
  let action : WorkM (List (List Nat × OperationPaths.Paths × Bool)) := do
    return (← Qirf.SourceDutySlots.readViews description requested).map fun view =>
      (view.path,view.requested,match view.status with | .closed _ => true | .conditional .. => false)
  (action.run 10000000).1.toOption

-- The free sibling and zero repetition are both retained. Closed right-child
-- expectations keep their exact child-edge address under the open parent.
private def openZero := (formal.binary named .thenOp).unary (fun child => .power child ⟨⟨0,[0]⟩,false⟩)
#guard views openZero forward = some
  [([0,0],forward,false),([0,1],forward,true),([0],forward,false),([],forward,false)]

-- A shared raw node has two occurrences. Equality of node indices is not a
-- rule for sharing bodies or demands; postorder preserves both child edges.
private def shared : Description :=
  ⟨frame,[.provider "main" "keep" [] [] [] [],.thenOp 0 0],1,[frame,frame]⟩
#guard views shared nonePaths = some [([0],nonePaths,true),([1],nonePaths,true),([],nonePaths,true)]

-- Identity scalars and direct primitives still have an explicit source view.
-- They do not acquire a fabricated provider declaration or a body slot.
#guard views (.singleton frame (.primitive .globalPhaseEighth [.fixed .unit])) nonePaths =
  some [([],nonePaths,true)]

private def prelude := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "meaning Identity:Bit=reference(keep);\n"

private def pending {sources catalogue} (queue : @GenericDutyQueue.Checked sources catalogue)
    (item : GenericDutyQueue.Item catalogue) : Qirf.SourceDutySlots.ItemExpectation queue item → List Qirf.SourceDutySlots.Pending :=
  match item with
  | .demand _ _ => fun plan => plan.pending
  | .header .. | .call .. | .pendingRecursion .. => fun _ => []

private def inspect (source : String) : WorkM (Nat × Nat × Nat × Nat × Nat) := do
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  let references := plan.bodyOrder.filter fun address => match address.role with
    | .quantumReference _ => true | _ => false
  let headers := plan.indexed.items.filter fun item => match item with | .header .. => true | _ => false
  let allPending := plan.entries.flatMap fun entry =>
    pending queue entry.subject entry.subjectExpectation
  let supplier := allPending.filter fun obligation => match obligation with | .supplierInstance _ => true | _ => false
  let classical := allPending.filter fun obligation => match obligation with | .classicalReferenceRows _ => true | _ => false
  return (references.length,(references.map (·.requirement)).eraseDups.length,
    headers.length,supplier.length,classical.length)

private def headerSource := prelude ++
  "unitary fn need[const U:Op<Bit,Identity>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{need[keep](q)}"

-- A caller/header reference resolves to one exact canonical callee-header
-- demand. The original unbound header stays conditional, while the concrete
-- caller instance gets a distinct forward Meaning-reference expectation.
private def headerSharing : WorkM Bool := do
  let (references,ids,headers,suppliers,classical) ← inspect headerSource
  return references == 1 && ids == 1 && headers > 0 && suppliers > 0 && classical == 0
#guard headerSharing.run 10000000 |>.1.toOption == some true

private def writtenSource := prelude ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{let q=invoke[checked_op(keep,Identity)](q);" ++
  "invoke[checked_op(keep,Identity)](q)}"

-- Equal M names and equal source providers do not merge two written
-- assertions. Each fresh reference graph retains its own canonical duty ID.
private def writtenSeparate : WorkM Bool := do
  let (references,ids,_,suppliers,classical) ← inspect writtenSource
  return references == 2 && ids == 2 && suppliers > 0 && classical == 0
#guard writtenSeparate.run 10000000 |>.1.toOption == some true

private def ordinarySource := "#![no_implicit_prelude]\n" ++
  "unitary fn keep(q:Q<Bit>)->Q<Bit>{q}\n" ++
  "classical fn identity(x:Bit)->Bit{x}\n" ++
  "meaning Identity:Bit=permutation_by(identity);\n" ++
  "unitary fn invoke[const U:Op<Bit>](q:Q<Bit>)->Q<Bit> requires Applicable(U){U(q)}\n" ++
  "unitary fn caller(q:Q<Bit>)->Q<Bit>{invoke[checked_op(keep,Identity)](q)}"

-- Classical reference leaves remain independent original-evaluator/row
-- obligations. They never consume a fake quantum FunctionEvidence slot.
private def ordinarySeparate : WorkM Bool := do
  let (references,ids,_,suppliers,classical) ← inspect ordinarySource
  return references == 0 && ids == 0 && suppliers > 0 && classical == 1
#guard ordinarySeparate.run 10000000 |>.1.toOption == some true

private def emptyRoots : WorkM (Nat × Nat × Nat × Nat) := do
  let source := prelude ++ "classical fn spareA()->Unit{()}\nclassical fn spareB()->Unit{()}\n"
  let catalogue ← GenericCatalogue.read #[("main",source)]
  let queue ← GenericDutyQueue.read catalogue
  let plan ← Qirf.SourceDutySlots.read queue
  return (queue.roots.length,plan.indexed.items.length,plan.indexed.array.size,plan.entries.length)

-- Empty original roots still belong to the one retained flattening. A zero
-- item count does not omit those roots from preparation or its traversal cost.
#guard emptyRoots.run 10000000 |>.1.toOption == some (3,0,0,0)

end QleisliKernel.Tests.SourceDutySlots
