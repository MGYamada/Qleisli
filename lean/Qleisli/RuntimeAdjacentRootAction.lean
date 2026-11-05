import Qleisli.RuntimeAdjacentAction
import QleisliKernel.Raw.ObservationLayer
import QleisliKernel.Qirf.RuntimeNamedFrameAxes

/-! Finalize only the actual complete projected quantum root. Subintervals of
an observing parent retain their unfinalized execution and parent's history.
The original observing root also retains its true ordered final event.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.RuntimeAdjacentSlices
open QleisliKernel QleisliKernel.Finite QleisliKernel.Qirf
open QleisliKernel.Semantics.Finite

private theorem atZero {deps program} (p : RuntimeInterval.Prepared deps program) {count}
    (i : Interval p.block 0 count) : i.before = p.entry := by
  obtain ⟨w,l,read⟩ := i.prefixRead
  change (Raw.Observation.checkOps deps 65 p.entry []).run w = (.ok i.before,l) at read
  obtain ⟨s,m,first,rest⟩ := bind_success _ _ _ _ _ read
  obtain ⟨_,k,_,last⟩ := bind_success _ _ _ _ _ rest
  exact (pure_success s _ k l last).1.trans (pure_success p.entry s w m first).1

private theorem recoverOps (ops : List RawOp) :
    (ops.map Semantics.Observation.Op.pure).filterMap Sector.pureOp = ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons,List.filterMap_cons]
    exact congrArg (List.cons op) ih

/-- The independently projected whole root and authentic zero-to-end coverage
are the only extra requirements beyond the unfinalized interval theorem. In
particular the first scope's local entry and child finish do not replace the
original root entry and finish. -/
theorem Three.rootProgram
    {root : Validity.Root} (p : RuntimeInterval.Prepared root.dependencies root.program)
    {a b c : Nat} {pre : Slice p.block 0 a} {choose : Slice p.block (0+a) b}
    {post : Slice p.block (0+a+b) c} {preEvents chooseEvents postEvents}
    (result : Three pre choose post preEvents chooseEvents postEvents)
    (raw : Semantics.Raw.Program) (project : Sector.project root.program = some raw)
    (exhausts : a+b+c = root.program.operations.length)
    {Reference : Type} (joint : Nat → Reference → ℂ) (ref : Reference) :
    Qleisli.Semantics.RawAction.program root.dependencies raw (fun v => joint v ref) =
      some (RawActionComposition.finish root.dependencies raw
        (post.interval.after.quantum.reference,Qleisli.Semantics.RawAction.events root.dependencies postEvents
        (Qleisli.Semantics.RawAction.events root.dependencies chooseEvents
          (Qleisli.Semantics.RawAction.events root.dependencies preEvents (fun v => joint v ref))))) := by
  have subject := (Sector.project_bound root.program raw project).1
  have sameInputs : root.program.inputs = raw.inputs := congrArg Semantics.Observation.Program.inputs subject
  have allOps : root.program.operations = raw.operations.map Semantics.Observation.Op.pure :=
    congrArg Semantics.Observation.Program.operations subject
  have literal := result.literal
  change (root.program.operations.drop 0).take (a+b+c) = _ at literal
  rw [List.drop_zero,exhausts,List.take_length] at literal
  have sequence : pre.ops ++ choose.ops ++ post.ops = raw.operations := by
    have h := congrArg (List.filterMap Sector.pureOp) (literal.symm.trans allOps)
    simpa only [recoverOps] using h
  have entry : pre.interval.before.quantum.reference = Semantics.RawTrace.initial raw.inputs := by
    rw [atZero p pre.interval]
    simpa only [sameInputs,Semantics.RawTrace.initial] using (RuntimeNamedFrameAxes.initialized p.inputRead).1
  rw [RawActionComposition.program_execute]
  have actual := result.execute joint ref
  rw [sequence,entry] at actual
  rw [actual,Option.map_some]

open Raw.ObservationAgreement (Reader Result readStep)

private def observationAdvance (recurse : Reader) (p : Result) (op : Semantics.Observation.Op) :
    Option Result := do
  let (next,added) ← readStep recurse p.1 op
  return (next,p.2 ++ added)

private theorem pure_in_observing {recurse : Reader}
    (ops : List RawOp) (initial final : Semantics.RawTrace.Prepared)
    (read : ops.foldlM Semantics.RawTrace.advance initial = some final) :
    (ops.map Semantics.Observation.Op.pure).foldlM (observationAdvance recurse)
      (initial.state,initial.events.map Semantics.Observation.Event.pure) =
      some (final.state,final.events.map Semantics.Observation.Event.pure) := by
  induction ops generalizing initial with
  | nil =>
    have same : initial = final := Option.some.inj read
    subst final
    rfl
  | cons op rest ih =>
    cases step : Semantics.RawTrace.step initial.state op with
    | none =>
      simp only [List.foldlM_cons,Semantics.RawTrace.advance,step,bind,Option.bind] at read
      cases read
    | some pair =>
      obtain ⟨next,added⟩ := pair
      simp only [List.foldlM_cons,Semantics.RawTrace.advance,step,bind,Option.bind,pure] at read
      simpa only [List.map_cons,List.foldlM_cons,observationAdvance,readStep,step,bind,Option.bind,
        pure,List.map_append] using ih {initial with state := next,events := initial.events ++ added} read

private theorem originalStart {deps program} (p : RuntimeInterval.Prepared deps program) {count}
    (i : Interval p.block 0 count) :
    i.before.quantum.reference = Semantics.RawTrace.initial program.inputs := by
  rw [atZero p i]
  exact (RuntimeNamedFrameAxes.initialized p.inputRead).1

/-- Compare to the *stored* Observation.read result of the originally
verified whole program, including its declared output tokens and one finish.
No pure-program projection, source-effect relabel, or return-order premise. -/
theorem Three.retainedRoot
    {deps program} (p : RuntimeInterval.Prepared deps program)
    {a b c : Nat} {pre : Slice p.block 0 a} {choose : Slice p.block (0+a) b}
    {post : Slice p.block (0+a+b) c} {preEvents chooseEvents postEvents}
    (result : Three pre choose post preEvents chooseEvents postEvents) (covers : a+b+c = program.operations.length) :
    p.whole.prepared.state = post.interval.after.quantum.reference ∧
    p.whole.prepared.events = (preEvents ++ chooseEvents ++ postEvents).map Semantics.Observation.Event.pure ++
      [.pure (.reorder post.interval.after.quantum.frame.length
        (Semantics.RawTrace.axes post.interval.after.quantum.reference
          (program.outputs.flatMap fun token => ((post.interval.after.quantum.live.find? (fun port => port.token == token)).map (·.wires)).getD [])))] := by
  let entry := pre.interval.before.quantum
  let exit_ := post.interval.after.quantum
  have allOps := result.literal
  change (program.operations.drop 0).take (a+b+c) = _ at allOps
  rw [List.drop_zero,covers,List.take_length] at allOps
  have parent := pure_in_observing (recurse := Semantics.Observation.readOps 64)
    (pre.ops ++ choose.ops ++ post.ops) ⟨entry.reference,[],entry.frame.length⟩
      ⟨exit_.reference,preEvents ++ chooseEvents ++ postEvents,entry.frame.length⟩ result.parentTrace
  have obs : Semantics.Observation.readOps 65 (Semantics.RawTrace.initial program.inputs) program.operations =
      some (exit_.reference,(preEvents ++ chooseEvents ++ postEvents).map Semantics.Observation.Event.pure) := by
    rw [← originalStart p pre.interval,allOps,Raw.ObservationAgreement.read_succ]
    exact parent
  have actual := p.originalRoot.reader
  simp only [Semantics.Observation.read,obs,bind,Option.bind,pure] at actual
  have same := Option.some.inj actual
  exact ⟨(congrArg Semantics.Observation.Prepared.state same).symm,
    (congrArg Semantics.Observation.Prepared.events same).symm⟩

#print axioms Three.rootProgram
#print axioms Three.retainedRoot
end Qleisli.RuntimeAdjacentSlices
