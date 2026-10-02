import QleisliKernel.Qirf
import Qleisli.RawBranchFunction
import Qleisli.HierarchicalUnitary

/-! Original-index QIRF graph and root denotation from actual native success.
No Rust extractor, supplied receipt, selected-arm summary or isometry premise.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace Qleisli.Qirf
open QleisliKernel.Qirf QleisliKernel.Semantics.ObservingFunction
open QleisliKernel.Semantics.Finite QleisliKernel.Semantics.Exact
open Qleisli.Semantics.ObservingFunction
open scoped Matrix

/-- Snapshots preserve original evidence slots, including temporarily empty
slots. Readiness covers both arms before any snapshot is used by a body. -/
inductive GraphDenotation (artifact : QleisliKernel.Qirf.Artifact) : Slots → List Nat → Slots → Prop
  | nil (slots) : GraphDenotation artifact slots [] slots
  | program (slots node rest final program) (checked : QleisliKernel.Raw.Observation.Checked)
      (found : artifact.programs[node]? = some program)
      (ready : QleisliKernel.Qirf.ready slots program = true)
      (body : QleisliKernel.Semantics.Observation.read program = some checked.prepared)
      (remaining : GraphDenotation artifact slots rest final) :
      GraphDenotation artifact slots (node :: rest) final
  | entry (slots node rest final entry actual receipt a b)
      (outside : artifact.programs.size ≤ node)
      (found : artifact.entries[node - artifact.programs.size]? = some entry)
      (binding : (QleisliKernel.Qirf.input artifact entry).run a = (.ok actual,b))
      (ready : QleisliKernel.Qirf.ready slots actual.implementation = true ∧
        QleisliKernel.Qirf.ready slots actual.specification = true)
      (attached : receipt.input = actual)
      (body : EntryMeaning (before slots) receipt)
      (remaining : GraphDenotation artifact
        (slots.set! (node - artifact.programs.size) (some receipt)) rest final) :
      GraphDenotation artifact slots (node :: rest) final

theorem graph_semantics {artifact slots nodes final}
    (checked : CheckedGraph artifact slots nodes final) : GraphDenotation artifact slots nodes final := by
  induction checked with
  | nil slots => exact .nil slots
  | cons slots node rest next final checked remaining ih =>
    cases checked with
    | program program checked work left found ready verified =>
      exact .program _ _ _ _ _ checked found ready
        (QleisliKernel.Raw.Observation.verify_conditions _ _ _ _ _ verified).2.2 ih
    | entry entry actual receipt a b c d outside found decoded ready verified =>
      have meaning := Raw.BranchFunction.checkEntry_semantics _ _ _ _ _ _ verified
      exact .entry _ _ _ _ _ _ _ a b outside found decoded ready meaning.1 meaning.2.2 ih

/-- The complete original graph is reconstructed from empty slots. Every
attachment has actual full-body complex semantics and both inverse laws. -/
theorem checkGraph_semantics (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (dependencies : List Dependency) (work left : Nat)
    (ok : (checkGraph artifact order).run work = (.ok dependencies,left)) :
    ∃ slots, GraphDenotation artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
      slots.all Option.isSome = true ∧ dependencies = (before slots).map Receipt.dependency := by
  obtain ⟨slots,trace,full,bound⟩ := checkGraph_fresh _ _ _ _ _ ok
  exact ⟨slots,graph_semantics trace,full,bound⟩

/-- Root correctness includes arbitrary input amplitudes, not only basis
probabilities. `BodyMeaning` is the independent original instrument semantics. -/
theorem reconstruct_semantics (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (signature : Basis) (inputPort outputPort : QleisliKernel.Semantics.Raw.Port)
    (actual : Matrix) (work left : Nat)
    (ok : (reconstruct artifact order signature inputPort outputPort).run work = (.ok actual,left)) :
    ∃ (slots : Slots) (program : QleisliKernel.Semantics.Observation.Program)
      (checked : QleisliKernel.Raw.Observation.Checked),
      GraphDenotation artifact (Array.replicate artifact.entries.size none) order.toList slots ∧
      slots.all Option.isSome = true ∧
      artifact.rootInterface = some (signature,signature) ∧
      artifact.programs[artifact.root]? = some program ∧
      program.inputs = [inputPort] ∧ program.outputs = [outputPort.token] ∧
      checked.state.quantum.live = [outputPort] ∧
      BodyMeaning ((before slots).map Receipt.dependency) program actual ∧
      (Qleisli.Finite.square actual)ᴴ * Qleisli.Finite.square actual = 1 ∧
      Qleisli.Finite.square actual * (Qleisli.Finite.square actual)ᴴ = 1 := by
  obtain ⟨deps,program,checked,a,b,c,d,e,f,g,h,hg,hi,hp,hinput,houtput,hclosed,_,_,_,hlive,hr,hu⟩ :=
    reconstruct_conditions _ _ _ _ _ _ _ _ ok
  obtain ⟨slots,graph,full,bound⟩ := checkGraph_semantics _ _ _ _ _ hg
  have body := Raw.BranchFunction.reconstruct_denotes deps program hclosed actual e f hr
  have unitary := Qleisli.Finite.wholeSpace_unitary actual g h hu
  rw [bound] at body
  exact ⟨slots,program,checked,graph,full,hi,hp,hinput,houtput,hlive,body,unitary⟩

theorem check_semantics (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (signature : Basis) (inputPort outputPort : QleisliKernel.Semantics.Raw.Port)
    (required actual : Matrix) (work left : Nat)
    (ok : (check artifact order signature inputPort outputPort required).run work = (.ok actual,left)) :
    actual = required ∧ ∃ a b,
      (reconstruct artifact order signature inputPort outputPort).run a = (.ok required,b) := by
  obtain ⟨same,a,b,reconstructed⟩ := check_equation _ _ _ _ _ _ _ _ _ ok
  exact ⟨same,a,b,same ▸ reconstructed⟩

/-- Whole-space laws extend to an arbitrary finite entangled reference; no
separability, normalization or basis-probability premise is required. -/
theorem reconstruct_reference_laws {R : Type} [Fintype R] [DecidableEq R]
    (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat) (signature : Basis)
    (inputPort outputPort : QleisliKernel.Semantics.Raw.Port) (actual : Matrix) (work left : Nat)
    (ok : (reconstruct artifact order signature inputPort outputPort).run work = (.ok actual,left)) :
    let joint := _root_.Matrix.kronecker (Qleisli.Finite.square actual) (1 : _root_.Matrix R R ℂ)
    jointᴴ * joint = 1 ∧ joint * jointᴴ = 1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,unitary⟩ := reconstruct_semantics _ _ _ _ _ _ _ _ ok
  have first := HierarchicalUnitary.reference_isometry (R := R) _ unitary.1
  exact ⟨first,mul_eq_one_comm.mp first⟩

end Qleisli.Qirf
