import Qleisli.Resource

namespace Qleisli

/-- Resource projections of sealed operations. These are not quantum semantics
or effect rules. In particular, `discard` says nothing about pure release. -/
inductive Action : Store → Store → Prop where
  | init (s t w : Nat) : Action [] [⟨⟨s, .bit⟩, t, [w]⟩]
  | gate (r : Register) (t : Nat) : Action [r] [{ r with token := t }]
  | gate2 (r₁ r₂ : Register) (t₁ t₂ : Nat) (distinct : t₁ ≠ t₂) :
      Action [r₁, r₂] [{ r₁ with token := t₁ }, { r₂ with token := t₂ }]
  | gate3 (r₁ r₂ r₃ : Register) (t₁ t₂ t₃ : Nat)
      (distinct : t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃) :
      Action [r₁, r₂, r₃]
        [{ r₁ with token := t₁ }, { r₂ with token := t₂ }, { r₃ with token := t₃ }]
  | split (s t s₁ s₂ t₁ t₂ : Nat) (a b : Basis) (u v : List Nat)
      (hs : s₁ ≠ s₂) (ht : t₁ ≠ t₂)
      (hu : u.length = a.width) (hv : v.length = b.width) :
      Action [⟨⟨s, .pair a b⟩, t, u ++ v⟩]
        [⟨⟨s₁, a⟩, t₁, u⟩, ⟨⟨s₂, b⟩, t₂, v⟩]
  | join (r₁ r₂ : Register) (s t : Nat) :
      Action [r₁, r₂]
        [⟨⟨s, .pair r₁.port.basis r₂.port.basis⟩, t, r₁.wires ++ r₂.wires⟩]
  | lift (r : Register) (b : Basis) (t : Nat) (extra : List Nat)
      (width : r.wires.length + extra.length = b.width)
      (unique : extra.Nodup)
      (fresh : ∀ a ∈ r.wires, ∀ b ∈ extra, a ≠ b) :
      Action [r] [⟨⟨r.port.slot, b⟩, t, r.wires ++ extra⟩]
  | measure (s t w : Nat) : Action [⟨⟨s, .bit⟩, t, [w]⟩] []
  | discard (r : Register) : Action [r] []
  | reset (s t w s' t' w' : Nat) :
      Action [⟨⟨s, .bit⟩, t, [w]⟩] [⟨⟨s', .bit⟩, t', [w']⟩]

private theorem singleton_valid (r : Register) (hn : r.wires.Nodup)
    (hw : r.wires.length = r.port.basis.width) : Store.Valid [r] where
  slots_unique := by simp [slots]
  tokens_unique := by simp [tokens]
  wires_unique := by simpa [wires] using hn
  widths x hx := by
    obtain rfl := List.mem_singleton.mp hx
    exact hw

/-- Local validity is derived from the operation's shape and side conditions;
the validity of its output is not a premise of `Action`. -/
theorem Action.preserves {before after : Store} (step : Action before after)
    (h : before.Valid) : after.Valid := by
  cases step with
  | init s t w =>
    exact singleton_valid _ (by simp) rfl
  | gate r t =>
    exact singleton_valid _ (by simpa [wires] using h.wires_unique)
      (h.widths r (by simp))
  | gate2 r₁ r₂ t₁ t₂ distinct =>
    refine ⟨h.slots_unique, by simpa [tokens] using distinct, ?_, ?_⟩
    · simpa [wires] using h.wires_unique
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.widths r₁ (by simp)
      · exact h.widths r₂ (by simp)
  | gate3 r₁ r₂ r₃ t₁ t₂ t₃ distinct =>
    refine ⟨h.slots_unique, by simpa [tokens, List.nodup_cons, and_assoc] using distinct, ?_, ?_⟩
    · simpa [wires] using h.wires_unique
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.widths r₁ (by simp)
      · exact h.widths r₂ (by simp)
      · exact h.widths r₃ (by simp)
  | split s t s₁ s₂ t₁ t₂ a b u v hs ht hu hv =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [slots] using hs
    · simpa [tokens] using ht
    · simpa [wires] using h.wires_unique
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hu
      · exact hv
  | join r₁ r₂ s t =>
    apply singleton_valid
    · simpa [wires] using h.wires_unique
    · simp only [List.length_append, Basis.width]
      rw [h.widths r₁ (by simp), h.widths r₂ (by simp)]
  | lift r b t extra width unique fresh =>
    apply singleton_valid
    · exact List.nodup_append.mpr
        ⟨by simpa [wires] using h.wires_unique, unique, fresh⟩
    · exact (List.length_append ..).trans width
  | measure => exact ⟨by simp [slots], by simp [tokens], by simp [wires], by simp⟩
  | discard => exact ⟨by simp [slots], by simp [tokens], by simp [wires], by simp⟩
  | reset => exact singleton_valid _ (by simp) rfl

/-- A local edit with complete input coverage and a disjoint untouched frame.
The frame may contain pending tuple fields, caller resources or entangled peers.
Output holder coverage is a local interface contract, not global validity. -/
structure Replacement (before after : Config) where
  consumed : Store
  produced : Store
  frame : Store
  result : List Value
  suspended : List Value
  partition : before.store.Perm (consumed ++ frame)
  step : Action consumed produced
  separate : Separate produced frame
  result_coverage : (own result).Perm (ports produced)
  frame_coverage : (own suspended).Perm (ports frame)
  output_holders : after.holders = result ++ suspended
  output_store : after.store = produced ++ frame

theorem Replacement.preserves {before after : Config}
    (step : Replacement before after) (h : before.Valid) : after.Valid := by
  have partitionValid := h.store_valid.perm step.partition
  have frameValid := partitionValid.right
  have consumedValid : step.consumed.Valid :=
    (partitionValid.perm List.perm_append_comm).right
  constructor
  · rw [step.output_holders, step.output_store, own_append]
    simpa [ports] using step.result_coverage.append step.frame_coverage
  · rw [step.output_store]
    exact (step.step.preserves consumedValid).append frameValid step.separate

theorem Replacement.input_coverage {before after : Config}
    (step : Replacement before after) (h : before.Valid) :
    (own before.holders).Perm (ports step.consumed ++ own step.suspended) := by
  have p : (own before.holders).Perm (ports step.consumed ++ ports step.frame) := by
    simpa [ports] using h.coverage.trans (step.partition.map Register.port)
  exact p.trans ((List.Perm.refl _).append step.frame_coverage.symm)

theorem Replacement.frame_preserved {before after : Config}
    (step : Replacement before after) (r : Register) (hr : r ∈ step.frame) :
    r ∈ after.store := by
  rw [step.output_store]
  exact List.mem_append_right _ hr

/-- A sequence of checked ownership edits or structural holder rearrangements. -/
inductive ResourceRun : Config → Config → Prop where
  | done (c : Config) : ResourceRun c c
  | rearrange {a b c : Config} (store : b.store = a.store)
      (holders : (own a.holders).Perm (own b.holders))
      (rest : ResourceRun b c) : ResourceRun a c
  | edit {a b c : Config} (step : Replacement a b)
      (rest : ResourceRun b c) : ResourceRun a c

/-- R1-accounting for the explicit resource-event model, not full source R1. -/
theorem ResourceRun.preserves {a b : Config} (run : ResourceRun a b)
    (h : a.Valid) : b.Valid := by
  induction run with
  | done => exact h
  | rearrange store holders _ ih =>
    apply ih
    exact ⟨by simpa [store] using holders.symm.trans h.coverage, by
      simpa [store] using h.store_valid⟩
  | edit step _ ih => exact ih (step.preserves h)

end Qleisli
