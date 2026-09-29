import QleisliKernel.Hierarchical.FourierBase
import QleisliKernel.Hierarchical.FourierControl
import QleisliKernel.Hierarchical.Hadamard

/-! Inspect the complete shared recursive Fourier body with one remaining budget.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
Only full-byte-bound finite H equations remain pending. This is the reversed
output body, not the complete outer Fourier request or a production seal. -/

namespace QleisliKernel.Hierarchical.FourierBody
open Artifact

structure Pending where
  requests : List Hadamard.Request
  visits : Nat
  deriving Repr

inductive Matches (artifact : Artifact) (precision : Nat) : Nat → Nat → List Hadamard.Request → Prop where
  | one (index remaining : Nat) (base : FourierStage.Pending) (h : Hadamard.Pending)
      (baseChecked : FourierBase.inspect artifact index remaining = .ok base)
      (hChecked : Hadamard.inspect artifact base.step.hIndex (remaining-base.visits) = .ok h) :
      Matches artifact precision 1 index [h.request]
  | step (n index remaining : Nat) (stage : FourierStage.Pending) (h : Hadamard.Pending)
      (control : FourierControl.Pending) (requests : List Hadamard.Request)
      (stageChecked : FourierStage.inspect artifact (n+1) index remaining = .ok stage)
      (hChecked : Hadamard.inspect artifact stage.step.hIndex (remaining-stage.visits) = .ok h)
      (controlChecked : FourierControl.inspect artifact precision (n+1) stage.step.gradientIndex
        (remaining-stage.visits-h.visits) = .ok control)
      (child : Matches artifact precision (n+1) stage.step.childIndex requests) :
      Matches artifact precision (n+2) index (h.request::requests)

/-- Direct total Nat.rec avoids compiler-generated partial recursion helpers. -/
def inspectAux (artifact : Artifact) (precision levels : Nat) : Nat → Nat → Except Error Pending :=
  Nat.rec (fun index remaining =>
    match FourierBase.inspect artifact index remaining with
    | .error e => .error e
    | .ok base =>
      match Hadamard.inspect artifact base.step.hIndex (remaining-base.visits) with
      | .error e => .error e
      | .ok h => .ok ⟨[h.request],base.visits+h.visits⟩)
    (fun n recurse index remaining =>
      match FourierStage.inspect artifact (n+1) index remaining with
      | .error e => .error e
      | .ok stage =>
        match Hadamard.inspect artifact stage.step.hIndex (remaining-stage.visits) with
        | .error e => .error e
        | .ok h =>
          match FourierControl.inspect artifact precision (n+1) stage.step.gradientIndex
              (remaining-stage.visits-h.visits) with
          | .error e => .error e
          | .ok control =>
            match recurse stage.step.childIndex (remaining-stage.visits-h.visits-control.visits) with
            | .error e => .error e
            | .ok child => .ok ⟨h.request::child.requests,stage.visits+h.visits+control.visits+child.visits⟩) levels

theorem inspectAux_zero (artifact : Artifact) (precision index remaining : Nat) :
    inspectAux artifact precision 0 index remaining =
      (match FourierBase.inspect artifact index remaining with
      | .error e => .error e
      | .ok base =>
        match Hadamard.inspect artifact base.step.hIndex (remaining-base.visits) with
        | .error e => .error e
        | .ok h => .ok ⟨[h.request],base.visits+h.visits⟩) := rfl

theorem inspectAux_succ (artifact : Artifact) (precision n index remaining : Nat) :
    inspectAux artifact precision (n+1) index remaining =
      (match FourierStage.inspect artifact (n+1) index remaining with
      | .error e => .error e
      | .ok stage =>
        match Hadamard.inspect artifact stage.step.hIndex (remaining-stage.visits) with
        | .error e => .error e
        | .ok h =>
          match FourierControl.inspect artifact precision (n+1) stage.step.gradientIndex
              (remaining-stage.visits-h.visits) with
          | .error e => .error e
          | .ok control =>
            match inspectAux artifact precision n stage.step.childIndex
                (remaining-stage.visits-h.visits-control.visits) with
            | .error e => .error e
            | .ok child => .ok ⟨h.request::child.requests,stage.visits+h.visits+control.visits+child.visits⟩) := rfl

def inspect (artifact : Artifact) (precision width index remaining : Nat) : Except Error Pending :=
  if remaining > 2000000 || precision > 8 || width = 0 || width > precision then .error .limit
  else inspectAux artifact precision (width-1) index remaining

theorem inspectAux_sound (artifact : Artifact) (precision levels index remaining : Nat) (pending : Pending)
    (accepted : inspectAux artifact precision levels index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ Matches artifact precision (levels+1) index pending.requests := by
  induction levels generalizing index remaining pending with
  | zero =>
    rw [inspectAux_zero] at accepted
    split at accepted
    next failed => contradiction
    next base bc =>
      split at accepted
      next failed => contradiction
      next h hc =>
        cases Except.ok.inj accepted
        have bb := (FourierBase.inspect_sound artifact index remaining base bc).1
        have hb := (Hadamard.inspect_sound artifact base.step.hIndex (remaining-base.visits) h hc).1
        refine ⟨?_,.one index remaining base h bc hc⟩
        change base.visits+h.visits ≤ remaining
        omega
  | succ n ih =>
    rw [inspectAux_succ] at accepted
    split at accepted
    next failed => contradiction
    next stage sc =>
      split at accepted
      next failed => contradiction
      next h hc =>
        split at accepted
        next failed => contradiction
        next control cc =>
          split at accepted
          next failed => contradiction
          next child checked =>
            cases Except.ok.inj accepted
            have sb := (FourierStage.inspect_sound artifact (n+1) index remaining stage sc).1
            have hb := (Hadamard.inspect_sound artifact stage.step.hIndex (remaining-stage.visits) h hc).1
            have cb := (FourierControl.inspect_sound artifact precision (n+1) stage.step.gradientIndex
              (remaining-stage.visits-h.visits) control cc).1
            obtain ⟨rb,matched⟩ := ih stage.step.childIndex
              (remaining-stage.visits-h.visits-control.visits) child checked
            refine ⟨?_,.step n index remaining stage h control child.requests sc hc cc matched⟩
            change stage.visits+h.visits+control.visits+child.visits ≤ remaining
            omega

theorem inspect_sound (artifact : Artifact) (precision width index remaining : Nat) (pending : Pending)
    (accepted : inspect artifact precision width index remaining = .ok pending) :
    pending.visits ≤ remaining ∧ remaining ≤ 2000000 ∧ 1 ≤ width ∧ width ≤ precision ∧ precision ≤ 8 ∧
    Matches artifact precision width index pending.requests := by
  unfold inspect at accepted
  split at accepted
  next invalid => contradiction
  next valid =>
    simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at valid
    obtain ⟨bound,matched⟩ := inspectAux_sound artifact precision (width-1) index remaining pending accepted
    have size : width-1+1 = width := by omega
    rw [size] at matched
    exact ⟨bound,by omega,by omega,by omega,by omega,matched⟩

theorem request_count (artifact : Artifact) (precision width index : Nat) (requests : List Hadamard.Request)
    (matched : Matches artifact precision width index requests) : requests.length = width := by
  induction matched with
  | one => rfl
  | step _ _ _ _ _ _ _ _ _ _ _ ih => simpa only [List.length_cons] using congrArg (·+1) ih

end QleisliKernel.Hierarchical.FourierBody
