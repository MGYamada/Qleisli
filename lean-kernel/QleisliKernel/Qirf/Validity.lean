import QleisliKernel.Qirf.Checked

/-! Refinement contracts for the actual typed QIRF acceptance stages.
The compatibility projections preserve successes, errors and remaining work.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Qirf.Validity
open Semantics.Exact Semantics.Finite Semantics.Observation Finite

def requested (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) : WorkM Unit := do
  let _ ← checkRequested artifact dependencies program request
  pure ()

def inspect (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) : WorkM Unit := do
  let _ ← check artifact order request
  pure ()

/-- Universal compatibility with the former request checker, including failure
codes and exhausted budgets, not merely a corpus-level success comparison. -/
theorem requested_projection (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) :
    requested artifact dependencies program request = (do
      guard (artifact.rootInterface == some (request.signature,request.signature)) .request
      guard (request.sources.isNone || request.sources == some artifact.sources) .request
      guard (Raw.BranchFunction.preflight request.signature program) .limit
      let target ← meaningProgram request.signature request.target
      let actual ← Raw.BranchFunction.reconstruct dependencies program
      let required ← Raw.BranchFunction.reconstruct [] target
      exactWork (Exact.charge actual.entries.length)
      guard (actual == required) .equation
      wholeSpace actual) := by
  simp [requested,checkRequested]

/-- Universal compatibility with the former inspection sequence. Equality of
WorkM actions preserves every capacity, diagnostic and remaining-work value. -/
theorem inspect_projection (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) :
    inspect artifact order request = (do
      let dependencies ← checkGraph artifact order
      let used := artifact.entries.foldl (fun used entry =>
        entry.sources.foldl (fun used index => used.set! index true) used)
        (Array.replicate artifact.sources.size false)
      guard (used.all id)
      let program ← lift (readOption artifact.programs[artifact.root]?)
      let _ ← Raw.Observation.verify dependencies program
      guard (interfaceValid artifact program) .request
      match request with
      | none => pure ()
      | some request => requested artifact dependencies program request) := by
  cases request <;> simp [inspect,check,checkRoot,sourcesUsed,requested,bind_assoc]

/-- Named stage facts keep acceptance decomposition out of semantic proofs.
These are refinement facts, not a definition of semantic resource safety. -/
structure RootPostcondition (artifact : Qirf.Artifact) (order : Array Nat)
    (root : Root) (work : Nat) : Prop where
  graph : ∃ left, (checkGraph artifact order).run work = (.ok root.dependencies,left)
  sources : sourcesUsed artifact = true
  original : artifact.programs[artifact.root]? = some root.program
  verification : ∃ a b,
    (Raw.Observation.verify root.dependencies root.program).run a = (.ok root.checked,b)
  interface : interfaceValid artifact root.program = true

structure EquationPostcondition (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) (equation : Equation) : Prop where
  interface : artifact.rootInterface = some (request.signature,request.signature)
  sources : request.sources = none ∨ request.sources = some artifact.sources
  preflight : Raw.BranchFunction.preflight request.signature program = true
  target : ∃ a b, (meaningProgram request.signature request.target).run a = (.ok equation.target,b)
  implementation : ∃ a b,
    (Raw.BranchFunction.reconstruct dependencies program).run a = (.ok equation.actual,b)
  specification : ∃ a b,
    (Raw.BranchFunction.reconstruct [] equation.target).run a = (.ok equation.actual,b)
  unitary : ∃ a b, (wholeSpace equation.actual).run a = (.ok (),b)

structure Postcondition (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (checked : Checked) (work : Nat) : Prop where
  root : RootPostcondition artifact order checked.root work
  equation : match request with
    | none => checked.equation = none
    | some request => ∃ equation, checked.equation = some equation ∧
      EquationPostcondition artifact checked.root.dependencies checked.root.program request equation

theorem checkRoot_postcondition (artifact : Qirf.Artifact) (order : Array Nat)
    (root : Root) (work left : Nat)
    (ok : (checkRoot artifact order).run work = (.ok root,left)) :
    RootPostcondition artifact order root work := by
  obtain ⟨dependencies,a,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,c,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,d,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,_,hi,h⟩ := bind_success _ _ _ _ _ h
  have same := (pure_success _ _ _ _ h).1
  subst root
  have present : artifact.programs[artifact.root]? = some program := by
    have found := (lift_success _ _ _ _ hp).1
    cases hf : artifact.programs[artifact.root]? <;> simp_all [readOption]
  exact ⟨⟨a,hg⟩,(guard_success _ _ _ _ hs).1,present,⟨c,d,hv⟩,(guard_success _ _ _ _ hi).1⟩

theorem checkRequested_postcondition (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) (equation : Equation) (work left : Nat)
    (ok : (checkRequested artifact dependencies program request).run work = (.ok equation,left)) :
    EquationPostcondition artifact dependencies program request equation := by
  obtain ⟨_,w₁,hi,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨target,w₄,ht,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₅,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₆,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,he,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₉,hu,h⟩ := bind_success _ _ _ _ _ h
  have result := (pure_success _ _ _ _ h).1
  subst equation
  have same := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  rw [← same] at hr
  have sources : request.sources = none ∨ request.sources = some artifact.sources := by
    have accepted := (guard_success _ _ _ _ hs).1
    simpa only [Bool.or_eq_true,Option.isNone_iff_eq_none,beq_iff_eq] using accepted
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hi).1,sources,(guard_success _ _ _ _ hp).1,
    ⟨w₃,w₄,ht⟩,⟨w₄,w₅,ha⟩,⟨w₅,w₆,hr⟩,⟨w₈,w₉,hu⟩⟩

theorem check_postcondition (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (checked : Checked) (work left : Nat)
    (ok : (check artifact order request).run work = (.ok checked,left)) :
    Postcondition artifact order request checked work := by
  obtain ⟨root,middle,hr,h⟩ := bind_success _ _ _ _ _ ok
  have rootFacts := checkRoot_postcondition _ _ _ _ _ hr
  cases request with
  | none =>
    obtain ⟨equation,_,he,h⟩ := bind_success _ _ _ _ _ h
    have absent := (pure_success _ _ _ _ he).1
    have same := (pure_success _ _ _ _ h).1
    subst checked
    exact ⟨rootFacts,absent⟩
  | some request =>
    obtain ⟨equation,_,hc,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst checked
    exact ⟨rootFacts,⟨equation,rfl,checkRequested_postcondition _ _ _ _ _ _ _ hc⟩⟩

/-- Production's Unit API has the same successful typed result and final budget. -/
theorem inspect_result (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (work left : Nat)
    (ok : (inspect artifact order request).run work = (.ok (),left)) :
    ∃ checked, (check artifact order request).run work = (.ok checked,left) ∧
      Postcondition artifact order request checked work := by
  obtain ⟨checked,middle,hc,h⟩ := bind_success _ _ _ _ _ ok
  have budget := (pure_success _ _ _ _ h).2
  subst middle
  exact ⟨checked,hc,check_postcondition _ _ _ _ _ _ hc⟩

/-- Canonical requested tables have no external classical inputs. -/
theorem meaningProgram_closed (signature : Basis) (target : Target) (program : Program)
    (work left : Nat)
    (ok : (meaningProgram signature target).run work = (.ok program,left)) :
    program.classicalInputs = [] := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  cases target with
  | circuit index => cases h
  | permutation table | phase8 table =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst program
    rfl

/-- The budgeted canonical adapter refines the independent, budget-free
interpretation of the caller's complete table. -/
theorem meaningProgram_target (signature : Basis) (target : Target) (program : Program)
    (work left : Nat)
    (ok : (meaningProgram signature target).run work = (.ok program,left)) :
    Semantics.Qirf.targetProgram signature target = some program := by
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ ok
  cases target with
  | circuit index => cases h
  | permutation table | phase8 table =>
    obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
    have same := (pure_success _ _ _ _ h).1
    subst program
    rfl

/-- Actual successful inspection freshly checked the original graph and
original root, including both arms and all evidence dependencies. -/
theorem inspect_checked (artifact : Qirf.Artifact) (order : Array Nat)
    (request : Option Request) (work left : Nat)
    (ok : (inspect artifact order request).run work = (.ok (),left)) :
    ∃ dependencies program checked a b c d,
      (checkGraph artifact order).run work = (.ok dependencies,a) ∧
      artifact.programs[artifact.root]? = some program ∧
      (Raw.Observation.verify dependencies program).run b = (.ok checked,c) ∧
      interfaceValid artifact program = true ∧
      ((match request with | none => pure () | some r => requested artifact dependencies program r) : WorkM Unit).run d =
        (.ok (),left) := by
  rw [inspect_projection] at ok
  obtain ⟨dependencies,a,hg,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,_,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨program,b,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,c,hv,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hi,h⟩ := bind_success _ _ _ _ _ h
  have present : artifact.programs[artifact.root]? = some program := by
    have found := (lift_success _ _ _ _ hp).1
    cases hf : artifact.programs[artifact.root]? <;> simp_all [readOption]
  exact ⟨dependencies,program,checked,a,b,c,d,hg,present,hv,(guard_success _ _ _ _ hi).1,h⟩

/-- Request success concerns freshly reconstructed matrices, retaining exact
global phase, the full input space and the caller's complete type tree. -/
theorem requested_equation (artifact : Qirf.Artifact) (dependencies : List Dependency)
    (program : Program) (request : Request) (work left : Nat)
    (ok : (requested artifact dependencies program request).run work = (.ok (),left)) :
    artifact.rootInterface = some (request.signature,request.signature) ∧
    (request.sources = none ∨ request.sources = some artifact.sources) ∧
    ∃ target actual a b c d e f g h,
      (meaningProgram request.signature request.target).run a = (.ok target,b) ∧
      (Raw.BranchFunction.reconstruct dependencies program).run c = (.ok actual,d) ∧
      (Raw.BranchFunction.reconstruct [] target).run e = (.ok actual,f) ∧
      (wholeSpace actual).run g = (.ok (),h) := by
  rw [requested_projection] at ok
  obtain ⟨_,w₁,hi,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,w₂,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₃,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨target,w₄,ht,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨actual,w₅,ha,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨required,w₆,hr,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₇,_,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,w₈,he,h⟩ := bind_success _ _ _ _ _ h
  have same := beq_iff_eq.mp (guard_success _ _ _ _ he).1
  rw [← same] at hr
  have sources : request.sources = none ∨ request.sources = some artifact.sources := by
    have accepted := (guard_success _ _ _ _ hs).1
    simpa only [Bool.or_eq_true,Option.isNone_iff_eq_none,beq_iff_eq] using accepted
  exact ⟨beq_iff_eq.mp (guard_success _ _ _ _ hi).1,sources,
    target,actual,w₃,w₄,w₄,w₅,w₅,w₆,w₈,left,ht,ha,hr,h⟩

end QleisliKernel.Qirf.Validity
