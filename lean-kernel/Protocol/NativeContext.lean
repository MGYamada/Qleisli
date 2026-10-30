import Protocol.ExecutionView.Native
import Protocol.ExecutionView.CheckedEngineeringPure
import Protocol.ExecutionView.CheckedEngineeringPureTensor
import Protocol.ExecutionView.CheckedEngineeringOpenQasm
import Protocol.ExecutionView.CheckedCarrier
import Protocol.ExecutionView.CheckedRuntimeRoot
import Protocol.ExecutionView.CheckedQmatch
import Protocol.Product

/-! One pure native dispatch and response projection. Context is validated from
the original envelope; existing profile checks still establish their own claims.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.NativeContext
open ExecutionView Gate

inductive Mode where
  | ordinary | contract | hierarchy (mode : CheckedHierarchy.Modes.Mode)
  | engineeringPure | engineeringPureTensor | engineeringInstrument | engineeringOpenQasm
  | readout | preparation | carrierPure | ordinaryRoot | runtimeRoot | qmatchSource
  deriving BEq, DecidableEq, Repr

def Mode.name : Mode → String
  | .ordinary => "--qirf-native"
  | .contract => "--qirf-contract"
  | .hierarchy .inspect => "--hierarchy-pending"
  | .hierarchy .request => "--hierarchy-request-pending"
  | .hierarchy .fourier => "--hierarchy-fourier-pending"
  | .hierarchy .instrument => "--instrument-pending"
  | .hierarchy .qpeInstrument => "--qpe-instrument-pending"
  | .engineeringPure => "--engineering-pure-check"
  | .engineeringPureTensor => "--engineering-pure-tensor-check"
  | .engineeringInstrument => "--qirf-engineering-instrument-native"
  | .engineeringOpenQasm => "--engineering-openqasm-check"
  | .readout => "--readout-check"
  | .preparation => "--preparation-check"
  | .carrierPure => "--carrier-pure-check"
  | .ordinaryRoot => "--ordinary-root-check"
  | .runtimeRoot => "--runtime-root-check"
  | .qmatchSource => "--qmatch-source-check"

def Mode.parse : String → Option Mode
  | "--qirf-native" => some .ordinary
  | "--qirf-contract" => some .contract
  | "--hierarchy-pending" => some (.hierarchy .inspect)
  | "--hierarchy-request-pending" => some (.hierarchy .request)
  | "--hierarchy-fourier-pending" => some (.hierarchy .fourier)
  | "--instrument-pending" => some (.hierarchy .instrument)
  | "--qpe-instrument-pending" => some (.hierarchy .qpeInstrument)
  | "--engineering-pure-check" => some .engineeringPure
  | "--engineering-pure-tensor-check" => some .engineeringPureTensor
  | "--qirf-engineering-instrument-native" => some .engineeringInstrument
  | "--engineering-openqasm-check" => some .engineeringOpenQasm
  | "--readout-check" => some .readout
  | "--preparation-check" => some .preparation
  | "--carrier-pure-check" => some .carrierPure
  | "--ordinary-root-check" => some .ordinaryRoot
  | "--runtime-root-check" => some .runtimeRoot
  | "--qmatch-source-check" => some .qmatchSource
  | _ => none

theorem Mode.parse_name (mode : Mode) : Mode.parse mode.name = some mode := by
  cases mode with
  | hierarchy mode => cases mode <;> rfl
  | _ => rfl

structure Readout where
  packet : Protocol.Hierarchical.ReadoutPacket
  checked : Hierarchical.Readout.Checked

structure Preparation where
  packet : Protocol.Hierarchical.PreparationPacket
  checked : Hierarchical.Preparation.Checked

def Value : Mode → Type
  | .ordinary => Native.Ordinary
  | .contract => Packet.Scope × NativeContract.Retained
  | .hierarchy _ => Packet.Scope × CheckedHierarchy.Modes.Inspected
  | .engineeringPure => CheckedEngineeringPure.Checked
  | .engineeringPureTensor => CheckedEngineeringPureTensor.Checked
  | .engineeringInstrument => CheckedEngineeringInstrument.Checked
  | .engineeringOpenQasm => CheckedEngineeringOpenQasm.Checked
  | .readout => Readout
  | .preparation => Preparation
  | .carrierPure => CheckedCarrier.Checked
  | .ordinaryRoot => CheckedOrdinaryRoot.Checked
  | .runtimeRoot => CheckedRuntimeRoot.Checked
  | .qmatchSource => CheckedQmatch.Checked

def scope : (mode : Mode) → Value mode → Packet.Scope
  | .ordinary, value => value.scope
  | .contract, value => value.1
  | .hierarchy _, value => value.1
  | .engineeringPure, _ | .engineeringPureTensor, _
  | .engineeringInstrument, _ | .engineeringOpenQasm, _ | .carrierPure, _ | .ordinaryRoot, _
  | .runtimeRoot, _ | .qmatchSource, _ => .execution
  | .readout, _ | .preparation, _ => .inspection

private def parseComponent {α : Type} (result : Except Protocol.Error α) : CheckM α :=
  lift (result.mapError fun e => match e with | .syntax => .packet | .limit => .native .limit)

private def readout (bytes : ByteArray) : CheckM Readout := do
  let input ← lift (Packet.read bytes)
  guard (decide (input.scope = .inspection)) .packet
  let packet ← parseComponent (Protocol.Hierarchical.parseReadout input.original)
  let checked ← lift ((Hierarchical.Readout.check packet.request packet.packet packet.budget).mapError
    fun e => match e with
      | .limit => .hierarchy .limit none
      | .contract => .hierarchy .contract none
      | .invalidIr => .hierarchy .invalidIr none)
  return ⟨packet,checked⟩

private def preparation (bytes : ByteArray) : CheckM Preparation := do
  let input ← lift (Packet.read bytes)
  guard (decide (input.scope = .inspection)) .packet
  let packet ← parseComponent (Protocol.Hierarchical.parsePreparation input.original)
  let checked ← lift ((Hierarchical.Preparation.check packet.request packet.packet packet.budget).mapError
    fun e => match e with
      | .limit => .hierarchy .limit none
      | .contract => .hierarchy .contract none
      | .invalidIr => .hierarchy .invalidIr none)
  return ⟨packet,checked⟩

def check : (mode : Mode) → ByteArray → CheckM (Value mode)
  | .ordinary => Native.ordinary
  | .contract => Native.contract
  | .hierarchy mode => Native.hierarchy mode
  | .engineeringPure => CheckedEngineeringPure.run
  | .engineeringPureTensor => CheckedEngineeringPureTensor.run
  | .engineeringInstrument => Native.engineeringInstrument
  | .engineeringOpenQasm => CheckedEngineeringOpenQasm.run
  | .readout => readout
  | .preparation => preparation
  | .carrierPure => CheckedCarrier.run
  | .ordinaryRoot => CheckedOrdinaryRoot.run
  | .runtimeRoot => CheckedRuntimeRoot.run
  | .qmatchSource => CheckedQmatch.run

private theorem mapError_original {α ε δ : Type} (input : Except ε α) (mapping : ε → δ)
    (value : α) (ok : input.mapError mapping = .ok value) : input = .ok value := by
  cases input with
  | error error => cases ok
  | ok result => cases ok; rfl

private theorem parseComponent_success {α : Type} (input : Except Protocol.Error α)
    (value : α) (work left : Nat)
    (ok : (parseComponent input).run work = (.ok value,left)) :
    input = .ok value ∧ left = work := by
  have parsed := lift_success _ _ _ _ ok
  exact ⟨mapError_original _ _ _ parsed.1,parsed.2⟩

theorem check_readout_binding (bytes : ByteArray) (value : Readout) (work left : Nat)
    (ok : (check .readout bytes).run work = (.ok value,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parseReadout input.original = .ok value.packet ∧
      Hierarchical.Readout.check value.packet.request value.packet.packet value.packet.budget =
        .ok value.checked ∧ left = work := by
  change (readout bytes).run work = (.ok value,left) at ok
  unfold readout at ok
  obtain ⟨input,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨packet,c,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,d,hc,h⟩ := bind_success _ _ _ _ _ h
  have final : value = ⟨packet,checked⟩ ∧ left = d := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have outer := lift_success _ _ _ _ hp
  have selected := guard_success _ _ _ _ hs
  have parsed := parseComponent_success _ _ _ _ hd
  have result := lift_success _ _ _ _ hc
  exact ⟨input,outer.1,of_decide_eq_true selected.1,parsed.1,
    mapError_original _ _ _ result.1,result.2.trans (parsed.2.trans (selected.2.trans outer.2))⟩

theorem check_preparation_binding (bytes : ByteArray) (value : Preparation) (work left : Nat)
    (ok : (check .preparation bytes).run work = (.ok value,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ input.scope = .inspection ∧
      Protocol.Hierarchical.parsePreparation input.original = .ok value.packet ∧
      Hierarchical.Preparation.check value.packet.request value.packet.packet value.packet.budget =
        .ok value.checked ∧ left = work := by
  change (preparation bytes).run work = (.ok value,left) at ok
  unfold preparation at ok
  obtain ⟨input,a,hp,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨_,b,hs,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨packet,c,hd,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨checked,d,hc,h⟩ := bind_success _ _ _ _ _ h
  have final : value = ⟨packet,checked⟩ ∧ left = d := by cases h; exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have outer := lift_success _ _ _ _ hp
  have selected := guard_success _ _ _ _ hs
  have parsed := parseComponent_success _ _ _ _ hd
  have result := lift_success _ _ _ _ hc
  exact ⟨input,outer.1,of_decide_eq_true selected.1,parsed.1,
    mapError_original _ _ _ result.1,result.2.trans (parsed.2.trans (selected.2.trans outer.2))⟩

structure Decision (mode : Mode) where
  edition : Packet.Edition
  scope : Packet.Scope
  value : Value mode

/-- Product/version checks precede parsing; successful data come only from the
same exact envelope and existing mode-specific executable checker. -/
def run (mode : Mode) (requestedProduct : String) (bytes : ByteArray) : CheckM (Decision mode) := do
  guard (requestedProduct == productVersion) .version
  let input ← lift (Packet.read bytes)
  let value ← check mode bytes
  guard (decide (scope mode value = input.scope)) .packet
  return ⟨input.edition,input.scope,value⟩

theorem run_binding (mode : Mode) (requestedProduct : String) (bytes : ByteArray)
    (decision : Decision mode) (work left : Nat)
    (ok : (run mode requestedProduct bytes).run work = (.ok decision,left)) :
    ∃ input, Packet.read bytes = .ok input ∧ requestedProduct = productVersion ∧
      decision.edition = input.edition ∧ decision.scope = input.scope ∧
      (check mode bytes).run work = (.ok decision.value,left) ∧
      scope mode decision.value = input.scope := by
  unfold run at ok
  obtain ⟨_,a,hv,h⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨input,b,hp,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨value,c,hc,h⟩ := bind_success _ _ _ _ _ h
  obtain ⟨_,d,hs,h⟩ := bind_success _ _ _ _ _ h
  have final : decision = ⟨input.edition,input.scope,value⟩ ∧ left = d := by
    cases h
    exact ⟨rfl,rfl⟩
  rcases final with ⟨rfl,rfl⟩
  have version := guard_success _ _ _ _ hv
  have parsed := lift_success _ _ _ _ hp
  have selected := guard_success _ _ _ _ hs
  have first := version.2
  have second := parsed.2
  have last := selected.2
  subst a; subst b; subst c
  exact ⟨input,parsed.1,beq_iff_eq.mp version.1,rfl,rfl,hc,of_decide_eq_true selected.1⟩

theorem run_edition (mode : Mode) (requestedProduct : String) (bytes : ByteArray)
    (decision : Decision mode) (work left : Nat)
    (ok : (run mode requestedProduct bytes).run work = (.ok decision,left)) :
    Packet.u32 bytes 4 = decision.edition.code := by
  obtain ⟨input,parsed,_,edition,_,_,_⟩ := run_binding _ _ _ _ _ _ ok
  rw [edition]
  exact Packet.read_edition bytes input parsed

def Mode.status : Mode → String
  | .ordinary | .contract | .carrierPure | .ordinaryRoot | .runtimeRoot | .qmatchSource => "accepted"
  | .hierarchy _ => "pending"
  | .engineeringPure | .engineeringPureTensor
  | .engineeringInstrument | .engineeringOpenQasm => "engineering-checked"
  | .readout | .preparation => "checked"

private def indices (values : List Nat) : List String :=
  toString values.length :: values.map toString

def payload : (mode : Mode) → Value mode → Nat → List String
  | .ordinary, value, work => [toString work,if value.requested then "1" else "0"]
  | .contract, _, work => [toString work,"1"]
  | .hierarchy mode, value, work =>
    let core := value.2.core
    [toString core.visits,toString work] ++ indices (core.requests.toList.map (·.index)) ++
      (if mode == .inspect then []
       else indices (if mode == .fourier then core.hadamards else core.pairs)) ++
      (if mode == .qpeInstrument then indices core.hadamards else [])
  | .engineeringPure, _, work | .engineeringPureTensor, _, work
  | .engineeringInstrument, _, work | .engineeringOpenQasm, _, work => [toString work]
  | .readout, value, _ => [toString value.checked.visits]
  | .preparation, value, _ => [toString value.checked.visits]
  | .carrierPure, _, work | .ordinaryRoot, _, work | .qmatchSource, _, work | .runtimeRoot, _, work => [toString work,"1"]

def successLines (mode : Mode) (decision : Decision mode) (work : Nat) : List String :=
  ["qleisli.native-result 3",mode.status,toString decision.edition.code,productVersion,
    mode.name,decision.scope.name] ++ payload mode decision.value work

structure Reply where
  success : Bool
  lines : List String

def Mode.errorCode : Mode → Gate.Error → String
  | .hierarchy _, .native error => Protocol.HierarchicalFinite.errorCode error
  | _, error => Native.errorCode error

def reply (mode : Mode) (work : Nat) (result : Except Gate.Error (Decision mode)) (left : Nat) : Reply :=
  match result with
  | .error error => ⟨false,["qleisli.native-result 3","error",mode.errorCode error]⟩
  | .ok decision => ⟨true,successLines mode decision (work-left)⟩

theorem reply_hierarchy_native_error (mode : CheckedHierarchy.Modes.Mode)
    (error : QleisliKernel.Finite.Error) (work left : Nat) :
    (reply (.hierarchy mode) work (.error (.native error)) left).lines =
      ["qleisli.native-result 3","error",Protocol.HierarchicalFinite.errorCode error] := rfl

theorem reply_success_context (mode : Mode) (decision : Decision mode) (work left : Nat) :
    (reply mode work (.ok decision) left).lines =
      ["qleisli.native-result 3",mode.status,toString decision.edition.code,productVersion,
        mode.name,decision.scope.name] ++ payload mode decision.value (work-left) := rfl

end QleisliKernel.Protocol.NativeContext
