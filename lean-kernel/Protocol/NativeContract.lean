import Protocol.Validity
import QleisliKernel.Qirf.Contract
import QleisliKernel.Qirf.ControlAccess

/-! Strict bounded request decoding; acceptance is delegated to the pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/
namespace QleisliKernel.Protocol.NativeContract
open Lean QleisliKernel.Finite

private def adapt {α : Type} (value : Except String α) : WorkM α :=
  lift (value.mapError fun _ => .invalid)
private def fields (value : Json) (names : List String) : Except String Unit := do
  let actual := (← value.getObj?).toList.map (·.1)
  if actual.length != names.length || !actual.all names.contains then throw "unexpected request fields"
private def port (value : Json) : Except String Semantics.Raw.Port := do
  fields value ["token","wires","shape"]
  let shape ← value.getObjVal? "shape"
  fields shape ["bits"]
  return ⟨← (← value.getObjVal? "token").getNat?,
    ← (← (← value.getObjVal? "wires").getArr?).toList.mapM Json.getNat?,
    ← (← shape.getObjVal? "bits").getNat?⟩

/-- Decode an obligation, never a producer-supplied action or success receipt. -/
private def checkControl (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) : WorkM Unit := do
  adapt (fields value ["format","version","kind","signature","axes"])
  let signature ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "signature")))
  let axes ← adapt ((← adapt (value.getObjVal? "axes")).getArr? >>= fun values =>
    values.toList.mapM Json.getNat?)
  let _ ← QleisliKernel.Qirf.ControlAccess.check artifact order signature axes
  pure ()

/-- Bound owner-forest decoding before traversing individual type trees. -/
def decodeOwnerSignatures (value : Json) : Except String (List Semantics.Finite.Basis) := do
  let values ← value.getArr?
  if values.size > 64 then throw "too many owner signatures"
  values.toList.mapM (Qirf.basis 129)

/-- Decode an obligation, never a producer-supplied action or success receipt. -/
private def checkControlOwners (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) : WorkM Unit := do
  adapt (fields value ["format","version","kind","signatures","axes"])
  let signatures ← adapt (decodeOwnerSignatures (← adapt (value.getObjVal? "signatures")))
  let axes ← adapt ((← adapt (value.getObjVal? "axes")).getArr? >>= fun values =>
    values.toList.mapM Json.getNat?)
  let _ ← QleisliKernel.Qirf.ControlAccess.checkOwners artifact order signatures axes
  pure ()

def check (bytes : ByteArray) : WorkM Bool := do
  let (body,request) ← adapt (Validity.packet bytes)
  let some request := request | throw .request
  let some text := String.fromUTF8? request | throw .invalid
  let value ← adapt (FiniteCodec.parseWithDepth text 128)
  let kind ← adapt ((← adapt (value.getObjVal? "kind")).getStr?)
  let format ← adapt ((← adapt (value.getObjVal? "format")).getStr?)
  let version ← adapt ((← adapt (value.getObjVal? "version")).getNat?)
  guard (format == "qleisli.native-contract" && version == 1) .request
  let (artifact,order) ← Qirf.read body
  if kind == "encoded" then
    adapt (fields value ["format","version","kind","contract"])
    let required ← FiniteCodec.readContract (← adapt (value.getObjVal? "contract"))
    QleisliKernel.Qirf.checkContract artifact order required
  else if kind == "leaf" then
    adapt (fields value ["format","version","kind","signature","input","output","matrix"])
    let signature ← adapt (Qirf.basis 129 (← adapt (value.getObjVal? "signature")))
    let input ← adapt (port (← adapt (value.getObjVal? "input")))
    let output ← adapt (port (← adapt (value.getObjVal? "output")))
    let matrix ← FiniteCodec.readMatrixValue (← adapt (value.getObjVal? "matrix"))
    let _ ← QleisliKernel.Qirf.Validity.checkRoot artifact order
    let _ ← QleisliKernel.Qirf.check artifact order signature input output matrix
    pure ()
  else if kind == "control" then
    checkControl artifact order value
  else if kind == "control-owners" then
    checkControlOwners artifact order value
  else throw .request
  return true

/-- The token, ordered wire list and exact bit shape read from a request port.
This is a binding fact, not a substitute for the kernel's port checks. -/
def PortBinding (value : Json) (result : Semantics.Raw.Port) : Prop :=
  ∃ shape token wires bits wireValues,
    value.getObjVal? "shape" = .ok shape ∧
    value.getObjVal? "token" = .ok token ∧ token.getNat? = .ok result.token ∧
    value.getObjVal? "wires" = .ok wires ∧ wires.getArr? = .ok wireValues ∧
    wireValues.toList.mapM Json.getNat? = .ok result.wires ∧
    shape.getObjVal? "bits" = .ok bits ∧ bits.getNat? = .ok result.bits

private theorem string_bind_success {α β : Type} (first : Except String α)
    (next : α → Except String β) (result : β) (ok : (first >>= next) = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error error => cases ok
  | ok value => exact ⟨value,rfl,ok⟩

private theorem port_binding (value : Json) (result : Semantics.Raw.Port)
    (ok : port value = .ok result) : PortBinding value result := by
  unfold port at ok
  obtain ⟨_,_,h⟩ := string_bind_success _ _ _ ok
  obtain ⟨shape,hs,h⟩ := string_bind_success _ _ _ h
  obtain ⟨_,_,h⟩ := string_bind_success _ _ _ h
  obtain ⟨token,ht,h⟩ := string_bind_success _ _ _ h
  obtain ⟨tokenValue,htv,h⟩ := string_bind_success _ _ _ h
  obtain ⟨wires,hw,h⟩ := string_bind_success _ _ _ h
  obtain ⟨wireValues,hwv,h⟩ := string_bind_success _ _ _ h
  obtain ⟨wireList,hwl,h⟩ := string_bind_success _ _ _ h
  obtain ⟨bits,hb,h⟩ := string_bind_success _ _ _ h
  obtain ⟨bitValue,hbv,h⟩ := string_bind_success _ _ _ h
  cases h
  exact ⟨shape,token,wires,bits,wireValues,hs,ht,htv,hw,hwv,hwl,hb,hbv⟩

private theorem adapt_success {α : Type} (input : Except String α) (value : α)
    (work left : Nat) (ok : (adapt input).run work = (.ok value,left)) :
    input = .ok value ∧ left = work := by
  have h := lift_success _ _ _ _ ok
  refine ⟨?_,h.2⟩
  cases input <;> simp_all [Except.mapError]

/-- An encoded request retains the decoded contract and its actual checking
stage. It does not identify the root matrix with the finite wrapper's result. -/
structure EncodedAcceptance (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) (work left : Nat) where
  contractJson : Json
  required : Semantics.Finite.Contract
  afterContract : Nat
  kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "encoded"
  contractBound : value.getObjVal? "contract" = .ok contractJson
  contractDecoded : (FiniteCodec.readContract contractJson).run work = (.ok required,afterContract)
  accepted : (QleisliKernel.Qirf.checkContract artifact order required).run afterContract = (.ok (),left)

/-- A leaf request retains tuple shape, ordered ports and the exact requested
matrix. Both root validation and equation checking are from this execution. -/
structure LeafAcceptance (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) (work left : Nat) where
  signatureJson : Json
  inputJson : Json
  outputJson : Json
  matrixJson : Json
  signature : Semantics.Finite.Basis
  input : Semantics.Raw.Port
  output : Semantics.Raw.Port
  matrix : Semantics.Exact.Matrix
  root : QleisliKernel.Qirf.Validity.Root
  actual : Semantics.Exact.Matrix
  afterMatrix : Nat
  afterRoot : Nat
  kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "leaf"
  signatureBound : value.getObjVal? "signature" = .ok signatureJson
  signatureDecoded : Qirf.basis 129 signatureJson = .ok signature
  inputBound : value.getObjVal? "input" = .ok inputJson
  inputDecoded : PortBinding inputJson input
  outputBound : value.getObjVal? "output" = .ok outputJson
  outputDecoded : PortBinding outputJson output
  matrixBound : value.getObjVal? "matrix" = .ok matrixJson
  matrixDecoded : (FiniteCodec.readMatrixValue matrixJson).run work = (.ok matrix,afterMatrix)
  rootAccepted : (QleisliKernel.Qirf.Validity.checkRoot artifact order).run afterMatrix = (.ok root,afterRoot)
  accepted : (QleisliKernel.Qirf.check artifact order signature input output matrix).run afterRoot = (.ok actual,left)

/-- A control request is bound to exact decoded coordinates and the freshly
reconstructed action of the original artifact, including its dependencies. -/
structure ControlAcceptance (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) (work left : Nat) where
  signatureJson : Json
  axesJson : Json
  signature : Semantics.Finite.Basis
  axes : List Nat
  actual : Semantics.Exact.Matrix
  kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control"
  signatureBound : value.getObjVal? "signature" = .ok signatureJson
  signatureDecoded : Qirf.basis 129 signatureJson = .ok signature
  axesBound : value.getObjVal? "axes" = .ok axesJson
  axesDecoded : (axesJson.getArr? >>= fun values => values.toList.mapM Json.getNat?) = .ok axes
  accepted : (QleisliKernel.Qirf.ControlAccess.check artifact order signature axes).run work = (.ok actual,left)

/-- A control request is bound to exact decoded coordinates and the freshly
reconstructed action of the original artifact, including its dependencies. -/
structure ControlOwnersAcceptance (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) (work left : Nat) where
  signaturesJson : Json
  axesJson : Json
  signatures : List Semantics.Finite.Basis
  axes : List Nat
  actual : Semantics.Exact.Matrix
  kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control-owners"
  signaturesBound : value.getObjVal? "signatures" = .ok signaturesJson
  signaturesDecoded : decodeOwnerSignatures signaturesJson = .ok signatures
  axesBound : value.getObjVal? "axes" = .ok axesJson
  axesDecoded : (axesJson.getArr? >>= fun values => values.toList.mapM Json.getNat?) = .ok axes
  accepted : (QleisliKernel.Qirf.ControlAccess.checkOwners artifact order signatures axes).run work = (.ok actual,left)

/-- The requested sector obligation holds for the actual reconstructed action.
The surrounding Acceptance additionally binds it to original packet bytes. -/
theorem ControlAcceptance.preservesSectors
    {artifact : QleisliKernel.Qirf.Artifact} {order : Array Nat} {value : Json}
    {work left : Nat} (binding : ControlAcceptance artifact order value work left) :
    Semantics.ControlAccess.PreservesSectors binding.actual binding.axes := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,sectors⟩ :=
    QleisliKernel.Qirf.ControlAccess.check_bound _ _ _ _ _ _ _ binding.accepted
  exact sectors

inductive RequestAcceptance (artifact : QleisliKernel.Qirf.Artifact) (order : Array Nat)
    (value : Json) (work left : Nat) where
  | encoded (binding : EncodedAcceptance artifact order value work left)
  | leaf (binding : LeafAcceptance artifact order value work left)
  | control (binding : ControlAcceptance artifact order value work left)
  | controlOwners (binding : ControlOwnersAcceptance artifact order value work left)

/-- Original QLV1 bytes, mandatory original request, decoded payload and the
continuous work states of the actual native-contract checker. These are
necessary success facts; no converse or compiler correspondence is asserted. -/
structure Acceptance (bytes : ByteArray) (answer : Bool) (work left : Nat) where
  body : ByteArray
  requestBytes : ByteArray
  text : String
  value : Json
  artifact : QleisliKernel.Qirf.Artifact
  order : Array Nat
  afterArtifact : Nat
  packetBound : Validity.packet bytes = .ok (body,some requestBytes)
  utf8Bound : String.fromUTF8? requestBytes = some text
  requestBound : FiniteCodec.parseWithDepth text 128 = .ok value
  formatBound : (value.getObjVal? "format" >>= Json.getStr?) = .ok "qleisli.native-contract"
  versionBound : (value.getObjVal? "version" >>= Json.getNat?) = .ok 1
  artifactBound : (Qirf.read body).run work = (.ok (artifact,order),afterArtifact)
  request : RequestAcceptance artifact order value afterArtifact left
  answered : answer = true

private theorem adapt_bind_success {α β : Type} (input : Except String α)
    (next : α → WorkM β) (result : β) (work left : Nat)
    (ok : (adapt input >>= next).run work = (.ok result,left)) :
    ∃ value, input = .ok value ∧ (next value).run work = (.ok result,left) := by
  obtain ⟨value,middle,first,rest⟩ := bind_success _ _ _ _ _ ok
  obtain ⟨bound,same⟩ := adapt_success _ _ _ _ first
  exact ⟨value,bound,same ▸ rest⟩

private theorem checkControl_binding (artifact : QleisliKernel.Qirf.Artifact)
    (order : Array Nat) (value : Json) (work left : Nat)
    (kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control")
    (ok : (checkControl artifact order value).run work = (.ok (),left)) :
    Nonempty (ControlAcceptance artifact order value work left) := by
  unfold checkControl at ok
  obtain ⟨_,_,h⟩ := adapt_bind_success _ _ _ _ _ ok
  obtain ⟨signatureJson,sj,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨signature,s,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨axesJson,aj,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨axes,a,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨actual,middle,accepted,h⟩ := bind_success _ _ _ _ _ h
  have final := pure_success _ _ _ _ h
  exact ⟨⟨signatureJson,axesJson,signature,axes,actual,kindBound,sj,s,aj,a,
    final.2.symm ▸ accepted⟩⟩

private theorem checkControlOwners_binding (artifact : QleisliKernel.Qirf.Artifact)
    (order : Array Nat) (value : Json) (work left : Nat)
    (kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control-owners")
    (ok : (checkControlOwners artifact order value).run work = (.ok (),left)) :
    Nonempty (ControlOwnersAcceptance artifact order value work left) := by
  unfold checkControlOwners at ok
  obtain ⟨_,_,h⟩ := adapt_bind_success _ _ _ _ _ ok
  obtain ⟨signaturesJson,sj,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨signatures,s,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨axesJson,aj,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨axes,a,h⟩ := adapt_bind_success _ _ _ _ _ h
  obtain ⟨actual,middle,accepted,h⟩ := bind_success _ _ _ _ _ h
  have final := pure_success _ _ _ _ h
  exact ⟨⟨signaturesJson,axesJson,signatures,axes,actual,kindBound,sj,s,aj,a,
    final.2.symm ▸ accepted⟩⟩

theorem check_acceptance (bytes : ByteArray) (answer : Bool) (work left : Nat)
    (ok : (check bytes).run work = (.ok answer,left)) :
    Nonempty (Acceptance bytes answer work left) := by
  unfold check at ok
  obtain ⟨⟨body,request⟩,packet,h⟩ := adapt_bind_success _ _ _ _ _ ok
  cases request with
  | none => cases h
  | some request =>
    cases utf8 : String.fromUTF8? request with
    | none => simp only [utf8] at h; cases h
    | some text =>
      simp only [utf8] at h
      obtain ⟨value,parsed,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨kindJson,kj,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨kind,k,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨formatJson,fj,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨format,f,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨versionJson,vj,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨version,v,h⟩ := adapt_bind_success _ _ _ _ _ h
      obtain ⟨_,w₈,hguard,h⟩ := bind_success _ _ _ _ _ h
      obtain ⟨profile,sameWork⟩ := guard_success _ _ _ _ hguard
      have hguarded := sameWork ▸ h
      simp only [Bool.and_eq_true,beq_iff_eq] at profile
      have formatBound : (value.getObjVal? "format" >>= Json.getStr?) = .ok "qleisli.native-contract" := by
        simp [fj,bind,Except.bind,f,profile.1]
      have versionBound : (value.getObjVal? "version" >>= Json.getNat?) = .ok 1 := by
        simp [vj,bind,Except.bind,v,profile.2]
      obtain ⟨⟨artifact,order⟩,w₉,hread,h⟩ := bind_success _ _ _ _ _ hguarded
      suffices binding : Nonempty (RequestAcceptance artifact order value w₉ left) ∧ answer = true by
        obtain ⟨⟨binding⟩,answered⟩ := binding
        exact ⟨⟨body,request,text,value,artifact,order,w₉,packet,utf8,parsed,
          formatBound,versionBound,hread,binding,answered⟩⟩
      split at h
      · rename_i isEncoded
        obtain ⟨_,_,h⟩ := adapt_bind_success _ _ _ _ _ h
        obtain ⟨contractJson,cj,h⟩ := adapt_bind_success _ _ _ _ _ h
        obtain ⟨required,c,hcontract,h⟩ := bind_success _ _ _ _ _ h
        obtain ⟨_,d,hcheck,hreturn⟩ := bind_success _ _ _ _ _ h
        have final := pure_success _ _ _ _ hreturn
        have kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "encoded" := by
          simp only [beq_iff_eq] at isEncoded
          simp [kj,bind,Except.bind,k,isEncoded]
        exact ⟨⟨.encoded ⟨contractJson,required,c,kindBound,cj,hcontract,final.2.symm ▸ hcheck⟩⟩,final.1⟩
      · split at h
        · rename_i isLeaf
          obtain ⟨_,_,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨signatureJson,sj,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨signature,s,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨inputJson,ij,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨input,i,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨outputJson,oj,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨output,o,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨matrixJson,mj,h⟩ := adapt_bind_success _ _ _ _ _ h
          obtain ⟨matrix,h₂,hm,h⟩ := bind_success _ _ _ _ _ h
          obtain ⟨root,h₃,hroot,h⟩ := bind_success _ _ _ _ _ h
          obtain ⟨actual,h₄,hcheck,h⟩ := bind_success _ _ _ _ _ h
          obtain ⟨_,h₅,hunit,hreturn⟩ := bind_success _ _ _ _ _ h
          have final := pure_success _ _ _ _ hreturn
          have unit := pure_success _ _ _ _ hunit
          have last : h₄ = left := (final.2.trans unit.2).symm
          have kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "leaf" := by
            simp only [beq_iff_eq] at isLeaf
            simp [kj,bind,Except.bind,k,isLeaf]
          exact ⟨⟨.leaf ⟨signatureJson,inputJson,outputJson,matrixJson,signature,input,output,
            matrix,root,actual,h₂,h₃,kindBound,sj,s,ij,port_binding _ _ i,oj,
            port_binding _ _ o,mj,hm,hroot,last ▸ hcheck⟩⟩,final.1⟩
        · split at h
          · rename_i isControl
            obtain ⟨_,middle,accepted,hreturn⟩ := bind_success _ _ _ _ _ h
            have final := pure_success _ _ _ _ hreturn
            have kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control" := by
              simp only [beq_iff_eq] at isControl
              simp [kj,bind,Except.bind,k,isControl]
            obtain ⟨binding⟩ := checkControl_binding artifact order value w₉ left kindBound
              (final.2.symm ▸ accepted)
            exact ⟨⟨.control binding⟩,final.1⟩
          · split at h
            · rename_i isControlOwners
              obtain ⟨_,middle,accepted,hreturn⟩ := bind_success _ _ _ _ _ h
              have final := pure_success _ _ _ _ hreturn
              have kindBound : (value.getObjVal? "kind" >>= Json.getStr?) = .ok "control-owners" := by
                simp only [beq_iff_eq] at isControlOwners
                simp [kj,bind,Except.bind,k,isControlOwners]
              obtain ⟨binding⟩ := checkControlOwners_binding artifact order value w₉ left kindBound
                (final.2.symm ▸ accepted)
              exact ⟨⟨.controlOwners binding⟩,final.1⟩
            · cases h

end QleisliKernel.Protocol.NativeContract
