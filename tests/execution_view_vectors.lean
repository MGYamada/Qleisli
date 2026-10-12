import Lean
import Protocol.ExecutionView.CheckedFinite
import Protocol.ExecutionView.CheckedContract
import Protocol.ExecutionView.CheckedCaller
import Protocol.Qirf

/-! Shared QDV1 data and pure comparison-gate regressions. Production cutover is pending.
Copyright 2026 Qleisli Project Contributors. SPDX-License-Identifier: Apache-2.0 -/
open Lean QleisliKernel.Protocol.ExecutionView

private def value (fuel : Nat) : Json → Except String Value :=
  Nat.rec (fun _ => throw "vector depth") (fun _ recurse input => do
    match input with
    | .null => return .null
    | .bool b => return .boolean b
    | .num _ => return .natural (← input.getNat?)
    | .str s => return .text s
    | .arr xs => return .array (← xs.toList.mapM recurse)
    | .obj _ => throw "canonical vector contains an object") fuel

private def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.flatMap fun byte =>
    let digits := "0123456789abcdef".toList
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

private def failed {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def coefficient (value : Json) : Except String QleisliKernel.Semantics.Exact.Coefficient := do
  let pair ← value.getArr?
  if pair.size != 2 then throw "expected a dyadic pair"
  let some numerator := (← pair[0]!.getStr?).toInt? | throw "expected a signed numerator"
  return ⟨numerator,← pair[1]!.getNat?⟩

private def matrix (value : Json) : Except String QleisliKernel.Semantics.Exact.Matrix := do
  let rows ← (← value.getObjVal? "rows").getNat?
  let cols ← (← value.getObjVal? "cols").getNat?
  let entries ← (← (← value.getObjVal? "entries").getArr?).toList.mapM fun scalar => do
    let cs ← (← scalar.getArr?).toList.mapM coefficient
    let [a,b,c,d] := cs | throw "expected four exact coefficients"
    return QleisliKernel.Semantics.Exact.Scalar.mk a b c d
  if entries.length != rows*cols then throw "matrix entry count"
  return ⟨rows,cols,entries⟩

private def finite (directory : System.FilePath) (row : Json) : IO Value := do
  match ← IO.ofExcept ((row.getObjVal? "kind") >>= Json.getStr?) with
  | "raw-source" =>
    let source ← IO.ofExcept ((row.getObjVal? "source") >>= Json.getStr?)
    let artifact ← IO.ofExcept (Json.parse (← IO.FS.readFile (directory / source)))
    let programs ← IO.ofExcept ((artifact.getObjVal? "programs") >>= Json.getArr?)
    if programs.size != 1 then throw (IO.userError "expected one retained root")
    IO.ofExcept (QleisliKernel.Protocol.Observation.program programs[0]! >>= FiniteView.program)
  | "raw" =>
    IO.ofExcept ((row.getObjVal? "program") >>= QleisliKernel.Protocol.Observation.program >>= FiniteView.program)
  | "basis" =>
    return FiniteView.basis (← IO.ofExcept ((row.getObjVal? "basis") >>= QleisliKernel.Protocol.Qirf.basis 129))
  | "matrix" => return FiniteView.matrix (← IO.ofExcept ((row.getObjVal? "matrix") >>= matrix))
  | _ => throw (IO.userError "unknown finite vector kind")

private def functionInput (row : Json) : Except String QleisliKernel.Semantics.ObservingFunction.Input := do
  let signature ← (← row.getObjVal? "signature") |> QleisliKernel.Protocol.Qirf.basis 129
  let implementation ← (← row.getObjVal? "implementation") |> QleisliKernel.Protocol.Observation.program
  let specification ← (← row.getObjVal? "specification") |> QleisliKernel.Protocol.Observation.program
  let identity ← row.getObjVal? "identity"
  let sources ← (← (← identity.getObjVal? "sources").getArr?).toList.mapM fun source => do
    let pair ← source.getArr?
    if pair.size != 2 then throw "expected source pair"
    return (← pair[0]!.getStr?,← pair[1]!.getStr?)
  return ⟨signature,implementation,specification,
    ⟨← (← identity.getObjVal? "implementation").getStr?,
      ← (← identity.getObjVal? "specification").getStr?,sources⟩⟩

private def checked {α : Type} (work : QleisliKernel.Finite.WorkM α) : IO α := do
  match work.run 10000000 with
  | (.ok result,_) => return result
  | (.error error,_) => throw (IO.userError ("native derivation refused: " ++ reprStr error))

private def lengthBytes (value : Nat) : ByteArray :=
  ⟨((List.range 4).map (fun index => (value / 256^index % 256).toUInt8)).toArray⟩

private def packet (body : ByteArray) (required : ByteArray := ByteArray.empty) : ByteArray :=
  "QLV1".toUTF8 ++ lengthBytes body.size ++ lengthBytes required.size ++ body ++ required

private def viewRejected (input supplied : ByteArray) (error : CheckedFinite.Error) : IO Unit := do
  match (CheckedFinite.check input supplied).run 10000000 with
  | (.error actual,_) => unless actual == error do
      throw (IO.userError ("wrong finite view refusal: " ++ reprStr actual))
  | (.ok _,_) => throw (IO.userError "divergent/malformed finite view accepted")

private def frameCases : IO Unit := do
  let invalid := [ByteArray.empty,"QDV1".toUTF8,"QDV0".toUTF8 ++ ⟨#[0]⟩,
    "QDV1".toUTF8 ++ ⟨#[6]⟩,
    "QDV1".toUTF8 ++ ⟨#[4,1,0,0,0,255]⟩,
    "QDV1".toUTF8 ++ ⟨#[4,2,0,0,0,192,128]⟩,
    "QDV1".toUTF8 ++ ⟨#[4,3,0,0,0,237,160,128]⟩,
    "QDV1".toUTF8 ++ ⟨#[5,255,255,255,255]⟩]
  for bytes in invalid do
    if framed bytes then throw (IO.userError "invalid QDV1 frame accepted")
  let deep := (List.range (maxDepth+1)).foldl
    (fun bytes _ => bytes ++ ⟨#[5,1,0,0,0]⟩) "QDV1".toUTF8 ++ ⟨#[0]⟩
  if framed deep then throw (IO.userError "over-depth QDV1 frame accepted")
  -- A small transport-only wide array exercises count traversal without
  -- allocating a maximum-size quantum case or changing any capacity.
  let wide := "QDV1".toUTF8 ++ ⟨#[5]⟩ ++ lengthBytes 4096 ++ ⟨Array.replicate 4096 0⟩
  unless framed wide do throw (IO.userError "bounded wide QDV1 array rejected")
  if framed (wide.extract 0 (wide.size-1)) then throw (IO.userError "short wide QDV1 array accepted")

private def gateCases (input : ByteArray) (description : Value) : IO Nat := do
  let supplied ← IO.ofExcept (encode description)
  let original := packet input
  -- The original artifact is valid independently of the candidate view. Each
  -- following test changes only that candidate, never the accepted raw input.
  let _ ← checked (QleisliKernel.Protocol.Validity.check original)
  match (CheckedFinite.check original supplied).run 10000000 with
  | (.ok result,_) =>
    unless result.body == input && result.requestBytes.isNone do
      throw (IO.userError "finite gate changed original input")
  | (.error error,_) => throw (IO.userError ("correct finite view rejected: " ++ reprStr error))
  let .array fields := description | throw (IO.userError "expected finite graph record")
  let mut refusals := 0
  for index in List.range fields.length do
    let replacement := match fields[index]? with
      | some .null => Value.array []
      | _ => Value.null
    let mutated ← IO.ofExcept (encode (.array (fields.set index replacement)))
    viewRejected original mutated .decodedView
    refusals := refusals+1
  -- Retained cache fields also participate, rather than merely the original
  -- implementation body or an evidence-table reference.
  if let some (Value.array (evidence :: rest)) := fields[5]? then
    if let Value.array cache := evidence then
      for index in (List.range (cache.length-1)).map (·+1) do
        let mutated := fields.set 5 (.array (.array (cache.set index .null) :: rest))
        viewRejected original (← IO.ofExcept (encode (.array mutated))) .decodedView
        refusals := refusals+1
  viewRejected original "QDV1".toUTF8 .invalidView
  viewRejected "QLV0".toUTF8 supplied .packet
  viewRejected (packet "invalid QIRF".toUTF8) supplied (.native .invalid)
  match (QleisliKernel.Protocol.Validity.check original).run 0 with
  | (.error error,remaining) =>
    match (CheckedFinite.check original supplied).run 0 with
    | (.error (.native actual),left) => unless actual == error && left == remaining do
        throw (IO.userError "finite gate changed the core work refusal")
    | _ => throw (IO.userError "finite gate hid the core work refusal")
  | (.ok _,_) => throw (IO.userError "expected bounded core work exhaustion")
  return refusals

private def requestCases (input supplied : ByteArray) : IO Unit := do
  let requirement := "{\"format\":\"qleisli.request\",\"version\":1,\"signature\":{\"tag\":\"unit\"},\"meaning\":{\"tag\":\"permutation\",\"table\":[0]},\"source_snapshot\":null}".toUTF8
  let original := packet input requirement
  let requested ← checked (QleisliKernel.Protocol.Validity.check original)
  unless requested do throw (IO.userError "expected an independently checked request")
  match (CheckedFinite.check original supplied).run 10000000 with
  | (.ok result,_) =>
    unless result.body == input && result.requestBytes == some requirement && result.requirement.isSome do
      throw (IO.userError "finite gate lost the original independent request")
  | (.error error,_) => throw (IO.userError ("requested finite view rejected: " ++ reprStr error))
  viewRejected original (← IO.ofExcept (encode .null)) .decodedView
  let invalid := packet input "{}".toUTF8
  match (QleisliKernel.Protocol.Validity.check invalid).run 10000000 with
  | (.error error,remaining) =>
    match (CheckedFinite.check invalid supplied).run 10000000 with
    | (.error (.native actual),left) => unless actual == error && left == remaining do
        throw (IO.userError "finite gate changed the request refusal")
    | _ => throw (IO.userError "finite gate bypassed the independent request")
  | (.ok _,_) => throw (IO.userError "invalid independent request accepted")

private def contractCases (path : System.FilePath) : IO Unit := do
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let mut requests := 0
  let mut circuits := 0
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    let kind ← IO.ofExcept ((row.getObjVal? "kind") >>= Json.getStr?)
    let actual ← if kind == "request" then do
      let input ← IO.ofExcept (row.getObjVal? "artifact")
      let requirement ← IO.ofExcept (row.getObjVal? "request")
      let original := packet input.compress.toUTF8 requirement.compress.toUTF8
      let retained ← checked (QleisliKernel.Protocol.NativeContract.checkRetained original)
      unless retained.body == input.compress.toUTF8 && retained.requestBytes == requirement.compress.toUTF8 do
        throw (IO.userError ("retained contract lost original bytes: " ++ name))
      -- Retention preserves all original checks, errors and work. This tests
      -- the executable projection as well as the separately proved equality.
      match (QleisliKernel.Protocol.NativeContract.checkRetained original).run 10000000,
          (QleisliKernel.Protocol.NativeContract.check original).run 10000000 with
      | (.ok _,left),(.ok true,remaining) => unless left == remaining do
          throw (IO.userError ("contract projection changed work: " ++ name))
      | _,_ => throw (IO.userError ("contract projection changed success: " ++ name))
      match (QleisliKernel.Protocol.NativeContract.checkRetained original).run 0,
          (QleisliKernel.Protocol.NativeContract.check original).run 0 with
      | (.error error,left),(.error actual,remaining) => unless error == actual && left == remaining do
          throw (IO.userError ("contract projection changed bounded refusal: " ++ name))
      | _,_ => throw (IO.userError ("expected bounded contract refusal: " ++ name))
      requests := requests+1
      pure (FiniteView.nativeRequest retained.request)
    else if kind == "circuit" then do
      let input ← IO.ofExcept ((row.getObjVal? "circuit") >>= QleisliKernel.Protocol.FiniteCodec.circuit)
      circuits := circuits+1
      -- This is the supplied literal caller circuit, not a contract wrapper
      -- or a reconstructed single-action surrogate.
      pure (FiniteView.circuit input)
    else throw (IO.userError "unknown contract vector kind")
    unless (← IO.ofExcept (encode actual)) == expected do
      throw (IO.userError ("typed contract/caller circuit vector mismatch: " ++ name))
  IO.println ("retained native obligations: " ++ toString requests ++
    "; literal caller circuits: " ++ toString circuits ++ "; shared vectors passed; production binding pending")

private def singleChanges (fuel : Nat) : Value → List Value :=
  Nat.rec (fun _ => []) (fun _ recurse input => match input with
    | .null => [.boolean false]
    | .boolean b => [.boolean (!b)]
    | .natural n => [.natural (n+1)]
    | .text text => [.text (text ++ "!")]
    | .array fields => .array (fields ++ [.null]) ::
      ((List.range fields.length).flatMap fun index =>
        match fields[index]? with
        | none => []
        | some field => (recurse field).map fun changed => .array (fields.set index changed))) fuel

private def callerAttachmentCases {α : Type} (base : Gate.CheckM α)
    (attach : ByteArray → List Nat → Gate.CheckM α) (description : Value)
    (indices : List Nat) (name : String) : IO Nat := do
  let supplied ← IO.ofExcept (encode description)
  match base.run 10000000 with
  | (.ok _,_) => pure ()
  | (.error error,_) => throw (IO.userError ("original caller base rejected: " ++ name ++ reprStr error))
  match (attach supplied indices).run 10000000 with
  | (.ok _,_) => pure ()
  | (.error error,_) => throw (IO.userError ("correct caller attachment rejected: " ++ name ++ reprStr error))
  let mut refusals := 0
  for changed in singleChanges 129 description do
    match (attach (← IO.ofExcept (encode changed)) indices).run 10000000 with
    | (.error .decodedView,_) => refusals := refusals+1
    | _ => throw (IO.userError ("changed caller attachment did not refuse: " ++ name))
  match (attach "QDV1".toUTF8 indices).run 10000000 with
  | (.error .invalidView,_) => pure ()
  | _ => throw (IO.userError "malformed caller attachment accepted")
  match (attach supplied [1000000]).run 10000000 with
  | (.error (.native .invalid),_) => pure ()
  | _ => throw (IO.userError "caller attachment accepted an absent receipt")
  if !indices.isEmpty then
    match (attach supplied []).run 10000000 with
    | (.error .decodedView,_) => pure ()
    | _ => throw (IO.userError "caller attachment accepted omitted aliases")
    match (attach supplied (indices ++ [0])).run 10000000 with
    | (.error .decodedView,_) => pure ()
    | _ => throw (IO.userError "caller attachment accepted an extra alias")
    if indices.contains 1 then
      match (attach supplied (indices.map fun index => if index == 0 then 1 else index)).run 10000000 with
      | (.error .decodedView,_) => pure ()
      | _ => throw (IO.userError "caller attachment accepted a different valid original slot")
  match base.run 0 with
  | (.error error,remaining) =>
    match (attach supplied indices).run 0 with
    | (.error actual,left) => unless actual == error && left == remaining do
        throw (IO.userError "caller attachment changed base work refusal")
    | _ => throw (IO.userError "caller attachment hid base work refusal")
  | (.ok _,_) => throw (IO.userError "expected exhausted caller base work")
  return refusals

private def callerCases (path refusalPath : System.FilePath) : IO Unit := do
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let mut refusals := 0
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept (row.getObjVal? "artifact")
    let indices ← IO.ofExcept ((row.getObjVal? "indices") >>= Json.getArr? >>= fun xs => xs.toList.mapM Json.getNat?)
    let description ← IO.ofExcept ((row.getObjVal? "view") >>= value 129)
    let graph ← IO.ofExcept ((row.getObjVal? "graph_view") >>= value 129)
    let suppliedGraph ← IO.ofExcept (encode graph)
    let original := packet input.compress.toUTF8
    let (artifact,order) ← checked (QleisliKernel.Protocol.Qirf.read input.compress.toUTF8)
    let root ← checked (QleisliKernel.Qirf.Validity.checkRoot artifact order)
    let supplied ← IO.ofExcept (encode description)
    let actual ← checked (Caller.origin artifact root indices)
    unless (← IO.ofExcept (encode actual)) == supplied do
      throw (IO.userError ("independent caller alias description mismatch: " ++ name))
    let exact ← checked (Caller.origin artifact root indices supplied.size)
    unless (← IO.ofExcept (encode exact)) == supplied do
      throw (IO.userError "exact caller byte capacity changed the view")
    match (Caller.origin artifact root indices (supplied.size-1)).run 10000000 with
    | (.error .limit,_) => pure ()
    | _ => throw (IO.userError "caller byte accounting omitted repeated data")
    match (Caller.origin artifact root indices).run 0 with
    | (.error (.arithmetic .workLimit),0) => pure ()
    | _ => throw (IO.userError "caller discovery work exhaustion was hidden")
    refusals := refusals + (← callerAttachmentCases (CheckedFinite.check original suppliedGraph)
      (CheckedCaller.finite original suppliedGraph) description indices name)
    -- The same independently authored bodies/caches also pass through the
    -- native-contract attachment. Only the explicit Bit root interface and
    -- empty control-sector request are added; no producer receipt is supplied.
    let fields ← IO.ofExcept input.getObj?
    let tree := Json.mkObj [("tag",.str "bit")]
    let contractInput := Json.mkObj (fields.toList.map fun (key,old) =>
      (key,if key == "root_interface" then Json.mkObj [("input",tree),("output",tree)] else old))
    let iface := Value.array [.text "root-interface",.array [.array [.text "bit"]],.array [.array [.text "bit"]]]
    let .array graphFields := graph | throw (IO.userError "caller graph is not a record")
    let .array originFields := description | throw (IO.userError "caller origin is not a record")
    let contractGraph := Value.array (graphFields.set 2 iface)
    let contractOrigin := Value.array (originFields.set 1 iface)
    let request := Json.mkObj [("format",.str "qleisli.native-contract"),("version",toJson (1 : Nat)),
      ("kind",.str "control"),("signature",tree),("axes",.arr #[])]
    let contractPacket := packet contractInput.compress.toUTF8 request.compress.toUTF8
    let contractView := Value.array [.text "native-contract",.array [.text "control",.array [.array [.text "bit"]],.array []],contractGraph,.null]
    let contractBytes ← IO.ofExcept (encode contractView)
    refusals := refusals + (← callerAttachmentCases (CheckedContract.check contractPacket contractBytes)
      (CheckedCaller.contract contractPacket contractBytes) contractOrigin indices (name ++ " native-contract"))
  let refusal ← IO.ofExcept (Json.parse (← IO.FS.readFile refusalPath))
  let original ← IO.ofExcept ((refusal.getObjVal? "original_artifact_text") >>= Json.getStr?)
  match (QleisliKernel.Protocol.Validity.check (packet original.toUTF8)).run 10000000 with
  | (.error .invalid,_) => pure ()
  | _ => throw (IO.userError "first caller phi refusal changed")
  IO.println ("caller aliases: " ++ toString rows.size ++ " finite and native-contract originals; " ++
    toString refusals ++ " divergent descriptions refused; original phi refusal rechecked")

private def completeContractCases (sourcePath path : System.FilePath) : IO Unit := do
  let sources ← IO.ofExcept (Json.parse (← IO.FS.readFile sourcePath) >>= Json.getArr?)
  let rows ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= Json.getArr?)
  let mut refusals := 0
  let mut callerRefusals := 0
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let index ← IO.ofExcept ((row.getObjVal? "source_index") >>= Json.getNat?)
    let some source := sources[index]? | throw (IO.userError "missing original contract case")
    let input ← IO.ofExcept (source.getObjVal? "artifact")
    let required ← IO.ofExcept (source.getObjVal? "request")
    let required ← match row.getObjVal? "expected_artifact" with
      | .error _ => pure required
      | .ok expected => do
        let fields ← IO.ofExcept required.getObj?
        pure (Json.mkObj (fields.toList.map fun (key,old) =>
          (key,if key == "expected_artifact" then expected else old)))
    let original := packet input.compress.toUTF8 required.compress.toUTF8
    let retained ← checked (QleisliKernel.Protocol.NativeContract.checkRetained original)
    let request ← IO.ofExcept ((source.getObjVal? "view") >>= value 129)
    let actualGraph ← IO.ofExcept ((row.getObjVal? "actual_graph") >>= value 129)
    let expectedGraph ← IO.ofExcept ((row.getObjVal? "expected_graph") >>= value 129)
    let description := Value.array [.text "native-contract",request,actualGraph,expectedGraph]
    let supplied ← IO.ofExcept (encode description)
    let .array graphFields := actualGraph | throw (IO.userError "expected actual contract graph")
    let some interface := graphFields[2]? | throw (IO.userError "missing contract interface")
    let some body := graphFields[6]? | throw (IO.userError "missing actual contract root")
    let callerDescription := Value.array [.text "caller-origin",interface,body,.array []]
    callerRefusals := callerRefusals + (← callerAttachmentCases (CheckedContract.check original supplied)
      (CheckedCaller.contract original supplied) callerDescription [] name)
    let actual ← checked (FiniteView.nativeContract retained)
    unless (← IO.ofExcept (encode actual)) == supplied do
      throw (IO.userError ("complete contract graph mismatch: " ++ name))
    match (CheckedContract.check original supplied).run 10000000 with
    | (.ok result,_) =>
      unless result.body == input.compress.toUTF8 && result.requestBytes == required.compress.toUTF8 do
        throw (IO.userError ("complete contract gate lost original bytes: " ++ name))
    | (.error error,_) => throw (IO.userError ("correct complete contract rejected: " ++ name ++ reprStr error))
    for changed in singleChanges 129 description do
      match (CheckedContract.check original (← IO.ofExcept (encode changed))).run 10000000 with
      | (.error .decodedView,_) => refusals := refusals+1
      | _ => throw (IO.userError ("changed complete contract did not refuse: " ++ name))
    match (CheckedContract.check original "QDV1".toUTF8).run 10000000 with
    | (.error .invalidView,_) => pure ()
    | _ => throw (IO.userError "malformed complete contract view accepted")
    match (QleisliKernel.Protocol.NativeContract.checkRetained original).run 0 with
    | (.error error,remaining) =>
      match (CheckedContract.check original supplied).run 0 with
      | (.error (.native actual),left) => unless actual == error && left == remaining do
          throw (IO.userError "complete contract gate changed core work refusal")
      | _ => throw (IO.userError "complete contract gate hid core refusal")
    | (.ok _,_) => throw (IO.userError "expected exhausted contract work refusal")
    match (CheckedContract.check (packet input.compress.toUTF8 "{}".toUTF8) supplied).run 10000000 with
    | (.error (.native _),_) => pure ()
    | _ => throw (IO.userError "complete contract gate bypassed mandatory request")
    let callerBytes ← IO.ofExcept (encode callerDescription)
    match (CheckedCaller.contract (packet input.compress.toUTF8 "{}".toUTF8) supplied callerBytes []).run 10000000 with
    | (.error (.native _),_) => pure ()
    | _ => throw (IO.userError "caller attachment bypassed mandatory request")
  IO.println ("pure complete contract gate: " ++ toString rows.size ++
    " original valid requests; " ++ toString refusals ++ " individual data mutations refused; production cutover pending")
  IO.println ("caller attachment across all six contract kinds: " ++ toString rows.size ++
    " original valid requests; " ++ toString callerRefusals ++ " divergent caller descriptions refused")

private def refusalCase (path : System.FilePath) (expected : QleisliKernel.Finite.Error) : IO Unit := do
  let record ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let row ← IO.ofExcept (record.getObjVal? "original_vector")
  let artifact ← IO.ofExcept (row.getObjVal? "artifact")
  let request ← IO.ofExcept (row.getObjVal? "request")
  let original := packet artifact.compress.toUTF8 request.compress.toUTF8
  match (QleisliKernel.Protocol.NativeContract.checkRetained original).run 10000000 with
  | (.error actual,_) => unless actual == expected do
      throw (IO.userError ("preserved authoring refusal changed: " ++ path.toString))
  | (.ok _,_) => throw (IO.userError ("preserved refused contract accepted: " ++ path.toString))

def main (args : List String) : IO Unit := do
  let [path,finitePath,functionPath,graphPath,contractPath,firstRefusal,secondRefusal,completeContractPath,callerPath,callerRefusal] := args |
    throw (IO.userError "expected primitive, finite, function, graph, contract, two refusal, complete-contract and two caller vector files")
  let text ← IO.FS.readFile path
  let rows ← IO.ofExcept (Json.parse text >>= Json.getArr?)
  frameCases
  for row in rows do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept ((row.getObjVal? "value") >>= value 129)
    let expected ← IO.ofExcept ((row.getObjVal? "hex") >>= Json.getStr?)
    let actual ← IO.ofExcept (encode input)
    unless hex actual == expected do
      throw (IO.userError ("canonical vector mismatch: " ++ name))
    unless framed actual do throw (IO.userError ("canonical frame rejected: " ++ name))
    for length in List.range actual.size do
      if framed (actual.extract 0 length) then throw (IO.userError "truncated frame accepted")
    if framed (actual ++ ⟨#[0]⟩) then throw (IO.userError "trailing frame bytes accepted")
  unless failed (encode (.natural (2^64))) do
    throw (IO.userError "out-of-range natural accepted")
  let atDepth := (List.range maxDepth).foldl (fun v _ => Value.array [v]) Value.null
  unless (encode atDepth).isOk && failed (encode (.array [atDepth])) do
    throw (IO.userError "canonical depth limit differs")
  unless framed (← IO.ofExcept (encode atDepth)) do
    throw (IO.userError "canonical framing depth limit differs")
  IO.println ("canonical encoding: " ++ toString rows.size ++ " shared vectors passed")
  let cases ← IO.ofExcept (Json.parse (← IO.FS.readFile finitePath) >>= Json.getArr?)
  let directory := (System.FilePath.mk finitePath).parent.getD "."
  for row in cases do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let actual ← IO.ofExcept (encode (← finite directory row))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("typed finite vector mismatch: " ++ name))
  IO.println ("typed finite data: " ++ toString cases.size ++ " shared vectors passed; no acceptance claim")
  let functions ← IO.ofExcept (Json.parse (← IO.FS.readFile functionPath) >>= Json.getArr?)
  let mut before := []
  for row in functions do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept (functionInput row)
    let receipt ← checked (QleisliKernel.Raw.BranchFunction.checkEntry before input input)
    let actual ← IO.ofExcept (encode (← checked (FiniteView.functionEvidence receipt)))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("retained function cache mismatch: " ++ name))
    before := before ++ [receipt]
  IO.println ("retained function caches: " ++ toString functions.size ++ " shared vectors passed; no production binding claim")
  let graphs ← IO.ofExcept (Json.parse (← IO.FS.readFile graphPath) >>= Json.getArr?)
  let mut gateRefusals := 0
  for row in graphs do
    let name ← IO.ofExcept ((row.getObjVal? "name") >>= Json.getStr?)
    let input ← IO.ofExcept (row.getObjVal? "artifact")
    let (artifact,order) ← checked (QleisliKernel.Protocol.Qirf.read input.compress.toUTF8)
    let retained ← checked (QleisliKernel.Qirf.Validity.checkRoot artifact order)
    let actual ← IO.ofExcept (encode (← checked (FiniteView.graph artifact retained)))
    let expected ← IO.ofExcept ((row.getObjVal? "view") >>= value 129 >>= encode)
    unless actual == expected do
      throw (IO.userError ("retained finite graph mismatch: " ++ name))
    gateRefusals := gateRefusals + (← gateCases input.compress.toUTF8
      (← IO.ofExcept ((row.getObjVal? "view") >>= value 129)))
    if name == "unit-interface" then requestCases input.compress.toUTF8 expected
  IO.println ("retained finite graphs: " ++ toString graphs.size ++ " shared vectors passed; no production binding claim")
  IO.println ("pure finite view gate: " ++ toString graphs.size ++ " original valid artifacts; " ++
    toString gateRefusals ++ " divergent candidate refusals; CLI/protocol cutover still pending")
  contractCases contractPath
  completeContractCases contractPath completeContractPath
  callerCases callerPath callerRefusal
  refusalCase firstRefusal .invalid
  refusalCase secondRefusal .equation
  IO.println "preserved original contract authoring refusals: 2 rechecked"
