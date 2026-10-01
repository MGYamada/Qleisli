import Protocol
import Init.System.IO

/-! Unproved transport adapter for the existing experimental profiles.
Inputs remain untrusted until checked by the independently specified pure kernel.
Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0 -/

namespace QleisliKernel.Cli

inductive Stage where
  | artifact
  | requirement
  | verification
  | usage

inductive Code where
  | accepted
  | rejected
  | syntax
  | limit
  | io
  | usage

namespace Internal

def stageName : Stage → String
  | .artifact => "artifact"
  | .requirement => "requirement"
  | .verification => "verification"
  | .usage => "usage"

def codeName : Code → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .syntax => "syntax"
  | .limit => "limit"
  | .io => "io"
  | .usage => "usage"

/-- Callers supply closed profile/code strings and internally rendered fields. -/
def emitResult (profile : String) (accepted : Bool) (code : String) (stage : Stage)
    (fields : String := "") : IO Unit := do
  let truth := if accepted then "true" else "false"
  IO.println ("{\"format\":\"qleisli.kernel-result\",\"version\":1," ++
    "\"profile\":\"" ++ profile ++ "\",\"accepted\":" ++ truth ++
    ",\"code\":\"" ++ code ++ "\",\"stage\":\"" ++ stageName stage ++ "\"" ++ fields ++ "}")

def emit (accepted : Bool) (code : Code) (stage : Stage) : IO Unit :=
  emitResult "phase256-word-v1" accepted (codeName code) stage


def readBytes (handle : IO.FS.Handle) (fuel : Nat)
    (initial : ByteArray) : IO (Except Code String) :=
  -- An explicit structural recursor keeps the compiled project declaration
  -- total as well as its logical definition; no generated partial recursion
  -- replacement is needed for this IO loop.
  Nat.rec (motive := fun _ => ByteArray → IO (Except Code String))
    (fun _ => pure (.error .limit))
    (fun _ next bytes => do
      if bytes.size > Protocol.maxInputBytes then return .error .limit
      -- At most limit+1 bytes are ever retained, even for a growing file or
      -- short reads. Each nonempty read consumes one unit of explicit fuel.
      let remaining := Protocol.maxInputBytes + 1 - bytes.size
      let chunk ← handle.read (USize.ofNat (min 4096 remaining))
      if chunk.isEmpty then
        match String.fromUTF8? bytes with
        | some text => return .ok text
        | none => return .error .syntax
      else
        next (bytes ++ chunk))
    fuel initial

def readInput (path : System.FilePath) : IO (Except Code String) := do
  try
    IO.FS.withFile path .read fun handle =>
      readBytes handle (Protocol.maxInputBytes + 2) ByteArray.empty
  catch _ =>
    return .error .io

def parseCode : Protocol.Error → Code
  | .syntax => .syntax
  | .limit => .limit

/-- Keep artifact/requirement diagnostics in their original IO order. -/
def readParsed {α : Type} (path : String) (parse : String → Except Protocol.Error α)
    (stage : Stage) (onError : Code → Stage → IO Unit) : IO (Option α) := do
  match ← readInput path with
  | .error code => onError code stage *> pure none
  | .ok text => match parse text with
    | .error code => onError (parseCode code) stage *> pure none
    | .ok value => pure (some value)

end Internal
end QleisliKernel.Cli
