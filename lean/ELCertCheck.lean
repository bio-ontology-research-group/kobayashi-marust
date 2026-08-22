import ContextCalculus.ELCompletionPublication

open Lean
open ContextCalculus.ELCompletion

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCertificate ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "ELC certificate accepted: exact taxonomy and inconsistency result"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "ELC certificate rejected: trace is unsound or materialization is not closed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"ELC certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"ELC certificate read error: {error}"
    return (2 : UInt32)

def checkResidualFile (symbolCount : Nat) (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireResidualCompilation ← fromJson? json
      document.check symbolCount
    match result with
    | .ok true =>
        IO.println "ELC residual compilation accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "ELC residual compilation rejected: evidence mismatch"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"ELC residual compilation rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"ELC residual compilation read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | ["--residual", symbolCount, path] =>
      match symbolCount.toNat? with
      | some count => checkResidualFile count path
      | none => do
          IO.eprintln s!"invalid symbol count: {symbolCount}"
          return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: elc-cert-check CERTIFICATE.json | --residual SYMBOL_COUNT PAYLOAD.json"
      return (2 : UInt32)
