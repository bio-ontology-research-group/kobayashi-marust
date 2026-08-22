import ContextCalculus.HypertableauDoublingTraceWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireAddressDoublingTrace ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "HT frontier-doubling trace accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT frontier-doubling trace rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT frontier-doubling trace rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT frontier-doubling trace read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-doubling-trace-check TRACE.json"
      return (2 : UInt32)
