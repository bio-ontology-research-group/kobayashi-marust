import ContextCalculus.HypertableauProductionBlockingWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireProductionBlockingTable ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT production blocking table accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT production blocking table rejected: incomplete or invalid options"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT production blocking table rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT production blocking table read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-production-blocking-check TABLE.json"
      return (2 : UInt32)
