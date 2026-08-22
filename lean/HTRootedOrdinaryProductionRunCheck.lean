import ContextCalculus.HypertableauRootedOrdinaryProductionRunWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRootedOrdinaryProductionRun ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "HT rooted ordinary production run accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT rooted ordinary production run rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT rooted ordinary production run rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT rooted ordinary production run read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: ht-rooted-ordinary-production-run-check RUN.json" *>
      pure (2 : UInt32)
