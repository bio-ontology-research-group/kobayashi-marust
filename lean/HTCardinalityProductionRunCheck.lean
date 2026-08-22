import ContextCalculus.HypertableauCardinalityProductionRunWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCardinalityProductionRun ← fromJson? json
      return document.check
    match result with
    | .ok true => IO.println "HT cardinality production run accepted"; return (0 : UInt32)
    | .ok false => IO.eprintln "HT cardinality production run rejected"; return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT cardinality production run rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT cardinality production run read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: ht-cardinality-production-run-check RUN.json" *>
      pure (2 : UInt32)
