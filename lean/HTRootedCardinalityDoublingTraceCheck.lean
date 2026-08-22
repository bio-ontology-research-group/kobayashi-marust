import ContextCalculus.HypertableauCardinalityDoublingTraceWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRootedCardinalityDoublingTrace ← fromJson? json
      return document.check
    match result with
    | .ok true => IO.println "HT rooted cardinality doubling trace accepted"; return (0 : UInt32)
    | .ok false => IO.eprintln "HT rooted cardinality doubling trace rejected"; return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT rooted cardinality doubling trace rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT rooted cardinality doubling trace read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: ht-rooted-cardinality-doubling-trace-check TRACE.json" *>
      pure (2 : UInt32)
