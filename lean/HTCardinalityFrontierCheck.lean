import ContextCalculus.HypertableauCardinalityFrontierStateWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCardinalityAddressRefinementDocument ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "HT cardinality frontier accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT cardinality frontier rejected: address refinement check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT cardinality frontier rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT cardinality frontier read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-cardinality-frontier-check FRONTIER.json"
      return (2 : UInt32)
