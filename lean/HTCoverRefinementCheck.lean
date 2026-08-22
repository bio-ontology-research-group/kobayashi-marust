import ContextCalculus.HypertableauCoverRefinementWire

open Lean
open ContextCalculus.Hypertableau

def checkCoverRefinementFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRegularCoverRefinement ← fromJson? json
      return (← document.decode).check
    match result with
    | .ok true =>
        IO.println "HT regular cover refinement accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT regular cover refinement rejected: evidence check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT regular cover refinement rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT regular cover refinement read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkCoverRefinementFile path
  | _ => do
      IO.eprintln "usage: ht-cover-refinement-check REFINEMENT.json"
      return (2 : UInt32)
