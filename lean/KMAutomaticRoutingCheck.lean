import ContextCalculus.KMAutomaticRouting

open Lean
open ContextCalculus.KMAutomaticRouting

#print axioms WireSelection.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireSelection ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "automatic routing decision accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "automatic routing decision rejected: selected route differs"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"automatic routing decision rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"automatic routing decision read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: km-automatic-routing-check DECISION.json"
      return (2 : UInt32)
