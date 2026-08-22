import ContextCalculus.HypertableauAddressRefinementWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireAddressRefinementDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT address refinement accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT address refinement rejected: state/address mismatch"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT address refinement rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT address refinement read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-address-refinement-check DOCUMENT.json"
      return (2 : UInt32)
