import ContextCalculus.HypertableauCoverObstructionWire

open Lean
open ContextCalculus.Hypertableau

def checkCoverObstructionFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRegularCoverObstruction ← fromJson? json
      return (← document.decode).check
    match result with
    | .ok true =>
        IO.println "HT regular cover obstruction accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT regular cover obstruction rejected: witness is not an obstruction"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT regular cover obstruction rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT regular cover obstruction read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkCoverObstructionFile path
  | _ => do
      IO.eprintln "usage: ht-cover-obstruction-check WITNESS.json"
      return (2 : UInt32)
