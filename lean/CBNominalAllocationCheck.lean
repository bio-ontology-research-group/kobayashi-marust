import ContextCalculus.CBNominalAllocationWire

open Lean
open ContextCalculus.CBNominalAllocationWire

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireNominalAllocation ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB Nom allocation certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB Nom allocation certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB Nom allocation certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB Nom allocation certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-nominal-allocation-check CERTIFICATE.json"
      return (2 : UInt32)
