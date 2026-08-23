import ContextCalculus.CBLocalFactorClosureWire

open Lean
open ContextCalculus.CBLocalFactorClosureWire

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireLocalFactorClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB local Factor-closure certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB local Factor-closure certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB local Factor-closure certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB local Factor-closure certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-local-factor-closure-check CERTIFICATE.json"
      return (2 : UInt32)
