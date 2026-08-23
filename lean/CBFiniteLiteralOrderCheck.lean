import ContextCalculus.CBFiniteLiteralOrderWire

open Lean
open ContextCalculus.CBFiniteLiteralOrderWire

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireFiniteLiteralOrderDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB finite literal-order certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB finite literal-order certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB finite literal-order certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB finite literal-order certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-finite-literal-order-check CERTIFICATE.json"
      return (2 : UInt32)
