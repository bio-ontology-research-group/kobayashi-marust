import ContextCalculus.CBBlockedCarrierWire

open Lean
open ContextCalculus.CBBlockedCarrierWire

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireBlockedCarrierDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB blocked-carrier certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB blocked-carrier certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB blocked-carrier certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB blocked-carrier certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-blocked-carrier-check CERTIFICATE.json"
      return (2 : UInt32)
