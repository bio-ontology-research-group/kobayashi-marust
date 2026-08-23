import ContextCalculus.CBBlockedGroundSaturationWire

open Lean
open ContextCalculus.CBBlockedGroundSaturationWire

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireBlockedGroundSaturationDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB blocked-ground saturation certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB blocked-ground saturation certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB blocked-ground saturation certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB blocked-ground saturation certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-blocked-ground-saturation-check CERTIFICATE.json"
      return (2 : UInt32)
