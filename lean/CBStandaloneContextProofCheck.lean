import ContextCalculus.CBStandaloneContextProofWire

open Lean
open ContextCalculus.CBStandaloneContextProofWire

#print axioms DecodedStandaloneNode.contextValid
#print axioms WireStandaloneDocument.check

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireStandaloneDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "source-bound chronological CB context proof accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "source-bound chronological CB context proof rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"source-bound chronological CB context proof rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"source-bound chronological CB context proof read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-standalone-context-proof-check CERTIFICATE.json"
      return (2 : UInt32)
