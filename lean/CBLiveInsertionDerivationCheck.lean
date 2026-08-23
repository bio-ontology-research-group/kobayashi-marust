import ContextCalculus.CBLiveInsertionDerivation

open Lean
open ContextCalculus.CBLiveInsertionDerivation

#print axioms WireLiveInsertionDerivationDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireLiveInsertionDerivationDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB live insertion-derivation certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB live insertion-derivation certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB live insertion-derivation certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB live insertion-derivation certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-live-insertion-derivation-check CERTIFICATE.json"
      return (2 : UInt32)
