import ContextCalculus.CBSourceProductionTaxonomyWire

open Lean
open ContextCalculus.CBSourceProductionTaxonomyWire

#print axioms DecodedDocument.publishes_source_exactly
#print axioms WireDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "source-bound shared-production CB taxonomy accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "source-bound shared-production CB taxonomy rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"source-bound shared-production CB taxonomy rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"source-bound shared-production CB taxonomy read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-source-production-taxonomy-check CERTIFICATE.json"
      return (2 : UInt32)
