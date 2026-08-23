import ContextCalculus.CBLiveExactTaxonomyPublication

open Lean
open ContextCalculus.CBLiveExactTaxonomyPublication

#print axioms DecodedLiveExactTaxonomyPublication.cell_exact
#print axioms DecodedLiveExactTaxonomyPublication.cell_source_exact
#print axioms WireLiveExactTaxonomyPublication.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireLiveExactTaxonomyPublication ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "live exact CB taxonomy publication accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "live exact CB taxonomy publication rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"live exact CB taxonomy publication rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"live exact CB taxonomy publication read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-live-exact-taxonomy-publication-check CERTIFICATE.json"
      return (2 : UInt32)
