import ContextCalculus.CBLiveTaxonomyPublication

open Lean
open ContextCalculus.CBLiveTaxonomyPublication

#print axioms WireLiveTaxonomyPublication.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireLiveTaxonomyPublication ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "live CB taxonomy publication accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "live CB taxonomy publication rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"live CB taxonomy publication rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"live CB taxonomy publication read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-live-taxonomy-publication-check CERTIFICATE.json"
      return (2 : UInt32)
