import ContextCalculus.HypertableauNativeABoxTaxonomyRunMatrixWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxTaxonomyRunMatrixFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireNativeABoxTaxonomyRunMatrix ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "HT native ABox taxonomy run matrix accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT native ABox taxonomy run matrix rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT native ABox taxonomy run matrix rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT native ABox taxonomy run matrix read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxTaxonomyRunMatrixFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-taxonomy-run-matrix-check CERTIFICATE.json"
      return (2 : UInt32)
