import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomySourceWire

open Lean
open ContextCalculus.Hypertableau

def checkDirectNativeABoxCardinalityTaxonomyFile
    (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireDirectNativeABoxCardinalityTaxonomyMatrix ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT direct native ABox cardinality taxonomy accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT direct native ABox cardinality taxonomy rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT direct native ABox cardinality taxonomy rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT direct native ABox cardinality taxonomy read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkDirectNativeABoxCardinalityTaxonomyFile path
  | _ => do
      IO.eprintln "usage: ht-direct-native-abox-cardinality-taxonomy-cert-check CERTIFICATE.json"
      return (2 : UInt32)
