import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomySourceWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxCardinalityTaxonomySourceJson (json : Json) : Except String Bool :=
  match (fromJson? json : Except String
      WireDirectNativeABoxCardinalityTaxonomyMatrix) with
  | .ok direct => direct.check
  | .error directError =>
      match (fromJson? json : Except String
          WireMixedNativeABoxCardinalityTaxonomyMatrix) with
      | .ok mixed => mixed.check
      | .error mixedError => throw
          s!"unsupported native ABox cardinality taxonomy source format; direct: {directError}; mixed: {mixedError}"

def checkNativeABoxCardinalityTaxonomySourceFile
    (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      checkNativeABoxCardinalityTaxonomySourceJson json
    match result with
    | .ok true =>
        IO.println "HT native ABox cardinality taxonomy source accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT native ABox cardinality taxonomy source rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT native ABox cardinality taxonomy source rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT native ABox cardinality taxonomy source read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxCardinalityTaxonomySourceFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-cardinality-taxonomy-source-cert-check CERTIFICATE.json"
      return (2 : UInt32)
