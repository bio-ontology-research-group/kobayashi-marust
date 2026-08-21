import ContextCalculus.HypertableauNativeABoxTaxonomySourceWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxTaxonomySourceFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      match (fromJson? json : Except String WireBundleNativeABoxTaxonomyMatrix) with
      | .ok document => document.check
      | .error bundleError =>
          match (fromJson? json : Except String WireMixedNativeABoxTaxonomyMatrix) with
          | .ok document => document.check
          | .error mixedError =>
              match (fromJson? json : Except String WireDirectNativeABoxTaxonomyMatrix) with
              | .ok document => document.check
              | .error directError =>
                  throw s!"no native ABox taxonomy source format matched: bundle ({bundleError}), mixed ({mixedError}), direct ({directError})"
    match result with
    | .ok true =>
        IO.println "source-composed HT native ABox taxonomy accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "source-composed HT native ABox taxonomy rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"source-composed HT native ABox taxonomy rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"source-composed HT native ABox taxonomy read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxTaxonomySourceFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-taxonomy-source-cert-check CERTIFICATE.json"
      return (2 : UInt32)
