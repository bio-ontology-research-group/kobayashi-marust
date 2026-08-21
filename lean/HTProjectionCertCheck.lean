import ContextCalculus.HypertableauBundleProjectionWire
import ContextCalculus.HypertableauBundleCardinalityProjectionWire
import ContextCalculus.HypertableauMixedCardinalityProjectionWire
import ContextCalculus.HypertableauDirectCardinalityProjectionWire
import ContextCalculus.HypertableauNativeABoxProjectionWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      match (fromJson? json : Except String WireBundleNativeABoxRefutation) with
      | .ok document => document.check
      | .error bundleNativeABoxRefutationError =>
       match (fromJson? json : Except String WireBundleNativeABoxCardinalityRefutation) with
       | .ok document => document.check
       | .error bundleNativeABoxCardinalityRefutationError =>
       match (fromJson? json : Except String WireMixedNativeABoxCardinalityRefutation) with
       | .ok document => document.check
       | .error mixedNativeABoxCardinalityRefutationError =>
       match (fromJson? json : Except String WireDirectNativeABoxCardinalityRefutation) with
       | .ok document => document.check
       | .error directNativeABoxCardinalityRefutationError =>
       match (fromJson? json : Except String WireNativeABoxCardinalityRefutation) with
       | .ok document => document.check
       | .error nativeABoxCardinalityRefutationError =>
       match (fromJson? json : Except String WireMixedNativeABoxRefutation) with
      | .ok document => document.check
      | .error mixedNativeABoxRefutationError =>
       match (fromJson? json : Except String WireDirectNativeABoxRefutation) with
      | .ok document => document.check
      | .error directNativeABoxRefutationError =>
       match (fromJson? json : Except String WireNativeABoxRefutation) with
      | .ok document => document.check
      | .error nativeABoxRefutationError =>
       match (fromJson? json : Except String WireNativeABoxSeed) with
      | .ok document => document.check
      | .error nativeABoxSeedError =>
       match (fromJson? json : Except String WireNativeABox) with
      | .ok document => document.check
      | .error nativeABoxError =>
       match (fromJson? json : Except String WireBundleCardinalityProjection) with
      | .ok document => document.check
      | .error bundleCardinalityError =>
       match (fromJson? json : Except String WireMixedCardinalityProjection) with
       | .ok document => document.check
       | .error mixedCardinalityError =>
        match (fromJson? json : Except String WireDirectCardinalityProjection) with
      | .ok document => document.check
      | .error combinedError =>
        match (fromJson? json : Except String WireCardinalityProjection) with
        | .ok document => document.check
        | .error cardinalityError =>
          match (fromJson? json : Except String WireBundleProjection) with
          | .ok document => document.check
          | .error bundleError =>
              match (fromJson? json : Except String WireMixedProjection) with
              | .ok document => document.check
              | .error mixedError =>
                  match (fromJson? json : Except String WireDirectProjection) with
                  | .ok document => document.check
                  | .error directError =>
                      throw s!"neither bundle native-ABox refutation ({bundleNativeABoxRefutationError}), bundle native-ABox cardinality refutation ({bundleNativeABoxCardinalityRefutationError}), mixed native-ABox cardinality refutation ({mixedNativeABoxCardinalityRefutationError}), direct native-ABox cardinality refutation ({directNativeABoxCardinalityRefutationError}), native-ABox cardinality refutation ({nativeABoxCardinalityRefutationError}), mixed native-ABox refutation ({mixedNativeABoxRefutationError}), direct native-ABox refutation ({directNativeABoxRefutationError}), native-ABox refutation ({nativeABoxRefutationError}), native-ABox seed ({nativeABoxSeedError}), native-ABox ({nativeABoxError}), bundle-cardinality ({bundleCardinalityError}), mixed-cardinality ({mixedCardinalityError}), direct-cardinality ({combinedError}), cardinality ({cardinalityError}), bundle ({bundleError}), mixed ({mixedError}), nor direct ({directError}) projection JSON"
    match result with
    | .ok true =>
        IO.println "HT source projection accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT source projection rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT source projection rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT source projection read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-projection-cert-check PROJECTION.json"
      return (2 : UInt32)
