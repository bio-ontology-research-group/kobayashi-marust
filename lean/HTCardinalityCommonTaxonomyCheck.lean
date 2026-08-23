import ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication
import ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication
import ContextCalculus.HTBundleCardinalityTaxonomyCommonPublication

open Lean
open ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication
open ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication
open ContextCalculus.HTBundleCardinalityTaxonomyCommonPublication

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let json ← match Json.parse input with
      | .ok value => pure value
      | .error message => throw <| IO.userError message
    let direct : Except String Bool := do
      let document : WireDirectCardinalityTaxonomyPublication ← fromJson? json
      document.check
    let result : Except String Bool := match direct with
      | .ok accepted => .ok accepted
      | .error directError =>
          let mixed : Except String Bool := do
            let document : WireMixedCardinalityTaxonomyPublication ← fromJson? json
            document.check
          match mixed with
          | .ok accepted => .ok accepted
          | .error mixedError =>
              let bundle : Except String Bool := do
                let document : WireBundleCardinalityTaxonomyPublication ← fromJson? json
                document.check
              match bundle with
              | .ok accepted => .ok accepted
              | .error bundleError => .error
                  s!"no common cardinality taxonomy format matched: direct ({directError}); mixed ({mixedError}); bundle ({bundleError})"
    match result with
    | .ok true =>
        IO.println "common HT cardinality taxonomy accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "common HT cardinality taxonomy rejected"
        return (1 : UInt32)
    | .error message =>
        IO.eprintln s!"common HT cardinality taxonomy rejected: {message}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"common HT cardinality taxonomy read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-cardinality-common-taxonomy-check PUBLICATION.json"
      return (2 : UInt32)
