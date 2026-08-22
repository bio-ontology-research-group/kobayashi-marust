import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxCardinalityTaxonomyDecisionFile
    (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireNativeABoxCardinalityTaxonomyDecision ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT native ABox cardinality taxonomy decision accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT native ABox cardinality taxonomy decision rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT native ABox cardinality taxonomy decision rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT native ABox cardinality taxonomy decision read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxCardinalityTaxonomyDecisionFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-cardinality-taxonomy-decision-check CERTIFICATE.json"
      return (2 : UInt32)
