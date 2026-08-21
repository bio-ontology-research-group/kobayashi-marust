import ContextCalculus.HypertableauNativeABoxSourceDecisionWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxSourceDecisionFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      match (fromJson? json : Except String
          WireBundleNativeABoxDecisionCertificate) with
      | .ok document => document.check
      | .error bundleError =>
          match (fromJson? json : Except String
              WireMixedNativeABoxDecisionCertificate) with
          | .ok document => document.check
          | .error mixedError =>
              match (fromJson? json : Except String
                  WireDirectNativeABoxDecisionCertificate) with
              | .ok document => document.check
              | .error directError =>
                  throw s!"neither bundle ({bundleError}), mixed ({mixedError}), nor direct ({directError}) native ABox source decision JSON"
    match result with
    | .ok true =>
        IO.println "HT native ABox source decision certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT native ABox source decision certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT native ABox source decision certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT native ABox source decision certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxSourceDecisionFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-source-decision-cert-check CERTIFICATE.json"
      return (2 : UInt32)
