import ContextCalculus.HypertableauJointSourceClassificationWire

open Lean
open ContextCalculus.Hypertableau

def checkJointNativeABoxClassificationJson (json : Json) : Except String Bool :=
  match (fromJson? json : Except String
      WireJointDirectNativeABoxCardinalityClassification) with
  | .ok document => document.check
  | .error directCardinalityError =>
      match (fromJson? json : Except String
          WireJointMixedNativeABoxCardinalityClassification) with
      | .ok document => document.check
      | .error mixedCardinalityError =>
          match (fromJson? json : Except String
              WireJointBundleNativeABoxCardinalityClassification) with
          | .ok document => document.check
          | .error bundleCardinalityError =>
              match (fromJson? json : Except String
                  WireJointDirectNativeABoxClassification) with
              | .ok document => document.check
              | .error directError =>
                  match (fromJson? json : Except String
                      WireJointMixedNativeABoxClassification) with
                  | .ok document => document.check
                  | .error mixedError =>
                      match (fromJson? json : Except String
                          WireJointBundleNativeABoxClassification) with
                      | .ok document => document.check
                      | .error bundleError => throw
                          s!"unsupported joint native ABox classification format; direct-cardinality: {directCardinalityError}; mixed-cardinality: {mixedCardinalityError}; bundle-cardinality: {bundleCardinalityError}; direct: {directError}; mixed: {mixedError}; bundle: {bundleError}"

def checkJointNativeABoxClassificationFile
    (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      checkJointNativeABoxClassificationJson json
    match result with
    | .ok true =>
        IO.println "joint source-composed HT native ABox classification accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "joint source-composed HT native ABox classification rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"joint source-composed HT native ABox classification rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"joint source-composed HT native ABox classification read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkJointNativeABoxClassificationFile path
  | _ => do
      IO.eprintln "usage: ht-joint-native-abox-classification-cert-check CERTIFICATE.json"
      return (2 : UInt32)
