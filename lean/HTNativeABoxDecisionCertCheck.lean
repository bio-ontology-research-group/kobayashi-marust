import ContextCalculus.HypertableauNativeABoxModelWire

open Lean
open ContextCalculus.Hypertableau

def checkNativeABoxDecisionFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      match (fromJson? json : Except String
          WireNativeABoxCardinalityDecisionCertificate) with
      | .ok document => document.check
      | .error cardinalityError =>
          match (fromJson? json : Except String WireNativeABoxDecisionCertificate) with
          | .ok document => document.check
          | .error nativeError =>
              throw s!"neither native ABox cardinality ({cardinalityError}) nor native ABox ({nativeError}) decision JSON"
    match result with
    | .ok true =>
        IO.println "HT native ABox decision certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT native ABox decision certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT native ABox decision certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT native ABox decision certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkNativeABoxDecisionFile path
  | _ => do
      IO.eprintln "usage: ht-native-abox-decision-cert-check CERTIFICATE.json"
      return (2 : UInt32)
