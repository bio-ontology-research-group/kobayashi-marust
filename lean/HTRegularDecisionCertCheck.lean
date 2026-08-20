import ContextCalculus.HypertableauRegularDecisionWire

open Lean
open ContextCalculus.Hypertableau

def checkRegularDecisionFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRegularDecisionCertificate ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT regular decision certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT regular decision certificate rejected: semantic evidence check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT regular decision certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT regular decision certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkRegularDecisionFile path
  | _ => do
      IO.eprintln "usage: ht-regular-decision-cert-check CERTIFICATE.json"
      return (2 : UInt32)
