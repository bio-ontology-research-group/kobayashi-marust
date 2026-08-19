import ContextCalculus.HypertableauEqualityWire

open Lean
open ContextCalculus.Hypertableau

def checkEqFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireEqCertificate ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT equality certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT equality certificate rejected: semantic evidence check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT equality certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT equality certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkEqFile path
  | _ => do
      IO.eprintln "usage: ht-eq-cert-check CERTIFICATE.json"
      return (2 : UInt32)
