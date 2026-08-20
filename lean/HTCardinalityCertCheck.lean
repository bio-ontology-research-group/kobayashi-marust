import ContextCalculus.HypertableauCardinalityWire

open Lean
open ContextCalculus.Hypertableau

def checkCardinalityFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCardinalityEqCertificate ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT cardinality certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT cardinality certificate rejected: semantic evidence check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT cardinality certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT cardinality certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkCardinalityFile path
  | _ => do
      IO.eprintln "usage: ht-cardinality-cert-check CERTIFICATE.json"
      return (2 : UInt32)
