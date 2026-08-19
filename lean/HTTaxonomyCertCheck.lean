import ContextCalculus.HypertableauTaxonomyWire

open Lean
open ContextCalculus.Hypertableau

def checkTaxonomyFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String DecodedTaxonomyCertificate := do
      let json ← Json.parse input
      let document : WireTaxonomyCertificate ← fromJson? json
      document.decode
    match result with
    | .ok _ =>
        IO.println "HT taxonomy certificate accepted"
        return (0 : UInt32)
    | .error error =>
        IO.eprintln s!"HT taxonomy certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT taxonomy certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkTaxonomyFile path
  | _ => do
      IO.eprintln "usage: ht-taxonomy-cert-check CERTIFICATE.json"
      return (2 : UInt32)
