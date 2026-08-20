import ContextCalculus.HypertableauCardinalityTaxonomyWire
import ContextCalculus.HypertableauNormalizedTaxonomyWire

open Lean
open ContextCalculus.Hypertableau

def checkTaxonomyFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Unit := do
      let json ← Json.parse input
      let versionValue ← json.getObjVal? "version"
      let version : Nat ← fromJson? versionValue
      if version = 6 || version = 7 then
        let document : WireNormalizedCardinalityTaxonomyCertificate ← fromJson? json
        let _ ← document.decode
        return ()
      else if version = 5 then
        let document : WireCardinalityTaxonomyCertificate ← fromJson? json
        let _ ← document.decode
        return ()
      else if version = 3 || version = 4 then
        let document : WireNormalizedTaxonomyCertificate ← fromJson? json
        let _ ← document.decode
        return ()
      else if version = 2 then
        let document : WireMixedTaxonomyCertificate ← fromJson? json
        let _ ← document.decode
        return ()
      else
        let document : WireTaxonomyCertificate ← fromJson? json
        let _ ← document.decode
        return ()
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
