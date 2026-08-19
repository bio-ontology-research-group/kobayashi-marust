import ContextCalculus.HypertableauNormalizedWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let versionValue ← json.getObjVal? "version"
      let version : Nat ← fromJson? versionValue
      if version = 3 then
        let document : WireNormalizedCertificate ← fromJson? json
        document.check
      else if version = 2 then
        let document : WireEqCertificate ← fromJson? json
        document.check
      else
        let document : WireCertificate ← fromJson? json
        document.check
    match result with
    | .ok true =>
        IO.println "HT certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT certificate rejected: semantic evidence check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-cert-check CERTIFICATE.json"
      return (2 : UInt32)
