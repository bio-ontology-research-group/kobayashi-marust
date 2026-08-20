import ContextCalculus.HypertableauAnchoredEqualityWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireAnchoredEqCertificate ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "equality-backed anchored HT certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "equality-backed anchored HT certificate rejected: semantic check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"equality-backed anchored HT certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"equality-backed anchored HT certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-anchored-eq-cert-check CERTIFICATE.json"
      return (2 : UInt32)
