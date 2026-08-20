import ContextCalculus.HypertableauAnchoredWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireAnchoredPremises ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "anchored HT premises accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "anchored HT premises rejected: semantic premise check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"anchored HT premises rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"anchored HT premise read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-anchored-premises-check CERTIFICATE.json"
      return (2 : UInt32)
