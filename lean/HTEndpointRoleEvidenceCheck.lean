import ContextCalculus.HypertableauEndpointRoleEvidenceWire

open Lean
open ContextCalculus.Hypertableau

def checkEndpointRoleEvidenceFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireEndpointRoleEvidenceDocument ← fromJson? json
      return (← document.decode).check
    match result with
    | .ok true =>
        IO.println "HT endpoint-role evidence accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT endpoint-role evidence rejected: derivation check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT endpoint-role evidence rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT endpoint-role evidence read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkEndpointRoleEvidenceFile path
  | _ => do
      IO.eprintln "usage: ht-endpoint-role-evidence-check EVIDENCE.json"
      return (2 : UInt32)
