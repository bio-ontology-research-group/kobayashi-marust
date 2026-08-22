import ContextCalculus.HypertableauExecutablePublicationWire

open Lean
open ContextCalculus.Hypertableau

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => do
      try
        let input ← IO.FS.readFile path
        let accepted : Except String (String × Bool) := do
          let json ← Json.parse input
          match (fromJson? json : Except String WireExecutableHTGlobalPublication) with
          | .ok document => return ("global", document.check)
          | .error globalError =>
              match (fromJson? json : Except String WireExecutableHTTaxonomyPublication) with
              | .ok document => return ("taxonomy", document.check)
              | .error taxonomyError =>
                  throw s!"not a global ({globalError}) or taxonomy ({taxonomyError}) publication"
        match accepted with
        | .ok (kind, true) =>
            IO.println s!"executable HT {kind} publication accepted"
            return (0 : UInt32)
        | .ok (kind, false) =>
            IO.eprintln s!"executable HT {kind} publication rejected"
            return (1 : UInt32)
        | .error error =>
            IO.eprintln s!"executable HT publication rejected: {error}"
            return (1 : UInt32)
      catch error =>
        IO.eprintln s!"executable HT publication read error: {error}"
        return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: ht-executable-publication-check CERTIFICATE.json"
      return (2 : UInt32)
