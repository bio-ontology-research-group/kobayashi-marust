import ContextCalculus.HypertableauOrdinaryTaxonomyProductionRunWire

open Lean
open ContextCalculus.Hypertableau

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => do
      try
        let input ← IO.FS.readFile path
        let result : Except String Bool := do
          let json ← Json.parse input
          let document : WireOrdinaryTaxonomyProductionRun ← fromJson? json
          return document.check
        match result with
        | .ok true => do
            IO.println "HT ordinary taxonomy production run accepted"
            return (0 : UInt32)
        | .ok false => do
            IO.eprintln "HT ordinary taxonomy production run rejected"
            return (1 : UInt32)
        | .error error => do
            IO.eprintln s!"HT ordinary taxonomy production run rejected: {error}"
            return (1 : UInt32)
      catch error =>
        IO.eprintln s!"HT ordinary taxonomy production run read error: {error}"
        return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: ht-ordinary-taxonomy-production-run-check CERTIFICATE.json"
      return (2 : UInt32)
