import ContextCalculus.HypertableauSourceBoundOrdinaryTaxonomyWire

open Lean
open ContextCalculus.Hypertableau

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => do
      try
        let input ← IO.FS.readFile path
        let result : Except String Bool := do
          let json ← Json.parse input
          let document : WireSourceBoundOrdinaryTaxonomy ← fromJson? json
          return document.check
        match result with
        | .ok true => do
            IO.println "HT source-bound ordinary taxonomy accepted"
            return (0 : UInt32)
        | .ok false => do
            let details : Except String String := do
              let json ← Json.parse input
              let document : WireSourceBoundOrdinaryTaxonomy ← fromJson? json
              let sourceDetail := match document.source.decode with
                | .ok _ => "ok"
                | .error error => error
              let targetCount := match document.source.payload with
                | .plain certificate => certificate.ontology.length
                | .mixed certificate => certificate.ontology.length
              return s!"source={document.source.check} ({sourceDetail}; normalization={document.source.normalization.length}, target={targetCount}), runs={document.runs.check}, bound={document.payloadBoundB}"
            let message := match details with
              | .ok message => message
              | .error _ => "diagnostic unavailable"
            IO.eprintln s!"HT source-bound ordinary taxonomy rejected: {message}"
            return (1 : UInt32)
        | .error error => do
            IO.eprintln s!"HT source-bound ordinary taxonomy rejected: {error}"
            return (1 : UInt32)
      catch error =>
        IO.eprintln s!"HT source-bound ordinary taxonomy read error: {error}"
        return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: ht-source-bound-ordinary-taxonomy-check CERTIFICATE.json"
      return (2 : UInt32)
