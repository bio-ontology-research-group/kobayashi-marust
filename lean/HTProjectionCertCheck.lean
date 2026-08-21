import ContextCalculus.HypertableauBundleProjectionWire
import ContextCalculus.HypertableauCardinalityProjectionWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      match (fromJson? json : Except String WireCardinalityProjection) with
      | .ok document => document.check
      | .error cardinalityError =>
          match (fromJson? json : Except String WireBundleProjection) with
          | .ok document => document.check
          | .error bundleError =>
              match (fromJson? json : Except String WireMixedProjection) with
              | .ok document => document.check
              | .error mixedError =>
                  match (fromJson? json : Except String WireDirectProjection) with
                  | .ok document => document.check
                  | .error directError =>
                      throw s!"neither cardinality ({cardinalityError}), bundle ({bundleError}), mixed ({mixedError}), nor direct ({directError}) projection JSON"
    match result with
    | .ok true =>
        IO.println "HT source projection accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT source projection rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT source projection rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT source projection read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-projection-cert-check PROJECTION.json"
      return (2 : UInt32)
