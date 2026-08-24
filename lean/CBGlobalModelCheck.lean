import ContextCalculus.CBGlobalModelWire

open Lean
open ContextCalculus.CBGlobalModelWire

#print axioms DecodedCBGlobalModelDocument.source_model
#print axioms DecodedCBGlobalModelDocument.source_model_nonempty
#print axioms DecodedCBGlobalModelDocument.production_model
#print axioms WireCBGlobalModelDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCBGlobalModelDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "CB global model certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "CB global model certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"CB global model certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"CB global model certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-global-model-check CERTIFICATE.json"
      return (2 : UInt32)
