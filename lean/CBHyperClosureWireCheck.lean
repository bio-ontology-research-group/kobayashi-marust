import ContextCalculus.CBHyperClosureWire

open Lean
open ContextCalculus.CBHyperClosureWire

#print axioms DecodedContextHyperClosure.complete_coverage
#print axioms WireHyperClosureDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireHyperClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true => IO.println "CB Hyper closure accepted"; return (0 : UInt32)
    | .ok false => IO.eprintln "CB Hyper closure rejected"; return (1 : UInt32)
    | .error error => IO.eprintln s!"CB Hyper closure rejected: {error}"; return (1 : UInt32)
  catch error => IO.eprintln s!"CB Hyper closure read error: {error}"; return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: cb-hyper-closure-wire-check CERTIFICATE.json" *> pure (2 : UInt32)
