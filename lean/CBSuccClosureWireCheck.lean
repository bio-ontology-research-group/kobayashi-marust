import ContextCalculus.CBSuccClosureWire

open Lean
open ContextCalculus.CBSuccClosureWire

#print axioms DecodedContextSuccClosure.complete_delivery
#print axioms WireSuccClosureDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireSuccClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true => IO.println "CB Succ closure accepted"; return (0 : UInt32)
    | .ok false => IO.eprintln "CB Succ closure rejected"; return (1 : UInt32)
    | .error error => IO.eprintln s!"CB Succ closure rejected: {error}"; return (1 : UInt32)
  catch error => IO.eprintln s!"CB Succ closure read error: {error}"; return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: cb-succ-closure-wire-check CERTIFICATE.json" *> pure (2 : UInt32)
