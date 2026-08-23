import ContextCalculus.CBJoin3ClosureWire

open Lean
open ContextCalculus.CBJoin3ClosureWire

#print axioms DecodedContextJoin3Closure.complete_coverage
#print axioms WireJoin3ClosureDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireJoin3ClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true => IO.println "CB Join-3 closure accepted"; return (0 : UInt32)
    | .ok false => IO.eprintln "CB Join-3 closure rejected"; return (1 : UInt32)
    | .error error => IO.eprintln s!"CB Join-3 closure rejected: {error}"; return (1 : UInt32)
  catch error => IO.eprintln s!"CB Join-3 closure read error: {error}"; return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: cb-join3-closure-wire-check CERTIFICATE.json" *> pure (2 : UInt32)
