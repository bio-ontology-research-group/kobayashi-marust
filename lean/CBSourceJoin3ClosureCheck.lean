import ContextCalculus.CBSourceJoin3Closure

open Lean
open ContextCalculus.CBSourceJoin3Closure

#print axioms WireSourceJoin3ClosureDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireSourceJoin3ClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "source-bound CB Join-3-closure certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "source-bound CB Join-3-closure certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"source-bound CB Join-3-closure certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"source-bound CB Join-3-closure certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-source-join3-closure-check CERTIFICATE.json"
      return (2 : UInt32)
