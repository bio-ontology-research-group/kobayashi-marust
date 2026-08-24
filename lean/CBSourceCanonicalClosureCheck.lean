import ContextCalculus.CBSourceCanonicalClosure

open Lean
open ContextCalculus.CBSourceCanonicalClosure

#print axioms WireSourceCanonicalClosureDocument.check_sound

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireSourceCanonicalClosureDocument ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "source-bound CB canonical-closure certificate accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "source-bound CB canonical-closure certificate rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"source-bound CB canonical-closure certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"source-bound CB canonical-closure certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: cb-source-canonical-closure-check CERTIFICATE.json"
      return (2 : UInt32)
