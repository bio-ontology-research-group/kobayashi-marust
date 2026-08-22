import ContextCalculus.HypertableauRootedCardinalityFrontierWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRootedCardinalityAddressFrontier ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "HT rooted cardinality frontier accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT rooted cardinality frontier rejected: address check failed"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT rooted cardinality frontier rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT rooted cardinality frontier read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-rooted-cardinality-frontier-check FRONTIER.json"
      return (2 : UInt32)
