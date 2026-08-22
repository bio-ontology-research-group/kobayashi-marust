import ContextCalculus.HypertableauRegularProductionTerminalWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRegularProductionTerminal ← fromJson? json
      document.check
    match result with
    | .ok true =>
        IO.println "HT regular production terminal accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "HT regular production terminal rejected"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT regular production terminal rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT regular production terminal read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: ht-regular-production-terminal-check TERMINAL.json"
      return (2 : UInt32)
