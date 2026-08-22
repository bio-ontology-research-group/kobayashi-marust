import ContextCalculus.HypertableauRootedCardinalityProductionRunWire

open Lean
open ContextCalculus.Hypertableau

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireRootedCardinalityProductionRun ← fromJson? json
      return document.check
    match result with
    | .ok true => IO.println "HT rooted cardinality production run accepted"; return (0 : UInt32)
    | .ok false =>
        let json ← match Json.parse input with
          | .ok json => pure json
          | .error error => throw (IO.userError error)
        let decoded : Except String WireRootedCardinalityProductionRun := fromJson? json
        let document ←
          match decoded with
          | .ok document => pure document
          | .error error => throw (IO.userError error)
        IO.eprintln s!"HT rooted cardinality production run rejected: trace={document.trace.check}, terminal={document.terminal.check}, within_budget={decide (document.terminal.nodeCount ≤ 8 * 2 ^ (document.start_budget + document.frontiers.length))}, matches_last={document.matchesLast}, terminal_nodes={document.terminal.nodeCount}, root_count={document.root_count}, terminal_roots={document.terminal.rootCount}, frontiers={document.frontiers.length}"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"HT rooted cardinality production run rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"HT rooted cardinality production run read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => IO.eprintln "usage: ht-rooted-cardinality-production-run-check RUN.json" *>
      pure (2 : UInt32)
