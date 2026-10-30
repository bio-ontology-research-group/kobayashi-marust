import ContextCalculus.RulesInertSortRelease

open Lean
open ContextCalculus.RulesInertSort

/-! Executable checker for the inert-sort release certificate of the
rule-consistency worker (`KM_RULES_INERT_CERT`). Acceptance means, by
`WireInertSortRelease.check_sound`, that the worker input in the certificate
is satisfiable iff the sorted clause set is, together with any side theory
that reads only the reserved concepts. -/

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireInertSortRelease ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "rules inert-sort release accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "rules inert-sort release rejected: a guard condition or the released clause set does not match"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"rules inert-sort release rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"rules inert-sort release read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: rules-inert-sort-release-check CERTIFICATE.json"
      return (2 : UInt32)
