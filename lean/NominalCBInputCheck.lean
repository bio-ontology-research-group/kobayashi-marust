import ContextCalculus.UniversalDefinerElimination

open Lean
open ContextCalculus.UniversalDefiner

/-! Executable checker for the nominal CB input certificate
(`KM_NOMINAL_CB_INPUT_CERT`, and under `KM_LEAN_CHECKERS`): the inert-sort
release followed by the universal-definer elimination. Acceptance means, by
`WireNominalCBInput.check_sound`, that the CB engine's input is satisfiable
iff the frontend's clause set is, together with any side theory that reads
only the reserved concepts; by `check_consistent`, `check_unsat` and
`check_entails`, the two have the same consistency verdict, unsatisfiable
reserved classes and subsumptions between reserved classes. -/

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireNominalCBInput ← fromJson? json
      return document.check
    match result with
    | .ok true =>
        IO.println "nominal CB input accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "nominal CB input rejected: a release or elimination condition or the result clause set does not match"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"nominal CB input rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"nominal CB input read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: nominal-cb-input-check CERTIFICATE.json"
      return (2 : UInt32)
