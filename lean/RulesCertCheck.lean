import ContextCalculus.RulesRouteCertificate

open Lean
open ContextCalculus.RulesRoute

/-! Executable checker for rule-route answer certificates (`KM_RULES_LEAN_CERT`).
Acceptance means, by `WireRulesCertificate.check_sound`, that the published
answer in the document is exact for the DL-safe knowledge base decoded from its
clause list, given its premises (entailments the worker took from the CB
taxonomy). The checker prints the number of premises so that a caller can
tell a premise-free certificate from a relative one. -/

def diagnose (c : Certificate) : String :=
  if !encodingOK c.oguard c.nominals c.ontology then "the O-guard encoding conditions fail"
  else
    let badRefs := (c.refutations.filter (fun r => !c.refOK r)).length
    let badModels := c.models.length - c.okModels.length
    s!"{badRefs} of {c.refutations.length} refutation(s) and {badModels} of {c.models.length} model(s) fail, or an answer lacks evidence"

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    match Json.parse input >>= fromJson? (α := WireRulesCertificate) with
    | .error error =>
        IO.eprintln s!"rules certificate rejected: {error}"
        return (1 : UInt32)
    | .ok wire =>
        if wire.check then
          IO.println s!"rules certificate accepted: {wire.refutations.length} refutation(s), {wire.models.length} model(s), {wire.premise_subsumptions.length + wire.premise_unsatisfiable.length} premise(s)"
          return (0 : UInt32)
        else
          IO.eprintln s!"rules certificate rejected: {diagnose wire.toCertificate}"
          return (1 : UInt32)
  catch error =>
    IO.eprintln s!"rules certificate read error: {error}"
    return (2 : UInt32)

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | _ => do
      IO.eprintln "usage: rules-cert-check CERTIFICATE.json"
      return (2 : UInt32)
