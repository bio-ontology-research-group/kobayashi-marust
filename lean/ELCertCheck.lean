import ContextCalculus.ELCompletionExecutablePublication

open Lean
open ContextCalculus.ELCompletion

/-- Names of the failing components of a certificate that decodes, for the
rejection message only. -/
def failedComponents (document : WireCertificate) : List String :=
  match document.decode with
  | .error _ => []
  | .ok doc =>
      let parts : List (String × Bool) :=
        [("canonical-origins", doc.checkCanonicalOrigins),
          ("origin-ontology", doc.checkOriginOntologyFast),
          ("source-partition", doc.checkSourcePartitionFast),
          ("normalization", doc.checkPartitionedNormalizationFast),
          ("residual-compilations",
            doc.residual_compilations.all (fun residual => residual.check)),
          ("finite-residuals", doc.checkFiniteResidualsFast),
          ("signature-closed", doc.checkSignatureClosedFast),
          ("trace", checkTraceFast doc.top doc.bottom doc.ontology doc.trace),
          ("closure", checkClosedTraceFast doc.top doc.bottom doc.ontology doc.trace),
          ("fact-agreement", doc.checkFactAgreementFast),
          ("active-concepts", doc.checkActiveConceptsFast),
          ("public-output", doc.checkPublicOutputFast),
          ("named-output", doc.checkNamedOutputFast)]
      parts.filterMap fun part => if part.2 then none else some part.1

def checkFile (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireCertificate ← fromJson? json
      document.checkFast
    match result with
    | .ok true =>
        IO.println "ELC certificate accepted: exact taxonomy and inconsistency result"
        return (0 : UInt32)
    | .ok false =>
        let failed : List String :=
          match (do
              let json ← Json.parse input
              let document : WireCertificate ← fromJson? json
              pure document : Except String WireCertificate) with
          | .ok document => failedComponents document
          | .error _ => []
        IO.eprintln s!"ELC certificate rejected: trace is unsound or materialization is not closed (failed: {", ".intercalate failed})"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"ELC certificate rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"ELC certificate read error: {error}"
    return (2 : UInt32)

def checkResidualFile (symbolCount : Nat) (path : System.FilePath) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result : Except String Bool := do
      let json ← Json.parse input
      let document : WireResidualCompilation ← fromJson? json
      document.check symbolCount
    match result with
    | .ok true =>
        IO.println "ELC residual compilation accepted"
        return (0 : UInt32)
    | .ok false =>
        IO.eprintln "ELC residual compilation rejected: evidence mismatch"
        return (1 : UInt32)
    | .error error =>
        IO.eprintln s!"ELC residual compilation rejected: {error}"
        return (1 : UInt32)
  catch error =>
    IO.eprintln s!"ELC residual compilation read error: {error}"
    return (2 : UInt32)

def timePhase {α : Type} (label : String) (action : Unit → α) : IO α := do
  let start ← IO.monoMsNow
  let value ← IO.lazyPure action
  let stop ← IO.monoMsNow
  IO.eprintln s!"{label}: {stop - start} ms"
  return value

/-- Time each component of `checkFast` (diagnostics only). -/
def profileDocument (document : WireCertificate) : IO UInt32 := do
  match document.decode with
  | Except.error error => do
      IO.eprintln error
      return 1
  | Except.ok doc =>
      let parts : List (String × (Unit → Bool)) :=
        [("canonical-origins", fun _ => doc.checkCanonicalOrigins),
          ("origin-ontology", fun _ => doc.checkOriginOntologyFast),
          ("source-partition", fun _ => doc.checkSourcePartitionFast),
          ("normalization", fun _ => doc.checkPartitionedNormalizationFast),
          ("residual-compilations", fun _ =>
            doc.residual_compilations.all (fun residual => residual.check)),
          ("finite-residuals", fun _ => doc.checkFiniteResidualsFast),
          ("signature-closed", fun _ => doc.checkSignatureClosedFast),
          ("trace", fun _ => checkTraceFast doc.top doc.bottom doc.ontology doc.trace),
          ("closure", fun _ => checkClosedTraceFast doc.top doc.bottom doc.ontology doc.trace),
          ("fact-agreement", fun _ => doc.checkFactAgreementFast),
          ("active-concepts", fun _ => doc.checkActiveConceptsFast),
          ("public-output", fun _ => doc.checkPublicOutputFast),
          ("named-output", fun _ => doc.checkNamedOutputFast)]
      let mut ok := true
      for (label, part) in parts do
        let value ← timePhase label part
        ok := ok && value
      IO.eprintln s!"verdict: {ok}"
      return (if ok then 0 else 1)

def profileFile (path : System.FilePath) : IO UInt32 := do
  let input ← IO.FS.readFile path
  let parsed ← timePhase "parse+fromJson" fun _ =>
    (do
      let json ← Json.parse input
      let document : WireCertificate ← fromJson? json
      pure document : Except String WireCertificate)
  match parsed with
  | .ok document =>
      let decoded ← timePhase "decode" fun _ => document.decode.isOk
      if decoded then profileDocument document else return 1
  | .error error => do
      IO.eprintln error
      return 1

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => checkFile path
  | ["--profile", path] => profileFile path
  | ["--residual", symbolCount, path] =>
      match symbolCount.toNat? with
      | some count => checkResidualFile count path
      | none => do
          IO.eprintln s!"invalid symbol count: {symbolCount}"
          return (2 : UInt32)
  | _ => do
      IO.eprintln "usage: elc-cert-check CERTIFICATE.json | --residual SYMBOL_COUNT PAYLOAD.json"
      return (2 : UInt32)
