import Lean.Data.Json
import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout

/-!
# Executable OWL reference procedure (`km-owl-reference`)

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7, and `docs/V1.6.3-HT-PLAN.md`.
Command-line wrapper over `OWLFrontend.owlReferenceSHI`,
`OWLFrontend.owlReference` and their routes on an OWL 2 functional-syntax
document:

```
km-owl-reference [--procedure el|sri|el-then-sri|alc|el-then-alc] <file.ofn>
```

1. read the file and run `OWL.parse` (a rejection declines);
2. request `OWLFrontend.probeRequest O`: the class IRIs `O.classNames`
   followed by the probes `urn:km:owl-reference:probe-a` and
   `urn:km:owl-reference:probe-b` (an ontology that mentions a probe
   declines);
3. run the route: `el` is `owlELReference`, `sri` is `owlSRIReference` (the
   SHI route), `el-then-sri` (default) is `owlReferenceSHI`, EL first, then
   SHI; `alc` is `owlALCReference`, `el-then-alc` is `owlReference`, EL
   first, then ALC. The SHI route has no concept budget. It declines when
   the ontology is outside the SRI fragment, or when a property chain is
   neither a plain inclusion nor `ObjectPropertyChain(r r)` below `r`; the
   reason names the first such axiom. `owlReferenceSHI_complete` says this
   never happens on OWL EL or on SHI (which contains OWL ALC). Before the
   ALC type elimination the binary enforces the runtime budget of the
   v1.6.0 stage: it declines with `alc budget: N concept names` when the
   ALC translation's `conceptCount` exceeds `KM_ALC_REFERENCE_MAX_CONCEPTS`
   (default `16`). The budget is a resource bound outside the completeness
   theorem;
4. publish through `publish`, which takes the route's equation
   (`RouteAnswer`), so its type records which theorem covers the output:
   `routeAnswer_exact` gives the conclusion of `owlReference_sound` (and of
   `owlSRIReference_sound`, `owlReferenceSHI_sound`) and
   `owlReadout_exact` says what the printed readout means under the OWL 2
   direct semantics.

Output (`format` `owl-sparse-v1`), streamed:
`{"format":"owl-sparse-v1","procedure":"el","inconsistent":false,"unsat":[IRIs],"rows":[{"sub":IRI,"sups":[IRIs]},...]}`.
`procedure` names the route that answered: `el`, `sri` or `alc`.
`inconsistent` is the probe bit `probe-a ⊑ probe-b`; `unsat` lists the classes
`A` with `A ⊑ probe-b`; one row per satisfiable class lists its class
superclasses (itself included). An inconsistent ontology prints empty `unsat`
and `rows` (every class is unsatisfiable).

Exit codes: `0` publish, `2` usage or unreadable input file
(`failed to read <path>: ...`), `3` decline (reason on stderr), `4` any later
IO error (`io error: ...`). With `KM_REFERENCE_TIMING=1` every phase prints
`KM_REFERENCE_TIMING phase=<name> ms=<ms>` on stderr: `read`, `parse`,
`names`, `translate`, `closure` (EL), `transitivity` and `classify` (SHI) or
`types` (ALC), `rows`, `readout`, `output`, `total`.

Loops over input-sized lists are tail recursive (`foldl`, `filter`,
`filterMap`, `map` and `append` compile to their tail-recursive twins), and
`writeChunked` recurses in tail position.
-/

open Lean
open ContextCalculus
open ContextCalculus.OWLFrontend
open ContextCalculus.SparseTaxonomy

namespace KMOWLReferenceCheck

/-! ### Phase timing (`KM_REFERENCE_TIMING=1`), as in `km-el-reference` -/

/-- Evaluate `f ()` at this point of the `IO` sequence; the subtype keeps the
equation the publication proof needs. -/
@[noinline] def evalNow {α : Type} (f : Unit → α) : BaseIO { a : α // a = f () } :=
  pure ⟨f (), rfl⟩

def timingEnabled : IO Bool := do
  return (← IO.getEnv "KM_REFERENCE_TIMING") == some "1"

def reportPhase (enabled : Bool) (name : String) (t0 : Nat) : IO Unit := do
  if enabled then
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"KM_REFERENCE_TIMING phase={name} ms={(t1 - t0) / 1000000}"

def timedPhase {α : Type} (enabled : Bool) (name : String) (f : Unit → α) :
    IO { a : α // a = f () } := do
  let t0 ← IO.monoNanosNow
  let r ← evalNow f
  reportPhase enabled name t0
  return r

/-! ### Decline reasons -/

def axiomKind : OWL.Axiom → String
  | .subClassOf .. => "SubClassOf"
  | .equivalentClasses _ => "EquivalentClasses"
  | .disjointClasses _ => "DisjointClasses"
  | .domain .. => "ObjectPropertyDomain"
  | .range .. => "ObjectPropertyRange"
  | .subObjectPropertyOf .. => "SubObjectPropertyOf"
  | .equivalentObjectProperties _ => "EquivalentObjectProperties"
  | .inverseObjectProperties .. => "InverseObjectProperties"
  | .transitive _ => "TransitiveObjectProperty"
  | .symmetric _ => "SymmetricObjectProperty"
  | .declareClass _ => "Declaration(Class)"
  | .declareObjectProperty _ => "Declaration(ObjectProperty)"

/-- The kind of the first axiom failing `p`, for a decline reason. -/
def firstFailing (O : OWL.Ontology) (p : OWL.Axiom → Bool) : String :=
  match O.axioms.find? (fun ax => !p ax) with
  | some ax => s!"first: {axiomKind ax}"
  | none => "every axiom passes alone"

/-- An object-property expression in functional syntax. -/
def propText : OWL.ObjProp → String
  | .named r => s!"<{r}>"
  | .inv r => s!"ObjectInverseOf(<{r}>)"

/-- The first axiom outside SHI, written out when it is a property chain. -/
def firstOutsideSHI (O : OWL.Ontology) : String :=
  match O.axioms.find? (fun ax => !ax.isSHI) with
  | some (.subObjectPropertyOf rs r) =>
    s!"SubObjectPropertyOf(ObjectPropertyChain({String.intercalate " " (rs.map propText)}) {propText r})"
  | some ax => axiomKind ax
  | none => "every axiom passes alone"

/-! ### The routes, phase by phase -/

/-- The EL answer with its closure passed in (the body of `owlELReference`),
so the closure and the row readout are timed separately. -/
def elAnswerOfClosure (T : ELTranslation) (c : ELReference.State) : OWLAnswer :=
  let named := List.range T.named.length
  let index := superIndex (Std.TreeSet.ofList named) c.subs
  { named := T.named, rows := named.map (sparseRowOf c T.bottom index) }

theorem owlELReference_of_translate {O : OWL.Ontology} {requested : List OWL.IRI}
    {T : ELTranslation} (hT : translateEL O requested = some T) :
    owlELReference O requested =
      some (elAnswerOfClosure T
        (ELReference.closure T.top T.bottom (List.range T.named.length) T.ontology)) := by
  simp only [owlELReference, hT, Option.map_some]
  rfl

/-- The ALC answer with its types passed in (the body of `owlALCReference`). -/
def alcAnswerOfTypes (T : ALCTranslation) (G : Finset (Finset (Fin T.conceptCount))) :
    OWLAnswer :=
  { named := T.named
    rows := (ofMatrix (List.range T.named.length) (alcIndexBit T G)).rows }

theorem owlALCReference_of_translate {O : OWL.Ontology} {requested : List OWL.IRI}
    {T : ALCTranslation} (hT : translateALC O requested = some T) :
    owlALCReference O requested =
      some (alcAnswerOfTypes T (ALCReference.saturateC T.ontology)) := by
  simp only [owlALCReference, hT, Option.map_some]
  rfl

/-- The SHI answer with the transitivity encoding passed in (the body of
`owlSRIReference`). -/
def sriAnswerOf (T : SRITranslation)
    (E : Σ k, SRI.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)) : OWLAnswer :=
  { named := T.named, rows := sriRows T (SRI.Proc.classifyF E.2 (sriRequest T E.1)) }

theorem owlSRIReference_of_translate {O : OWL.Ontology} {requested : List OWL.IRI}
    {T : SRITranslation} (hT : translateSRI O requested = some T)
    (hS : isSHIB T.ontology = true) :
    owlSRIReference O requested = some (sriAnswerOf T (SRI.Proc.encTrans T.ontology)) := by
  simp only [owlSRIReference, hT, hS, if_true]
  rfl

/-- What a route run gives: an answer with its equation, or a decline. -/
inductive Run (P : OWLAnswer → Prop) (Q : Prop) where
  | published (a : OWLAnswer) (h : P a)
  /-- The route did not apply (`Q` records why, for the EL-then-ALC
  composition). -/
  | notApplicable (h : Q)
  | declined (reason : String)

def runEL (timing : Bool) (O : OWL.Ontology) (requested : List OWL.IRI) :
    IO (Run (fun a => owlELReference O requested = some a)
      (owlELReference O requested = none)) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateEL O requested)
  match tOpt, ht with
  | none, ht =>
    return .notApplicable (by simp [owlELReference, ← ht])
  | some T, ht =>
    let ⟨c, hc⟩ ← timedPhase timing "closure" (fun _ =>
      ELReference.closure T.top T.bottom (List.range T.named.length) T.ontology)
    let ⟨a, ha⟩ ← timedPhase timing "rows" (fun _ => elAnswerOfClosure T c)
    return .published a (by rw [owlELReference_of_translate ht.symm, ha, hc])

def defaultAlcMaxConcepts : Nat := 16

def getAlcMaxConcepts : IO Nat := do
  match (← IO.getEnv "KM_ALC_REFERENCE_MAX_CONCEPTS") with
  | none => pure defaultAlcMaxConcepts
  | some raw => pure (raw.toNat?.getD defaultAlcMaxConcepts)

def runALC (timing : Bool) (maxConcepts : Nat) (O : OWL.Ontology)
    (requested : List OWL.IRI) :
    IO (Run (fun a => owlALCReference O requested = some a) True) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateALC O requested)
  match tOpt, ht with
  | none, _ => return .notApplicable trivial
  | some T, ht =>
    if T.conceptCount > maxConcepts then
      return .declined s!"alc budget: {T.conceptCount} concept names"
    else
      let ⟨G, hG⟩ ← timedPhase timing "types" (fun _ => ALCReference.saturateC T.ontology)
      let ⟨a, ha⟩ ← timedPhase timing "rows" (fun _ => alcAnswerOfTypes T G)
      return .published a (by rw [owlALCReference_of_translate ht.symm, ha, hG])

def runSRI (timing : Bool) (O : OWL.Ontology) (requested : List OWL.IRI) :
    IO (Run (fun a => owlSRIReference O requested = some a) True) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateSRI O requested)
  match tOpt, ht with
  | none, _ => return .notApplicable trivial
  | some T, ht =>
    if hS : isSHIB T.ontology = true then
      let ⟨E, hE⟩ ← timedPhase timing "transitivity" (fun _ => SRI.Proc.encTrans T.ontology)
      let ⟨cls, hcls⟩ ← timedPhase timing "classify" (fun _ =>
        SRI.Proc.classifyF E.2 (sriRequest T E.1))
      let ⟨a, ha⟩ ← timedPhase timing "rows" (fun _ =>
        ({ named := T.named, rows := sriRows T cls } : OWLAnswer))
      return .published a (by
        rw [owlSRIReference_of_translate ht.symm hS, ha, hcls, hE]
        rfl)
    else
      return .declined s!"not SHI: property chain outside SHI: {firstOutsideSHI O}"

/-! ### Output -/

/-- Stream `items` as comma-separated JSON fragments, at most 4096 items per
write, never building the whole output string. Tail recursive. -/
def writeChunked {α : Type} (out : IO.FS.Stream) (render : α → String) :
    Bool → String → Nat → List α → IO Unit
  | _, acc, _, [] => if acc.isEmpty then pure () else out.putStr acc
  | first, acc, k, x :: xs => do
    let acc := acc ++ (if first then "" else ",") ++ render x
    if k + 1 ≥ 4096 then
      out.putStr acc
      writeChunked out render false "" 0 xs
    else
      writeChunked out render false acc (k + 1) xs

def procedureName : OWLProcedure → String
  | .el => "el"
  | .alc => "alc"
  | .elThenAlc => "el-then-alc"
  | .sri => "sri"
  | .elThenSri => "el-then-sri"

/-- Publish the readout of an answer to `probeRequest O`. The proof argument
records in the type that the answer comes from the route's equation; with the
freshness of the probes, `owlReadout_exact` gives the meaning of every printed
field under the OWL 2 direct semantics. `route` names the route that answered
(`el`, `sri` or `alc`). -/
def publish (timing : Bool) (route : String) (p : OWLProcedure) (O : OWL.Ontology)
    (a : OWLAnswer) (_h : RouteAnswer p O (probeRequest O) a)
    (_hA : probeA ∉ O.classNames) (_hB : probeB ∉ O.classNames) : IO UInt32 := do
  let names := O.classNames
  let ⟨r, _⟩ ← timedPhase timing "readout" (fun _ => owlReadout names.length a)
  let t0 ← IO.monoNanosNow
  let encoded : Array String := names.toArray.map fun s => (Json.str s).compress
  let nameOf (i : Nat) : String := encoded[i]?.getD "\"\""
  let renderRow (row : Nat × List Nat) : String :=
    let sups := String.intercalate "," (row.2.map nameOf)
    s!"\{\"sub\":{nameOf row.1},\"sups\":[{sups}]}"
  let out ← IO.getStdout
  let inc := if r.inconsistent then "true" else "false"
  out.putStr s!"\{\"format\":\"owl-sparse-v1\",\"procedure\":{(Json.str route).compress},\"inconsistent\":{inc},\"unsat\":["
  writeChunked out nameOf true "" 0 r.unsat
  out.putStr "],\"rows\":["
  writeChunked out renderRow true "" 0 r.rows
  out.putStr "]}\n"
  out.flush
  reportPhase timing "output" t0
  return 0

/-! ### Driver -/

def decline (reason : String) : IO UInt32 := do
  IO.eprintln reason
  return 3

def runOntology (timing : Bool) (p : OWLProcedure) (O : OWL.Ontology) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let names := O.classNames
  if hA : probeA ∈ names then
    return ← decline s!"probe IRI mentioned: {probeA}"
  else if hB : probeB ∈ names then
    return ← decline s!"probe IRI mentioned: {probeB}"
  else
    let requested := probeRequest O
    reportPhase timing "names" t0
    match p with
    | .el =>
      match ← runEL timing O requested with
      | .published a h => publish timing "el" .el O a h hA hB
      | .notApplicable _ =>
        decline s!"not recognised: not OWL EL ({firstFailing O OWL.Axiom.isEL})"
      | .declined reason => decline reason
    | .alc =>
      let maxConcepts ← getAlcMaxConcepts
      match ← runALC timing maxConcepts O requested with
      | .published a h => publish timing "alc" .alc O a h hA hB
      | .notApplicable _ =>
        decline s!"not recognised: not OWL ALC ({firstFailing O OWL.Axiom.isALC})"
      | .declined reason => decline reason
    | .sri =>
      match ← runSRI timing O requested with
      | .published a h => publish timing "sri" .sri O a h hA hB
      | .notApplicable _ =>
        decline s!"not recognised: not OWL SRI ({firstFailing O OWL.Axiom.isSRI})"
      | .declined reason => decline reason
    | .elThenSri =>
      match ← runEL timing O requested with
      | .published a h =>
        publish timing "el" .elThenSri O a
          (show owlReferenceSHI O requested = some a by simp [owlReferenceSHI, h]) hA hB
      | .declined reason => decline reason
      | .notApplicable hnone =>
        match ← runSRI timing O requested with
        | .published a h =>
          publish timing "sri" .elThenSri O a
            (show owlReferenceSHI O requested = some a by simp [owlReferenceSHI, hnone, h]) hA hB
        | .notApplicable _ =>
          decline s!"not recognised: neither OWL EL ({firstFailing O OWL.Axiom.isEL}) nor OWL SRI ({firstFailing O OWL.Axiom.isSRI})"
        | .declined reason => decline reason
    | .elThenAlc =>
      match ← runEL timing O requested with
      | .published a h =>
        publish timing "el" .elThenAlc O a
          (show owlReference O requested = some a by simp [owlReference, h]) hA hB
      | .declined reason => decline reason
      | .notApplicable hnone =>
        let maxConcepts ← getAlcMaxConcepts
        match ← runALC timing maxConcepts O requested with
        | .published a h =>
          publish timing "alc" .elThenAlc O a
            (show owlReference O requested = some a by simp [owlReference, hnone, h]) hA hB
        | .notApplicable _ =>
          decline s!"not recognised: neither OWL EL ({firstFailing O OWL.Axiom.isEL}) nor OWL ALC ({firstFailing O OWL.Axiom.isALC})"
        | .declined reason => decline reason

def runText (timing : Bool) (p : OWLProcedure) (text : String) : IO UInt32 := do
  let ⟨parsed, _⟩ ← timedPhase timing "parse" (fun _ => OWL.parse text)
  match parsed with
  | .error reason => decline s!"parse rejected: {reason}"
  | .ok O => runOntology timing p O

def parseProcedure : String → Option OWLProcedure
  | "el" => some .el
  | "alc" => some .alc
  | "el-then-alc" => some .elThenAlc
  | "sri" => some .sri
  | "el-then-sri" => some .elThenSri
  | _ => none

def parseArgs (p : OWLProcedure) (path : Option String) :
    List String → Option (OWLProcedure × String)
  | [] => path.map fun f => (p, f)
  | "--procedure" :: raw :: rest =>
    match parseProcedure raw with
    | some p' => parseArgs p' path rest
    | none => none
  | arg :: rest =>
    if arg.startsWith "--procedure=" then
      match parseProcedure (arg.drop "--procedure=".length).toString with
      | some p' => parseArgs p' path rest
      | none => none
    else if arg.startsWith "-" then none
    else match path with
      | none => parseArgs p (some arg) rest
      | some _ => none

/-- Read the file, then run. Only a failed read reports `failed to read`
(exit 2); an IO error afterwards reports `io error` (exit 4). -/
def runFile (p : OWLProcedure) (path : String) : IO UInt32 := do
  let timing ← timingEnabled
  let t0 ← IO.monoNanosNow
  match ← (IO.FS.readFile path).toBaseIO with
  | .error err =>
    IO.eprintln s!"failed to read {path}: {err}"
    return 2
  | .ok text =>
    reportPhase timing "read" t0
    let code ← match ← (runText timing p text).toBaseIO with
      | .ok code => pure code
      | .error err =>
        IO.eprintln s!"io error: {err}"
        pure 4
    reportPhase timing "total" t0
    return code

end KMOWLReferenceCheck

def main (args : List String) : IO UInt32 := do
  match KMOWLReferenceCheck.parseArgs .elThenSri none args with
  | none =>
    IO.eprintln "usage: km-owl-reference [--procedure el|sri|el-then-sri|alc|el-then-alc] <file.ofn> (default el-then-sri)"
    return 2
  | some (p, path) => KMOWLReferenceCheck.runFile p path
