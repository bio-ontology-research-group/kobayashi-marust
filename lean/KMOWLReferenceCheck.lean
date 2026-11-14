import Lean.Data.Json
import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout
import ContextCalculus.OWLFrontend.ReadoutAt
import ContextCalculus.OWLFrontend.SRIQDReference
import ContextCalculus.OWLFrontend.SRIQDKBRows
import ContextCalculus.OWLFrontend.SHOIQDC2aReference

/-!
# Executable OWL reference procedure (`km-owl-reference`)

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7, and `docs/V1.6.3-HT-PLAN.md`.
Command-line wrapper over `OWLFrontend.owlReferenceSHI`,
`OWLFrontend.owlReference` and their routes on an OWL 2 functional-syntax
document:

```
km-owl-reference [--procedure el|sri|el-then-sri|sriq|el-then-sriq|alc|el-then-alc] <file.ofn>
km-owl-reference --procedure sriq-kb [--hint FILE] [--type CLASS INDIVIDUAL] <file.ofn>
km-owl-reference --procedure sriqd <file.ofn>
km-owl-reference --procedure sriqd-kb [--hint FILE] [--type CLASS INDIVIDUAL] <file.ofn>
km-owl-reference --procedure shoiq-c2a [--hint FILE] [--type CLASS INDIVIDUAL] <file.ofn>
```

`shoiq-c2a` is `owlSHOIQDC2aConsistent`, the v1.7.0 stage C2a route for
SHOIQ(D) knowledge bases with nominals and datatypes
(`docs/V1.7.0-C2-NOMINALS-DESIGN.md`). It prints the `owl-consistency-v1`
line, exact at the OWL 2 datatype map for every hint
(`owlSHOIQDC2aConsistent_sound`); with `--type CLASS INDIVIDUAL` it decides
the class assertion (`owlSHOIQDTypeRow`, `owlSHOIQDTypeRow_sound`) and
prints the `owl-type-v1` line. It declines outside the SHOIQ(D)
knowledge-base part, on a non-simple role, outside C2a, and on data ranges
outside the supported sub-theory. The hint is a core in the text format of
`SHOIQC2aReference.lean`, over the names of the reduced ontology.

`sriqd` is `owlSHIQDReference`, the v1.7.0 stage C4 route for SHIQ with
data properties and datatypes. Its answers are exact under the OWL 2 direct
semantics at the OWL 2 datatype map (`owlSHIQDReference_sound`, with
`xsd:pattern` read by any matcher), so `owlReadout_exactAt` (not
`owlReadout_exact`) says what its readout means; `publishAt` takes its
equation. It declines outside the SHIQ(D) part, on a non-simple role, and
when a data atom is outside the supported sub-theory of the datatype map
(`allSupported`).

`sriqd-kb` is `owlSHIQDKBConsistent`, the route for SHIQ(D) knowledge bases
with individuals and data property assertions. It prints
`{"format":"owl-consistency-v1","consistent":true|false}`, exact at the OWL 2
datatype map for every hint (`owlSHIQDKBConsistent_sound`). With
`--type CLASS INDIVIDUAL` it decides the class assertion (`owlTypeRowD`,
`owlTypeRowD_sound`) and prints the `owl-type-v1` line of `sriq-kb`. The
hint of `--hint FILE` is handed to every part of the data theory; it never
changes an answer.

`sriq-kb` is `owlSHIQKBReference`, the v1.7.0 route for SHIQ knowledge
bases with individuals (`docs/V1.7.0-C1B-ABOX-DESIGN.md`). It decides
consistency with the hint of `--hint FILE` first (text format in the
docstring of `SRIQKBReference.lean`) and the exhaustive search as fallback;
the stderr line `hint: accepted`, `hint: rejected, searching` or
`hint: does not fit the translation, searching` says what happened. Its
theorems hold for every hint (`owlSHIQKBReference_sound`). With
`--type CLASS INDIVIDUAL` it decides the class assertion instead
(`owlTypeRow`, `owlTypeRow_sound`; the hint is then a countermodel of the
knowledge base with the complement of the class at the individual) and
prints `{"format":"owl-type-v1","class":C,"individual":a,"entailed":true|false}`.
`--hint` and `--type` are usage errors with any procedure but `sriq-kb` and
`sriqd-kb`.

1. read the file and run `OWL.parse` (a rejection declines);
2. request `OWLFrontend.probeRequest O`: the class IRIs `O.classNames`
   followed by the probes `urn:km:owl-reference:probe-a` and
   `urn:km:owl-reference:probe-b` (an ontology that mentions a probe
   declines);
3. run the route: `el` is `owlELReference`, `sri` is `owlSRIReference` (the
   SHI route), `el-then-sri` (default) is `owlReferenceSHI`, EL first, then
   SHI; `sriq` is `owlSHIQReference` (the v1.7.0 SHIQ route),
   `el-then-sriq` is `owlReferenceSHIQ`, EL, then SHI, then SHIQ; `alc` is
   `owlALCReference`, `el-then-alc` is `owlReference`, EL first, then ALC. The SHI route has no concept budget. It declines when
   the ontology is outside the SRI fragment, or when a property chain is
   neither a plain inclusion nor `ObjectPropertyChain(r r)` below `r`; the
   reason names the first such axiom. `owlReferenceSHI_complete` says this
   never happens on OWL EL or on SHI (which contains OWL ALC). Before the
   ALC type elimination the binary enforces the runtime budget of the
   v1.6.0 stage: it declines with `alc budget: N concept names` when the
   ALC translation's `conceptCount` exceeds `KM_ALC_REFERENCE_MAX_CONCEPTS`
   (default `16`). The budget is a resource bound outside the completeness
   theorem. The SHIQ route declines outside the SHIQ part, and when a role
   of a number restriction or of a functionality axiom has a transitive role
   below it or below its inverse (the OWL 2 DL simple-role restriction); the
   reason names the two roles. `owlSHIQReference_isSome_iff` says it
   publishes exactly on the other ontologies. It has no budget: its star
   elimination is exponential in the number of concept and role indices;
4. publish through `publish`, which takes the route's equation
   (`RouteAnswer`), so its type records which theorem covers the output:
   `routeAnswer_exact` gives the conclusion of `owlReference_sound` (and of
   `owlSRIReference_sound`, `owlReferenceSHI_sound`) and
   `owlReadout_exact` says what the printed readout means under the OWL 2
   direct semantics.

Output (`format` `owl-sparse-v1`), streamed:
`{"format":"owl-sparse-v1","procedure":"el","inconsistent":false,"unsat":[IRIs],"rows":[{"sub":IRI,"sups":[IRIs]},...]}`.
`procedure` names the route that answered: `el`, `sri`, `sriq` or `alc`.
`inconsistent` is the probe bit `probe-a ⊑ probe-b`; `unsat` lists the classes
`A` with `A ⊑ probe-b`; one row per satisfiable class lists its class
superclasses (itself included). An inconsistent ontology prints empty `unsat`
and `rows` (every class is unsatisfiable).

Exit codes: `0` publish, `2` usage or unreadable input file
(`failed to read <path>: ...`), `3` decline (reason on stderr), `4` any later
IO error (`io error: ...`). With `KM_REFERENCE_TIMING=1` every phase prints
`KM_REFERENCE_TIMING phase=<name> ms=<ms>` on stderr: `read`, `parse`,
`names`, `translate`, `closure` (EL), `transitivity` and `classify` (SHI and
SHIQ) or `types` (ALC), `hint` and `search` (`sriq-kb`), `type` (`--type`),
`rows`, `readout`, `output`, `total`.

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
  | .disjointUnion .. => "DisjointUnion"
  | .disjointObjectProperties _ => "DisjointObjectProperties"
  | .functional _ => "FunctionalObjectProperty"
  | .inverseFunctional _ => "InverseFunctionalObjectProperty"
  | .reflexive _ => "ReflexiveObjectProperty"
  | .irreflexive _ => "IrreflexiveObjectProperty"
  | .asymmetric _ => "AsymmetricObjectProperty"
  | .subDataPropertyOf .. => "SubDataPropertyOf"
  | .equivalentDataProperties _ => "EquivalentDataProperties"
  | .disjointDataProperties _ => "DisjointDataProperties"
  | .dataDomain .. => "DataPropertyDomain"
  | .dataRange .. => "DataPropertyRange"
  | .functionalData _ => "FunctionalDataProperty"
  | .datatypeDefinition .. => "DatatypeDefinition"
  | .hasKey .. => "HasKey"
  | .sameIndividual _ => "SameIndividual"
  | .differentIndividuals _ => "DifferentIndividuals"
  | .classAssertion .. => "ClassAssertion"
  | .objectPropertyAssertion .. => "ObjectPropertyAssertion"
  | .negativeObjectPropertyAssertion .. => "NegativeObjectPropertyAssertion"
  | .dataPropertyAssertion .. => "DataPropertyAssertion"
  | .negativeDataPropertyAssertion .. => "NegativeDataPropertyAssertion"
  | .declareDataProperty _ => "Declaration(DataProperty)"
  | .declareNamedIndividual _ => "Declaration(NamedIndividual)"
  | .declareDatatype _ => "Declaration(Datatype)"
  | .declareAnnotationProperty _ => "Declaration(AnnotationProperty)"

/-- The kind of the first axiom failing `p`, for a decline reason. -/
def firstFailing (O : OWL.Ontology) (p : OWL.Axiom → Bool) : String :=
  match O.axioms.find? (fun ax => !p ax) with
  | some ax => s!"first: {axiomKind ax}"
  | none => "every axiom passes alone"

/-- An object-property expression in functional syntax. -/
def propText : OWL.ObjProp → String
  | .named r => s!"<{r}>"
  | .inv r => s!"ObjectInverseOf(<{r}>)"
  | .top => "owl:topObjectProperty"
  | .bot => "owl:bottomObjectProperty"

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

/-- The SHIQ answer with the transitivity encoding passed in (the body of
`owlSHIQReference`). -/
def sriqAnswerOf (T : SRIQTranslation)
    (E : Σ k, SRIQ.Ontology (Fin (T.conceptCount + k)) (Fin T.roleCount)) : OWLAnswer :=
  { named := T.named, rows := sriqRows T (QProc.classifyQO E.2 (sriqRequest T E.1)) }

theorem owlSHIQReference_of_translate {O : OWL.Ontology} {requested : List OWL.IRI}
    {T : SRIQTranslation} (hT : translateSRIQ O requested = some T)
    (hS : isSHIQB T.ontology = true) :
    owlSHIQReference O requested = some (sriqAnswerOf T (SRIQ.Proc.encTransQ T.ontology)) := by
  simp only [owlSHIQReference, hT, hS, if_true]
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

/-- The SHI route for `el-then-sriq`: a decline of the chain check is a
proof that the route gives `none`, so the SHIQ route runs next. -/
def runSRIOrNone (timing : Bool) (O : OWL.Ontology) (requested : List OWL.IRI) :
    IO (Run (fun a => owlSRIReference O requested = some a)
      (owlSRIReference O requested = none)) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateSRI O requested)
  match tOpt, ht with
  | none, ht => return .notApplicable (by simp [owlSRIReference, ← ht])
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
      return .notApplicable (by simp [owlSRIReference, ← ht, hS])

/-- The IRI of role index `k` of the SHIQ translation, for a decline
reason. -/
def sriqRoleText (O : OWL.Ontology) (requested : List OWL.IRI) {m : Nat} :
    SRI.RoleT (Fin m) → String
  | .pos k => s!"<{(((SRIQT.run O requested).1.b.rdefs[k.val]?).bind List.head?).getD "?"}>"
  | .inv k =>
    s!"ObjectInverseOf(<{(((SRIQT.run O requested).1.b.rdefs[k.val]?).bind List.head?).getD "?"}>)"

/-- The first pair `(T, R)` that fails the simple-role check: `T` transitive
and below `R` or below the inverse of `R`, `R` a role of a counting clause. -/
def nonSimpleWitness {n m : Nat} (O : SRIQ.Ontology (Fin n) (Fin m)) :
    Option (SRI.RoleT (Fin m) × SRI.RoleT (Fin m)) :=
  (transRoles O).findSome? fun T =>
    let up := SRI.Proc.roleUp (SRIQ.sriPart O) T
    ((countRoles O).find? fun R => up.contains R || up.contains R.flip).map fun R => (T, R)

def runSRIQ (timing : Bool) (O : OWL.Ontology) (requested : List OWL.IRI) :
    IO (Run (fun a => owlSHIQReference O requested = some a) True) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateSRIQ O requested)
  match tOpt, ht with
  | none, _ => return .notApplicable trivial
  | some T, ht =>
    if hS : isSHIQB T.ontology = true then
      let ⟨E, hE⟩ ← timedPhase timing "transitivity" (fun _ => SRIQ.Proc.encTransQ T.ontology)
      let ⟨cls, hcls⟩ ← timedPhase timing "classify" (fun _ =>
        QProc.classifyQO E.2 (sriqRequest T E.1))
      let ⟨a, ha⟩ ← timedPhase timing "rows" (fun _ =>
        ({ named := T.named, rows := sriqRows T cls } : OWLAnswer))
      return .published a (by
        rw [owlSHIQReference_of_translate ht.symm hS, ha, hcls, hE]
        rfl)
    else
      match nonSimpleWitness T.ontology with
      | some (tr, R) =>
        return .declined
          s!"not SHIQ: non-simple role in a number restriction or functionality axiom: {sriqRoleText O requested R} has the transitive role {sriqRoleText O requested tr} below it or below its inverse"
      | none =>
        return .declined s!"not SHIQ: property chain outside SHIQ: {firstOutsideSHI O}"

/-- The SHIQ knowledge-base answer with its consistency verdict passed in
(the body of `owlSHIQKBReference`). -/
theorem owlSHIQKBReference_of_translate {O : OWL.Ontology} {requested : List OWL.IRI}
    {hint : Option RawHint} {T : SRIQKBTranslation} (hT : translateSRIQKB O requested = some T)
    (hS : kbOK T = true) :
    owlSHIQKBReference O requested hint =
      some (kbAnswerOf T (SRIQ.Proc.encTransQ T.ontology)
        (SRIQ.Proc.consistentKBQ T.ontology T.abox (hint.bind fun h => h.toHint _ _ _))) := by
  simp only [owlSHIQKBReference, hT, hS, if_true, kbHint]

/-- The verdict of `owlTypeRow` once the translation is known. -/
theorem owlTypeRow_of_translate {O : OWL.Ontology} {C a : OWL.IRI} {hint : Option RawHint}
    {T : SRIQKBTranslation} (hT : translateSRIQKB O [C] [a] = some T) (hS : kbOK T = true)
    (hC : 0 < T.named.length) (ha : T.inds.idxOf a < T.inds.length) :
    owlTypeRow O C a hint =
      some (!SRIQ.Proc.consistentKBQ
        (SRIQ.Proc.complO T.ontology ⟨0, Nat.lt_of_lt_of_le hC T.hnamed⟩)
        (SRIQ.Proc.complA T.abox ⟨_, ha⟩) (hint.bind fun h => h.toHint _ _ _)) := by
  simp only [owlTypeRow, hT, hS, hC, ha, dif_pos, if_true, SRIQ.Proc.typeRow]

/-- `consistentKBQ` with the hint check and the search timed apart; the
stderr line reports what the hint did. -/
def consistentTimed (timing : Bool) {n m k : Nat} (O : SRIQ.Ontology (Fin n) (Fin m))
    (A : SRIQ.ABox (Fin n) (Fin m) (Fin k)) (hint : Option RawHint) :
    IO { b : Bool // b = SRIQ.Proc.consistentKBQ O A (hint.bind fun h => h.toHint _ _ _) } := do
  let ⟨ok, hok⟩ ← timedPhase timing "hint" (fun _ =>
    (hint.bind fun h => h.toHint (n + (SRIQ.Proc.encTransQ O).1) m k).any
      (SRIQ.Proc.checkRealisation (SRIQ.Proc.encTransQ O).2 (SRIQ.Proc.encABox O A)))
  if hint.isSome then
    if (hint.bind fun h => h.toHint (n + (SRIQ.Proc.encTransQ O).1) m k).isNone then
      IO.eprintln "hint: does not fit the translation, searching"
    else if ok then
      IO.eprintln "hint: accepted"
    else
      IO.eprintln "hint: rejected, searching"
  if hok' : ok = true then
    return ⟨true, by
      simp only [SRIQ.Proc.consistentKBQ, SRIQ.Proc.consistentKB, ← hok, hok', Bool.true_or]⟩
  else
    let ⟨s, hs⟩ ← timedPhase timing "search" (fun _ =>
      SRIQ.Proc.searchKB (SRIQ.Proc.encTransQ O).2 (SRIQ.Proc.encABox O A))
    return ⟨s, by
      simp only [SRIQ.Proc.consistentKBQ, SRIQ.Proc.consistentKB, ← hok,
        Bool.eq_false_iff.2 hok', Bool.false_or, hs]⟩

/-- The first assertion with an anonymous individual, for the decline
reason of `sriq-kb`. -/
def firstAnonymous (O : OWL.Ontology) : Option String :=
  let anon : OWL.Individual → Bool := fun | .anon _ => true | .named _ => false
  (O.axioms.find? fun ax => match ax with
    | .classAssertion _ a => anon a
    | .objectPropertyAssertion _ a b | .negativeObjectPropertyAssertion _ a b => anon a || anon b
    | .sameIndividual as | .differentIndividuals as => as.any anon
    | .dataPropertyAssertion _ a _ | .negativeDataPropertyAssertion _ a _ => anon a
    | _ => false).map axiomKind

/-- The decline reason when the knowledge-base translation does not apply. -/
def kbNotRecognised (O : OWL.Ontology) : String :=
  match firstAnonymous O with
  | some k => s!"not recognised: anonymous individuals are declined for now (first in: {k})"
  | none =>
    s!"not recognised: not an OWL SHIQ knowledge base ({firstFailing O OWL.Axiom.isSHIQKB})"

/-- The first negative role assertion whose role has a transitive role
below it or below its inverse. -/
def nonSimpleNeg {n m k : Nat} (O : SRIQ.Ontology (Fin n) (Fin m))
    (A : SRIQ.ABox (Fin n) (Fin m) (Fin k)) : Option (SRI.RoleT (Fin m) × SRI.RoleT (Fin m)) :=
  (transRoles O).findSome? fun T =>
    let up := SRI.Proc.roleUp (SRIQ.sriPart O) T
    ((nroleRoles A).find? fun R => up.contains R || up.contains R.flip).map fun R => (T, R)

/-- The IRI of role index `k` of the knowledge-base translation. -/
def kbRoleText (O : OWL.Ontology) (requested : List OWL.IRI) {m : Nat} :
    SRI.RoleT (Fin m) → String
  | .pos k =>
    s!"<{(((SRIQT.run (SRIQKB.kbTBox O (SRIQKB.defBase O requested)) requested).1.b.rdefs[k.val]?).bind List.head?).getD "?"}>"
  | .inv k =>
    s!"ObjectInverseOf(<{(((SRIQT.run (SRIQKB.kbTBox O (SRIQKB.defBase O requested)) requested).1.b.rdefs[k.val]?).bind List.head?).getD "?"}>)"

/-- The decline reason of a translation that fails `kbOK`. -/
def kbDecline (O : OWL.Ontology) (requested : List OWL.IRI) (T : SRIQKBTranslation) : String :=
  match nonSimpleWitness T.ontology with
  | some (tr, R) =>
    s!"not SHIQ: non-simple role in a number restriction or functionality axiom: {kbRoleText O requested R} has the transitive role {kbRoleText O requested tr} below it or below its inverse"
  | none =>
    match nonSimpleNeg T.ontology T.abox with
    | some (tr, R) =>
      s!"not SHIQ: non-simple role in a negative property assertion: {kbRoleText O requested R} has the transitive role {kbRoleText O requested tr} below it or below its inverse"
    | none => s!"not SHIQ: property chain outside SHIQ: {firstOutsideSHI O}"

def runSRIQKB (timing : Bool) (O : OWL.Ontology) (requested : List OWL.IRI)
    (hint : Option RawHint) :
    IO (Run (fun a => owlSHIQKBReference O requested hint = some a) True) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateSRIQKB O requested)
  match tOpt, ht with
  | none, _ => return .notApplicable trivial
  | some T, ht =>
    if hS : kbOK T = true then
      let ⟨c, hc⟩ ← consistentTimed timing T.ontology T.abox hint
      let ⟨a, ha⟩ ← timedPhase timing "rows" (fun _ =>
        kbAnswerOf T (SRIQ.Proc.encTransQ T.ontology) c)
      return .published a (by rw [owlSHIQKBReference_of_translate ht.symm hS, ha, hc])
    else
      return .declined (kbDecline O requested T)

/-- Decide one class assertion with `owlTypeRow`, timed. -/
def runType (timing : Bool) (O : OWL.Ontology) (C a : OWL.IRI) (hint : Option RawHint) :
    IO (Except String { v : Bool // owlTypeRow O C a hint = some v }) := do
  let ⟨tOpt, ht⟩ ← timedPhase timing "translate" (fun _ => translateSRIQKB O [C] [a])
  match tOpt, ht with
  | none, _ =>
    return .error (kbNotRecognised O)
  | some T, ht =>
    if hS : kbOK T = true then
      if hC : 0 < T.named.length then
        if ha : T.inds.idxOf a < T.inds.length then
          let ⟨c, hc⟩ ← consistentTimed timing
            (SRIQ.Proc.complO T.ontology ⟨0, Nat.lt_of_lt_of_le hC T.hnamed⟩)
            (SRIQ.Proc.complA T.abox ⟨_, ha⟩) hint
          return .ok ⟨!c, by rw [owlTypeRow_of_translate ht.symm hS hC ha, hc]⟩
        else return .error "internal: individual without an index"
      else return .error "internal: class without an index"
    else return .error (kbDecline O [C] T)

/-- Print the verdict of `owlTypeRow`. The proof argument records that the
verdict is the one of `owlTypeRow`, so `owlTypeRow_sound` gives its
meaning. -/
def publishType (C a : OWL.IRI) (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlTypeRow O C a hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  let verdict := if v then "true" else "false"
  out.putStrLn ("{\"format\":\"owl-type-v1\",\"class\":" ++ (Json.str C).compress ++
    ",\"individual\":" ++ (Json.str a).compress ++ ",\"entailed\":" ++ verdict ++ "}")
  out.flush
  return 0

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
  | .sriq => "sriq"
  | .elThenSriq => "el-then-sriq"
  | .sriqKB => "sriq-kb"

/-- Publish the readout of an answer to `probeRequest O`. The proof argument
records in the type that the answer comes from the route's equation; with the
freshness of the probes, `owlReadout_exact` gives the meaning of every printed
field under the OWL 2 direct semantics. `route` names the route that answered
(`el`, `sri`, `sriq` or `alc`). -/
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

/-- Publish the readout of an answer of the SHIQ(D) route to
`probeRequest O`; `owlReadout_exactAt` gives its meaning at the OWL 2
datatype map. -/
def publishAt (timing : Bool) (O : OWL.Ontology) (a : OWLAnswer)
    (_h : owlSHIQDReference O (probeRequest O) = some a)
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
  out.putStr s!"\{\"format\":\"owl-sparse-v1\",\"procedure\":\"sriqd\",\"inconsistent\":{inc},\"unsat\":["
  writeChunked out nameOf true "" 0 r.unsat
  out.putStr "],\"rows\":["
  writeChunked out renderRow true "" 0 r.rows
  out.putStr "]}\n"
  out.flush
  reportPhase timing "output" t0
  return 0

/-- Why the SHIQ(D) route declines. -/
def sriqdDecline (O : OWL.Ontology) (requested : List OWL.IRI) : String :=
  if !O.isSHIQD then s!"not recognised: not OWL SHIQ(D) ({firstFailing O OWL.Axiom.isSHIQD})"
  else match translateSRIQD O requested with
    | none => "not recognised: the SHIQ(D) translation failed"
    | some T =>
      if !isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) then
        "not SHIQ: non-simple role in a number restriction or functionality axiom"
      else if !allSupported T then
        "datatypes: a data range outside the supported sub-theory of the OWL 2 datatype map"
      else "not recognised"

/-- Why the SHIQ(D) knowledge-base route declines. -/
def sriqdKBDecline (O : OWL.Ontology) : String :=
  if !O.isSHIQDKB then
    s!"not recognised: not an OWL SHIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSHIQDKB})"
  else match translateSRIQDKB O [] [] with
    | none => "not recognised: the SHIQ(D) knowledge-base translation failed"
    | some T =>
      if !isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) then
        "not SHIQ: non-simple role in a number restriction or functionality axiom"
      else if !negSimpleB (ContextCalculus.SRIQD.objPart T.ontology)
          (ContextCalculus.SRIQD.objABox T.abox) then
        "not SHIQ: non-simple role in a negative property assertion"
      else "datatypes: a data range outside the supported sub-theory of the OWL 2 datatype map"

/-- Print the consistency verdict of `owlSHIQDKBConsistent`; the proof
argument records where it came from (`owlSHIQDKBConsistent_sound`). -/
def publishConsistent (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlSHIQDKBConsistent O hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-consistency-v1\",\"consistent\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- Print the verdict of `owlTypeRowD` (`owlTypeRowD_sound`). -/
def publishTypeD (C a : OWL.IRI) (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlTypeRowD O C a hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-type-v1\",\"class\":" ++ (Json.str C).compress ++
    ",\"individual\":" ++ (Json.str a).compress ++ ",\"entailed\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- Why the SHOIQ(D) C2a route declines. -/
def shoiqDecline (O : OWL.Ontology) : String :=
  if !O.isSHOIQDKB then
    s!"not recognised: not an OWL SHOIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSHOIQDKB})"
  else match translateSHOIQD O [] with
    | none => "not recognised: the SHOIQ(D) translation failed"
    | some T =>
      if !isSHIQB (ContextCalculus.SRIQD.objPart T.ontology) then
        "not SHIQ: non-simple role in a number restriction or functionality axiom"
      else if !decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (dosn T (OWLFrontend.SHOIQ.nomNames O []))))
      then "not C2a: an existential or at-least restriction on a subject that is neither a " ++
        "nominal nor nominal-only has a role below the inverse of the role of an at-most restriction"
      else "datatypes: a data range outside the supported sub-theory of the OWL 2 datatype map"

/-- Print the consistency verdict of `owlSHOIQDC2aConsistent`
(`owlSHOIQDC2aConsistent_sound`). -/
def publishConsistentN (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlSHOIQDC2aConsistent O hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-consistency-v1\",\"consistent\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- Print the verdict of `owlSHOIQDTypeRow` (`owlSHOIQDTypeRow_sound`). -/
def publishTypeN (C a : OWL.IRI) (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlSHOIQDTypeRow O C a hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-type-v1\",\"class\":" ++ (Json.str C).compress ++
    ",\"individual\":" ++ (Json.str a).compress ++ ",\"entailed\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- The SHOIQ(D) C2a route on an ontology. -/
def runOntologyN (timing : Bool) (hint : Option RawHint) (query : Option (OWL.IRI × OWL.IRI))
    (O : OWL.Ontology) : IO UInt32 := do
  match query with
  | some (C, a) =>
    let ⟨res, hres⟩ ← timedPhase timing "type" (fun _ => owlSHOIQDTypeRow O C a hint)
    match res, hres with
    | some v, h => publishTypeN C a v h.symm
    | none, _ =>
      IO.eprintln (shoiqDecline (addAxs O (typeAxs C a)))
      return 3
  | none =>
    let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlSHOIQDC2aConsistent O hint)
    match res, hres with
    | some v, h => publishConsistentN v h.symm
    | none, _ =>
      IO.eprintln (shoiqDecline O)
      return 3

/-- The SHIQ(D) knowledge-base route on an ontology. -/
def runOntologyDKB (timing : Bool) (hint : Option RawHint) (query : Option (OWL.IRI × OWL.IRI))
    (O : OWL.Ontology) : IO UInt32 := do
  match query with
  | some (C, a) =>
    let ⟨res, hres⟩ ← timedPhase timing "type" (fun _ => owlTypeRowD O C a hint)
    match res, hres with
    | some v, h => publishTypeD C a v h.symm
    | none, _ =>
      IO.eprintln (sriqdKBDecline (addAxs O (typeAxs C a)))
      return 3
  | none =>
    let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlSHIQDKBConsistent O hint)
    match res, hres with
    | some v, h => publishConsistent v h.symm
    | none, _ =>
      IO.eprintln (sriqdKBDecline O)
      return 3

/-- The SHIQ(D) route on an ontology. -/
def runOntologyD (timing : Bool) (route : String) (hint : Option RawHint)
    (query : Option (OWL.IRI × OWL.IRI)) (O : OWL.Ontology) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  if route == "sriqd-kb" then
    return ← runOntologyDKB timing hint query O
  if route == "shoiq-c2a" then
    return ← runOntologyN timing hint query O
  let names := O.classNames
  if hA : probeA ∈ names then
    IO.eprintln s!"probe IRI mentioned: {probeA}"
    return 3
  else if hB : probeB ∈ names then
    IO.eprintln s!"probe IRI mentioned: {probeB}"
    return 3
  else
    reportPhase timing "names" t0
    let ⟨res, hres⟩ ← timedPhase timing "classify" (fun _ => owlSHIQDReference O (probeRequest O))
    match res, hres with
    | some a, h => publishAt timing O a h.symm hA hB
    | none, _ =>
      IO.eprintln (sriqdDecline O (probeRequest O))
      return 3

/-! ### Driver -/

def decline (reason : String) : IO UInt32 := do
  IO.eprintln reason
  return 3

def runOntology (timing : Bool) (p : OWLProcedure) (hint : Option RawHint)
    (query : Option (OWL.IRI × OWL.IRI)) (O : OWL.Ontology) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  if let some (C, a) := query then
    match ← runType timing O C a hint with
    | .ok ⟨v, hv⟩ => return ← publishType C a v hv
    | .error reason => return ← decline reason
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
    | .sriq =>
      match ← runSRIQ timing O requested with
      | .published a h => publish timing "sriq" .sriq O a h hA hB
      | .notApplicable _ =>
        decline s!"not recognised: not OWL SHIQ ({firstFailing O OWL.Axiom.isSHIQ})"
      | .declined reason => decline reason
    | .elThenSriq =>
      match ← runEL timing O requested with
      | .published a h =>
        publish timing "el" .elThenSriq O a
          (show owlReferenceSHIQ O requested = some a by
            simp [owlReferenceSHIQ, owlReferenceSHI, h]) hA hB
      | .declined reason => decline reason
      | .notApplicable hEL =>
        match ← runSRIOrNone timing O requested with
        | .published a h =>
          publish timing "sri" .elThenSriq O a
            (show owlReferenceSHIQ O requested = some a by
              simp [owlReferenceSHIQ, owlReferenceSHI, hEL, h]) hA hB
        | .declined reason => decline reason
        | .notApplicable hSRI =>
          match ← runSRIQ timing O requested with
          | .published a h =>
            publish timing "sriq" .elThenSriq O a
              (show owlReferenceSHIQ O requested = some a by
                simp [owlReferenceSHIQ, owlReferenceSHI, hEL, hSRI, h]) hA hB
          | .notApplicable _ =>
            decline s!"not recognised: neither OWL EL ({firstFailing O OWL.Axiom.isEL}) nor OWL SHIQ ({firstFailing O OWL.Axiom.isSHIQ})"
          | .declined reason => decline reason
    | .sriqKB =>
      match ← runSRIQKB timing O requested hint with
      | .published a h => publish timing "sriq-kb" .sriqKB O a ⟨hint, h⟩ hA hB
      | .notApplicable _ => decline (kbNotRecognised O)
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

def runText (timing : Bool) (p : OWLProcedure) (hint : Option RawHint)
    (query : Option (OWL.IRI × OWL.IRI)) (text : String) : IO UInt32 := do
  let ⟨parsed, _⟩ ← timedPhase timing "parse" (fun _ => OWL.parse text)
  match parsed with
  | .error reason => decline s!"parse rejected: {reason}"
  | .ok O => runOntology timing p hint query O

def parseProcedure : String → Option OWLProcedure
  | "el" => some .el
  | "alc" => some .alc
  | "el-then-alc" => some .elThenAlc
  | "sri" => some .sri
  | "el-then-sri" => some .elThenSri
  | "sriq" => some .sriq
  | "el-then-sriq" => some .elThenSriq
  | "sriq-kb" => some .sriqKB
  | _ => none

/-- The command line: procedure, input file, hint file, type query. -/
structure Args where
  procedure : OWLProcedure := .elThenSri
  path : Option String := none
  hint : Option String := none
  query : Option (OWL.IRI × OWL.IRI) := none
  /-- `sriqd` or `sriqd-kb` (the data routes, outside `OWLProcedure`). -/
  dataRoute : Option String := none

def parseArgs (acc : Args) : List String → Option Args
  | [] => if acc.path.isSome then some acc else none
  | "--procedure" :: "sriqd" :: rest => parseArgs { acc with dataRoute := some "sriqd" } rest
  | "--procedure" :: "sriqd-kb" :: rest => parseArgs { acc with dataRoute := some "sriqd-kb" } rest
  | "--procedure" :: "shoiq-c2a" :: rest =>
    parseArgs { acc with dataRoute := some "shoiq-c2a" } rest
  | "--procedure" :: raw :: rest =>
    match parseProcedure raw with
    | some p' => parseArgs { acc with procedure := p' } rest
    | none => none
  | "--hint" :: f :: rest => parseArgs { acc with hint := some f } rest
  | "--type" :: C :: a :: rest => parseArgs { acc with query := some (C, a) } rest
  | arg :: rest =>
    if arg.startsWith "--procedure=" then
      match parseProcedure (arg.drop "--procedure=".length).toString with
      | some p' => parseArgs { acc with procedure := p' } rest
      | none => none
    else if arg.startsWith "--hint=" then
      parseArgs { acc with hint := some (arg.drop "--hint=".length).toString } rest
    else if arg.startsWith "-" then none
    else match acc.path with
      | none => parseArgs { acc with path := some arg } rest
      | some _ => none

/-- Read the hint file, if any. -/
def readHint (path : Option String) : IO (Except String (Option RawHint)) := do
  match path with
  | none => return .ok none
  | some f =>
    match ← (IO.FS.readFile f).toBaseIO with
    | .error err => return .error s!"failed to read hint {f}: {err}"
    | .ok text =>
      match RawHint.parseHint text with
      | .ok h => return .ok (some h)
      | .error reason => return .error s!"bad hint {f}: {reason}"

/-- Read the hint file and the input file, then run. Only a failed read
reports `failed to read` (exit 2, also for a malformed hint file); an IO
error afterwards reports `io error` (exit 4). -/
def runFile (args : Args) (path : String) : IO UInt32 := do
  let timing ← timingEnabled
  let t0 ← IO.monoNanosNow
  match ← readHint args.hint with
  | .error msg =>
    IO.eprintln msg
    return 2
  | .ok hint =>
  match ← (IO.FS.readFile path).toBaseIO with
  | .error err =>
    IO.eprintln s!"failed to read {path}: {err}"
    return 2
  | .ok text =>
    reportPhase timing "read" t0
    let run : IO UInt32 := match args.dataRoute with
      | some route => do
        let ⟨parsed, _⟩ ← timedPhase timing "parse" (fun _ => OWL.parse text)
        match parsed with
        | .error reason => decline s!"parse rejected: {reason}"
        | .ok O => runOntologyD timing route hint args.query O
      | none => runText timing args.procedure hint args.query text
    let code ← match ← run.toBaseIO with
      | .ok code => pure code
      | .error err =>
        IO.eprintln s!"io error: {err}"
        pure 4
    reportPhase timing "total" t0
    return code

end KMOWLReferenceCheck

def main (args : List String) : IO UInt32 := do
  let usage := "usage: km-owl-reference [--procedure el|sri|el-then-sri|sriq|el-then-sriq|alc|el-then-alc|sriq-kb|sriqd|sriqd-kb|shoiq-c2a] [--hint FILE] [--type CLASS INDIVIDUAL] <file.ofn> (default el-then-sri; --hint and --type with sriq-kb, sriqd-kb and shoiq-c2a only)"
  match KMOWLReferenceCheck.parseArgs {} args with
  | some a =>
    match a.path with
    | some path =>
      if (a.hint.isSome || a.query.isSome) &&
          !((a.procedure == .sriqKB && a.dataRoute.isNone) || a.dataRoute == some "sriqd-kb" ||
            a.dataRoute == some "shoiq-c2a") then
        IO.eprintln usage
        return 2
      else KMOWLReferenceCheck.runFile a path
    | none =>
      IO.eprintln usage
      return 2
  | none =>
    IO.eprintln usage
    return 2
