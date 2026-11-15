import Lean.Data.Json
import ContextCalculus.OWL.Parse
import ContextCalculus.OWLFrontend.ReferenceReadout
import ContextCalculus.OWLFrontend.ReadoutAt
import ContextCalculus.OWLFrontend.SRIQDReference
import ContextCalculus.OWLFrontend.SRIQDKBRows
import ContextCalculus.OWLFrontend.SHOIQDC2aReference
import ContextCalculus.OWLFrontend.SROIQAnon
import ContextCalculus.OWLFrontend.ZeroRoute
import ContextCalculus.OWLFrontend.HasSelfClass

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
km-owl-reference --procedure sroiq-c2a [--hint FILE] [--type CLASS INDIVIDUAL] [--check] <file.ofn>
km-owl-reference --procedure sriq-kb|sriqd-kb|shoiq-c2a|sroiq-c2a --print-index <file.ofn>
```

`--print-index` prints the index tables a hint refers to (`printIndex`).
`--check` (with `shoiq-c2a` or `sroiq-c2a`) runs the fragment checks only
and prints `accepted` or the decline reason.

`sroiq-c2a` is `owlSROIQDC2aConsistent`, the v1.7.0 stage C3 route: the
SHOIQ(D) route with general regular role chains and reflexive properties
(`docs/V1.7.0-C3-ROLES-DESIGN.md`), exact for every hint
(`owlSROIQDC2aConsistent_sound`; type row `owlSROIQDTypeRow_sound`). It
also declines irregular role hierarchies, role automata that do not close,
and number restrictions over a role with a chain or reflexive role below it.

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

/-- Why the SROIQ(D) C2a route declines. -/
def sroiqDecline (O : OWL.Ontology) : String :=
  if !O.isSROIQDKB then
    s!"not recognised: not an OWL SROIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSROIQDKB})"
  else match translateSHOIQD (roleOff O) [] with
    | none => "not recognised: the SHOIQ(D) translation failed"
    | some T =>
      match roleCls T O with
      | none => "not recognised: a property of a role chain has no role index"
      | some E =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
        if !SROIQ.Proc.regularB (objC T L E) then
          "not regular: the role hierarchy violates the OWL 2 regularity condition"
        else if !SROIQ.Proc.condB (objC T L E) then
          "not simple or not closed: a number restriction over a role with a chain or " ++
          "reflexive role below it, or a role automaton that does not close"
        else if !decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encC T L E))) then
          "not C2a: an existential or at-least restriction on a subject that is neither a " ++
          "nominal nor nominal-only has a role below the inverse of the role of an at-most restriction"
        else "datatypes: a data range outside the supported sub-theory of the OWL 2 datatype map"

/-- Why the Self checks fail on a translation. -/
def selfReason (T : SRIQDKBTranslation) (L : List OWL.IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)))
    (SC : List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : String :=
          if !SROIQ.Proc.regularB (objC T L E) then
            "not regular: the role hierarchy violates the OWL 2 regularity condition"
          else if !SROIQ.Proc.condB (objC T L E) then
            "not simple or not closed: a number restriction over a role with a chain " ++
            "below it, or a role automaton that does not close"
          else if !SROIQ.Proc.selfSimpleB (objC T L E) SC then
            "not simple: an irreflexive property with a chain below it"
          else if !SROIQ.Proc.lamOKB (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC)
              (lamC T L E SC) (irrC T L E SC) then
            "loop roles: the closure of the loop roles failed"
          else if !decide (SRIQN.IsC2aD (encS T L E SC)) ||
              !decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encS T L E SC))) then
            "not C2a: an existential or at-least restriction on a subject that is neither a " ++
            "nominal nor nominal-only has a role below the inverse of the role of an at-most " ++
            "restriction (after the Self encoding)"
          else "datatypes: a data range outside the supported sub-theory of the OWL 2 datatype map"

/-- Why the route with irreflexive and reflexive properties declines (its
input already renamed by `anonOff`). -/
def selfDecline (O : OWL.Ontology) : String :=
  if !O.isSROIQDSKB then
    s!"not recognised: not an OWL SROIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSROIQDSKB})"
  else match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => "not recognised: the SHOIQ(D) translation failed"
    | some T =>
      match roleCls T (selfOff O) with
      | none => "not recognised: a property of a role chain has no role index"
      | some E =>
        match selfCls T O with
        | none => "not recognised: a property of a self axiom has no role index"
        | some SC =>
          let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) []
          selfReason T L E SC

/-- Why the route with `ObjectHasSelf` in class expressions declines (its
input already renamed by `anonOff`). -/
def hsDecline (O0 : OWL.Ontology) : String :=
  let O := hsOff O0
  let P := selfPairs O0
  if !O.isSROIQDSKB then
    s!"not recognised: not an OWL SROIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSROIQDSKB})"
  else match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => "not recognised: the SHOIQ(D) translation failed"
    | some T =>
      match roleCls T (selfOff O) with
      | none => "not recognised: a property of a role chain has no role index"
      | some E =>
        match selfCls T O, pairCls T P with
        | some SC, some PC =>
          selfReason T (OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) (pairNames P)) E (SC ++ PC)
        | _, _ => "not recognised: a property of a self axiom or of ObjectHasSelf has no role index"

/-- The decline of `sroiq-c2a`: the Self route's reason when the input uses
irreflexive properties, the chain route's reason otherwise. -/
def sroiqDeclineS (O : OWL.Ontology) : String :=
  if !(selfPairs O).isEmpty then hsDecline O
  else if O.isSROIQDKB then sroiqDecline O else selfDecline O

/-- Print the consistency verdict of `owlSROIQDC2aConsistent`
(`owlSROIQDAConsistent_sound`). -/
def publishConsistentS (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlC3HConsistent O hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-consistency-v1\",\"consistent\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- Print the verdict of `owlSROIQDTypeRow` (`owlSROIQDATypeRow_sound`). -/
def publishTypeS (C a : OWL.IRI) (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlC3HTypeRow O C a hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-type-v1\",\"class\":" ++ (Json.str C).compress ++
    ",\"individual\":" ++ (Json.str a).compress ++ ",\"entailed\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- The SROIQ(D) C2a route on an ontology. -/
def runOntologyS (timing : Bool) (hint : Option RawHint) (query : Option (OWL.IRI × OWL.IRI))
    (O : OWL.Ontology) : IO UInt32 := do
  match query with
  | some (C, a) =>
    let ⟨res, hres⟩ ← timedPhase timing "type" (fun _ => owlC3HTypeRow O C a hint)
    match res, hres with
    | some v, h => publishTypeS C a v h.symm
    | none, _ =>
      IO.eprintln (sroiqDeclineS (addAxs (anonOff [a] (duOff O)) (typeAxs C a)))
      return 3
  | none =>
    let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlC3HConsistent O hint)
    match res, hres with
    | some v, h => publishConsistentS v h.symm
    | none, _ =>
      IO.eprintln (sroiqDeclineS (anonOff [] (duOff O)))
      return 3

/-- The fragment checks of `sroiq-c2a`, without the decision (phases timed
with `KM_REFERENCE_TIMING=1`). -/
def checkS (timing : Bool) (O : OWL.Ontology) : IO Bool := do
  if !O.isSROIQDKB then return false
  let ⟨tr, _⟩ ← timedPhase timing "translate" (fun _ => translateSHOIQD (roleOff O) [])
  match tr with
  | none => return false
  | some T =>
    let ⟨rc, _⟩ ← timedPhase timing "roles" (fun _ => roleCls T O)
    match rc with
    | none => return false
    | some E =>
      let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
      let ⟨r1, _⟩ ← timedPhase timing "regular" (fun _ => SROIQ.Proc.regularB (objC T L E))
      if !r1 then return false
      let ⟨r2, _⟩ ← timedPhase timing "automata" (fun _ => SROIQ.Proc.condB (objC T L E))
      if !r2 then return false
      let ⟨r3, _⟩ ← timedPhase timing "c2a"
        (fun _ => decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN (encC T L E))))
      if !r3 then return false
      let ⟨r4, _⟩ ← timedPhase timing "data"
        (fun _ => (List.finRange T.tab.length).all fun p => OWL.Datatypes.drSupported (OWLFrontend.SHIQD.spec T.tab p))
      return r4

/-- The fragment checks of the Self route (`owlSelfCore`), without the
decision. -/
def checkSelf (timing : Bool) (O : OWL.Ontology) : IO Bool := do
  if !O.isSROIQDSKB || (selfAxs O).isEmpty then return false
  let ⟨tr, _⟩ ← timedPhase timing "translate" (fun _ => translateSHOIQD (roleOff (selfOff O)) [])
  match tr with
  | none => return false
  | some T =>
    let ⟨rc, _⟩ ← timedPhase timing "roles" (fun _ => roleCls T (selfOff O))
    match rc with
    | none => return false
    | some E =>
      match selfCls T O with
      | none => return false
      | some SC =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) []
        let ⟨r1, _⟩ ← timedPhase timing "regular" (fun _ => SROIQ.Proc.regularB (objC T L E))
        if !r1 then return false
        let ⟨r2, _⟩ ← timedPhase timing "automata" (fun _ => SROIQ.Proc.condB (objC T L E))
        if !r2 then return false
        let ⟨r3, _⟩ ← timedPhase timing "self-simple" (fun _ => SROIQ.Proc.selfSimpleB (objC T L E) SC)
        if !r3 then return false
        let ⟨r4, _⟩ ← timedPhase timing "loop-roles" (fun _ => SROIQ.Proc.lamOKB
          (SRIQD.objPart (SRIQN.dbase (chC T L E))) (scC T L E SC) (lamC T L E SC) (irrC T L E SC))
        if !r4 then return false
        let ⟨D, _⟩ ← timedPhase timing "encode" (fun _ => encS T L E SC)
        let ⟨r5, _⟩ ← timedPhase timing "c2a" (fun _ => decide (SRIQN.IsC2aD D))
        if !r5 then return false
        let ⟨r6, _⟩ ← timedPhase timing "c2a-trans"
          (fun _ => decide (SRIQN.IsC2aD (SRIQN.Proc.encTransDN D)))
        if !r6 then return false
        let ⟨r7, _⟩ ← timedPhase timing "data"
          (fun _ => (List.finRange T.tab.length).all fun p => OWL.Datatypes.drSupported (OWLFrontend.SHIQD.spec T.tab p))
        return r7

/-- Diagnostic for a C2a decline of the chain route (`KM_C2A_WHY=1` with
`--check`): every pair of a lower clause on a non-exempt subject and an
at-most clause whose inverted role lies above the lower role. Not part of
any proved statement. -/
def whyC2a (O : OWL.Ontology) : List String :=
  match translateSHOIQD (roleOff O) [] with
  | none => []
  | some T =>
    match roleCls T O with
    | none => []
    | some E =>
      let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
      let D := SRIQN.objN (SRIQN.Proc.encTransDN (encC T L E))
      let B := SRIQN.basePart D
      let N := SRIQN.noms D
      let cn : Nat → String := fun i =>
        match T.obj.cnames.find? (fun p => p.2 == i) with
        | some p => p.1
        | none => s!"#{i}"
      let rn : SRI.RoleT (Fin T.obj.roleCount) → String := fun R =>
        let (sgn, k) := match R with | .pos r => ("", r.val) | .inv r => ("inv ", r.val)
        match T.obj.rnames.find? (fun p => p.2 == k) with
        | some p => sgn ++ p.1
        | none => sgn ++ s!"r{k}"
      let ups := SRIQ.upperL B
      let C := SRIQ.sriPart B
      (SRIQ.lowerL B).filterMap fun q =>
        if q.1 ∈ N || decide (SRIQN.NomOnly D q.1) then none else
        let up := SRI.Proc.roleUp C q.2.2.1
        match (ups.find? (fun q' => q'.2.1 != 0 && q'.2.2.1.flip ∈ up)).orElse
            (fun _ => ups.find? (fun q' => q'.2.2.1.flip ∈ up)) with
        | none => none
        | some q' => some s!"lower {cn q.1.val} >= {q.2.1} {rn q.2.2.1} {cn q.2.2.2.val} | upper {cn q'.1.val} <= {q'.2.1} {rn q'.2.2.1} {cn q'.2.2.2.val}"

/-- The fragment checks of the route with at-most-zero clauses rewritten
(`owlZeroCore`). -/
def checkZero (timing : Bool) (O : OWL.Ontology) : IO Bool := do
  if !O.isSROIQDKB then return false
  match translateSHOIQD (roleOff O) [] with
  | none => return false
  | some T =>
    match roleCls T O with
    | none => return false
    | some E =>
      let ⟨r, _⟩ ← timedPhase timing "zero-checks"
        (fun _ => sroiqZOK T (OWLFrontend.SHOIQ.nomNames (roleOff O) []) E)
      return r

/-- The fragment checks of the route with `ObjectHasSelf` in class
expressions (`owlHSCore`), without the decision. -/
def checkHS (timing : Bool) (O0 : OWL.Ontology) : IO Bool := do
  let P := selfPairs O0
  if P.isEmpty then return false
  let ⟨O, _⟩ ← timedPhase timing "hasself" (fun _ => hsOff O0)
  if !O.isSROIQDSKB then return false
  let ⟨tr, _⟩ ← timedPhase timing "translate"
    (fun _ => translateSHOIQD (roleOff (selfOff O)) (pairNames P))
  match tr with
  | none => return false
  | some T =>
    match roleCls T (selfOff O), selfCls T O, pairCls T P with
    | some E, some SC, some PC =>
      let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) (pairNames P)
      let ⟨r, _⟩ ← timedPhase timing "self-checks" (fun _ => sroiqSOK T L E (SC ++ PC))
      return r
    | _, _, _ => return false

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
  if route == "sroiq-c2a" then
    return ← runOntologyS timing hint query O
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
  /-- Print the index tables of the translation instead of deciding. -/
  printIndex : Bool := false
  /-- Run the fragment checks of `shoiq-c2a` only (no decision). -/
  checkOnly : Bool := false

def parseArgs (acc : Args) : List String → Option Args
  | [] => if acc.path.isSome then some acc else none
  | "--procedure" :: "sriqd" :: rest => parseArgs { acc with dataRoute := some "sriqd" } rest
  | "--procedure" :: "sriqd-kb" :: rest => parseArgs { acc with dataRoute := some "sriqd-kb" } rest
  | "--procedure" :: "shoiq-c2a" :: rest =>
    parseArgs { acc with dataRoute := some "shoiq-c2a" } rest
  | "--procedure" :: "sroiq-c2a" :: rest =>
    parseArgs { acc with dataRoute := some "sroiq-c2a" } rest
  | "--procedure" :: raw :: rest =>
    match parseProcedure raw with
    | some p' => parseArgs { acc with procedure := p' } rest
    | none => none
  | "--hint" :: f :: rest => parseArgs { acc with hint := some f } rest
  | "--print-index" :: rest => parseArgs { acc with printIndex := true } rest
  | "--check" :: rest => parseArgs { acc with checkOnly := true } rest
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

/-- The index lines of a knowledge-base translation: concept and role
indices of the IRIs, sorted by index. -/
def indexLines (T : SRIQKBTranslation) : List String :=
  let cs := (T.cnames.toArray.qsort (fun a b => a.2 < b.2)).toList
  let rs := (T.rnames.toArray.qsort (fun a b => a.2 < b.2)).toList
  (cs.map fun p => s!"concept {p.2} {p.1}") ++ (rs.map fun p => s!"role {p.2} {p.1}")

/-- **Index printer** (`--print-index`): the concept, role and individual
indices a hint for the route refers to. Lines: `concepts N` (the number of
concept indices of the ontology the hint is checked against, encoding
names included), `roles M`, `concept I IRI`, `role I IRI`, and
`nominal I IRI` (shoiq-c2a: the index of the nominal class of a named
individual) or `individual I IRI` (sriq-kb, sriqd-kb). Indices from the
end of the `concept` lines up to `N - 1` are names of the normalisation
and of the transitivity encoding. -/
def printIndex (route : String) (O : OWL.Ontology) : IO UInt32 := do
  let out ← IO.getStdout
  let emit (ls : List String) : IO Unit := do for l in ls do out.putStrLn l
  let O := if route == "sroiq-c2a" then duOff O else O
  if route == "sroiq-c2a" && !(selfPairs (anonOff [] O)).isEmpty &&
      !(anonOff [] O).isSROIQDSKB then
    let O0 := anonOff [] O
    let P := selfPairs O0
    let O := hsOff O0
    match translateSHOIQD (roleOff (selfOff O)) (pairNames P) with
    | none => decline (hsDecline O0)
    | some T =>
      match roleCls T (selfOff O), selfCls T O, pairCls T P with
      | some E, some SC, some PC =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) (pairNames P)
        let SC := SC ++ PC
        let n1 := T.obj.conceptCount + SROIQ.Proc.kCD (dosnC T L E)
        let nc := (SRIQD.objPart (SRIQN.dbase (chC T L E))).length
        let m := T.obj.roleCount
        emit [s!"concepts {SRIQN.SelfE.ncOf (SRIQN.Proc.encTransDN (encS T L E SC))}", s!"roles {m}"]
        emit (indexLines T.obj)
        emit ((roleOff (selfOff O)).individualNames.filterMap fun a =>
          (nameIx T.obj (OWLFrontend.SHOIQ.nmOf (roleOff (selfOff O)) (pairNames P) a)).map fun i =>
            s!"nominal {i.val} {a}")
        -- the class of `ObjectHasSelf(r)`: `hasself I IRI` or `hasself I inv IRI`
        emit (P.filterMap fun p =>
          (nameIx T.obj p.1).map fun i =>
            match p.2 with
            | .inv r => s!"hasself {i.val} inv {r}"
            | r => s!"hasself {i.val} {r.name}")
        emit [s!"loops {n1}", s!"splits {n1 + 2 * m}", s!"guards {n1 + 2 * m + 3 * nc}",
          s!"fresh-nominal {n1 + 2 * m + 3 * nc + n1 + 1}"]
        out.flush
        return 0
      | _, _, _ => decline (hsDecline O0)
  else if route == "sroiq-c2a" && !(← checkS false (anonOff [] O)) && (anonOff [] O).isSROIQDSKB &&
      !(selfAxs (anonOff [] O)).isEmpty then
    let O := anonOff [] O
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => decline (selfDecline O)
    | some T =>
      match roleCls T (selfOff O), selfCls T O with
      | some E, some SC =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) []
        let n1 := T.obj.conceptCount + SROIQ.Proc.kCD (dosnC T L E)
        let nc := (SRIQD.objPart (SRIQN.dbase (chC T L E))).length
        let m := T.obj.roleCount
        emit [s!"concepts {SRIQN.SelfE.ncOf (SRIQN.Proc.encTransDN (encS T L E SC))}", s!"roles {m}"]
        emit (indexLines T.obj)
        emit ((roleOff (selfOff O)).individualNames.filterMap fun a =>
          (nameIx T.obj (OWLFrontend.SHOIQ.nmOf (roleOff (selfOff O)) [] a)).map fun i =>
            s!"nominal {i.val} {a}")
        -- the Self encoding: loop names from n1 (role j: n1 + j, its inverse n1 + m + j),
        -- split names, nominal guards, the fresh nominal
        emit [s!"loops {n1}", s!"splits {n1 + 2 * m}", s!"guards {n1 + 2 * m + 3 * nc}",
          s!"fresh-nominal {n1 + 2 * m + 3 * nc + n1 + 1}"]
        out.flush
        return 0
      | _, _ => decline (selfDecline O)
  else if route == "sroiq-c2a" && !(← checkS false (anonOff [] O)) && (← checkZero false (anonOff [] O)) then
    let O := anonOff [] O
    match translateSHOIQD (roleOff O) [] with
    | none => decline (sroiqDecline O)
    | some T =>
      match roleCls T O with
      | none => decline (sroiqDecline O)
      | some E =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
        let n1 := T.obj.conceptCount + SROIQ.Proc.kCD (dosnC T L E)
        emit [s!"concepts {SRIQN.SelfE.ncOf (SRIQN.Proc.encTransDN (encZ T L E))}",
          s!"roles {T.obj.roleCount}"]
        emit (indexLines T.obj)
        emit ((roleOff O).individualNames.filterMap fun a =>
          (nameIx T.obj (OWLFrontend.SHOIQ.nmOf (roleOff O) [] a)).map fun i => s!"nominal {i.val} {a}")
        -- the at-most-zero rewriting: one name per object clause from n1
        emit [s!"zeros {n1}"]
        out.flush
        return 0
  else if route == "sroiq-c2a" then
    let O := anonOff [] O
    match translateSHOIQD (roleOff O) [] with
    | none => decline (sroiqDecline O)
    | some T =>
      match roleCls T O with
      | none => decline (sroiqDecline O)
      | some E =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
        emit [s!"concepts {T.obj.conceptCount + SROIQ.Proc.kCD (dosnC T L E) + SRIQN.Proc.encKD (encC T L E)}",
          s!"roles {T.obj.roleCount}"]
        emit (indexLines T.obj)
        emit ((roleOff O).individualNames.filterMap fun a =>
          (nameIx T.obj (OWLFrontend.SHOIQ.nmOf (roleOff O) [] a)).map fun i => s!"nominal {i.val} {a}")
        out.flush
        return 0
  else if route == "shoiq-c2a" then
    match translateSHOIQD O [] with
    | none => decline (shoiqDecline O)
    | some T =>
      let L := OWLFrontend.SHOIQ.nomNames O []
      emit [s!"concepts {T.obj.conceptCount + SRIQN.Proc.encKD (dosn T L)}",
        s!"roles {T.obj.roleCount}"]
      emit (indexLines T.obj)
      emit (O.individualNames.filterMap fun a =>
        (nameIx T.obj (OWLFrontend.SHOIQ.nmOf O [] a)).map fun i => s!"nominal {i.val} {a}")
      out.flush
      return 0
  else if route == "sriqd-kb" then
    match translateSRIQDKB O [] [] with
    | none => decline (sriqdKBDecline O)
    | some T =>
      emit [s!"concepts {T.obj.conceptCount}", s!"roles {T.obj.roleCount}"]
      emit (indexLines T.obj)
      emit ((List.range T.obj.inds.length).zip T.obj.inds |>.map fun p => s!"individual {p.1} {p.2}")
      out.flush
      return 0
  else
    match translateSRIQKB O [] with
    | none => decline "not recognised: not an OWL SHIQ knowledge base"
    | some T =>
      emit [s!"concepts {T.conceptCount + (SRIQ.Proc.encTransQ T.ontology).1}",
        s!"roles {T.roleCount}"]
      emit (indexLines T)
      emit ((List.range T.inds.length).zip T.inds |>.map fun p => s!"individual {p.1} {p.2}")
      out.flush
      return 0

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
    let run : IO UInt32 := if args.checkOnly then do
        match OWL.parse text with
        | .error reason => decline s!"parse rejected: {reason}"
        | .ok O =>
          if args.dataRoute == some "sroiq-c2a" then
            let O := duOff O
            if ← checkS (← timingEnabled) (anonOff [] O) then do
              IO.println "accepted"
              return 0
            else if ← checkSelf (← timingEnabled) (anonOff [] O) then do
              IO.println "accepted"
              return 0
            else if ← checkZero (← timingEnabled) (anonOff [] O) then do
              IO.println "accepted"
              return 0
            else if ← checkHS (← timingEnabled) (anonOff [] O) then do
              IO.println "accepted"
              return 0
            else do
              if (← IO.getEnv "KM_C2A_WHY") == some "1" then
                let ws := whyC2a (anonOff [] O)
                IO.eprintln s!"why-summary pairs {ws.length} k-positive {(ws.filter fun l => !(l.splitOn "<= 0 ").length > 1).length}"
                for l in ws.take 20 do IO.eprintln s!"why: {l}"
              decline (sroiqDeclineS (anonOff [] O))
          else
          match translateSHOIQD O [] with
          | some T =>
            if kbdnOK T (OWLFrontend.SHOIQ.nomNames O []) then do
              IO.println "accepted"
              return 0
            else decline (shoiqDecline O)
          | none => decline (shoiqDecline O)
      else if args.printIndex then do
        match OWL.parse text with
        | .error reason => decline s!"parse rejected: {reason}"
        | .ok O => printIndex (args.dataRoute.getD "sriq-kb") O
      else match args.dataRoute with
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
  let usage := "usage: km-owl-reference [--procedure el|sri|el-then-sri|sriq|el-then-sriq|alc|el-then-alc|sriq-kb|sriqd|sriqd-kb|shoiq-c2a|sroiq-c2a] [--hint FILE] [--check] [--type CLASS INDIVIDUAL] [--print-index] <file.ofn> (default el-then-sri; --hint, --type and --print-index with sriq-kb, sriqd-kb and shoiq-c2a only)"
  match KMOWLReferenceCheck.parseArgs {} args with
  | some a =>
    match a.path with
    | some path =>
      if (a.hint.isSome || a.query.isSome || a.printIndex || a.checkOnly) &&
          !((a.procedure == .sriqKB && a.dataRoute.isNone) || a.dataRoute == some "sriqd-kb" ||
            a.dataRoute == some "shoiq-c2a" || a.dataRoute == some "sroiq-c2a") then
        IO.eprintln usage
        return 2
      else KMOWLReferenceCheck.runFile a path
    | none =>
      IO.eprintln usage
      return 2
  | none =>
    IO.eprintln usage
    return 2
