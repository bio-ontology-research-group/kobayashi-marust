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
import ContextCalculus.OWLFrontend.DatatypeDef
import ContextCalculus.OWLFrontend.HintBatch
import ContextCalculus.OWLFrontend.RuleGround
import ContextCalculus.OWLFrontend.KeyRules
import ContextCalculus.OWLFrontend.EdgeStrengthen
import ContextCalculus.SRIQN.HintExplain
import ContextCalculus.OWLFrontend.HintWitnessA
import ContextCalculus.OWLFrontend.HintRows
import ContextCalculus.OWLFrontend.HintRowsD

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
km-owl-reference --procedure sroiq-hint --hint FILE [--row ROW] <file.ofn>
km-owl-reference --procedure sroiq-hint --batch FILE|- <file.ofn>
km-owl-reference --procedure sroiq-hint --check|--print-index|--print-clauses [--row ROW] <file.ofn>
```

`sroiq-hint` is the hint-only route of stage C5 (`OWLFrontend/HintRoute.lean`,
`docs/V1.7.0-C5-HINT-ROUTE.md`): the translations of `sroiq-c2a` without the
C2a check, answering only when the hint checks. A certified row prints
`{"format":"owl-hint-v1","row":ROW,"certified":true}` (exit 0;
`hintRowAns_sound`); otherwise the reason goes to stderr (exit 3). `ROW` is
one argument: `consistent` (default), `nontype C a`, `nonsame a b`,
`nonsub A B`, `nondiff a b`, `nonrole r a b`, `nonnrole r a b`,
`nonsubs A B1 B2 ...`, `nontypes a C1 C2 ...` (full IRIs; `^IRI` is the
inverse of a property). `--batch` reads pairs `row ...` / hint lines / `end`
and prints one `owl-hint-batch-v1` line per pair (`certified`, `rejected`:
the hint does not check, `declined`: outside the route); pairs with the same
row share one translation (`hintRowsB_eq`, `hintPB_eq`). `--print-index`
prints the tables of the core the route uses on the (row-extended)
ontology; `--print-clauses` prints the object clauses and nominal names the
hint is checked against (a diagnostic).

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

/-- The ontology with its datatype definitions unfolded (`dtLoop`); `none`
when a definition cannot be unfolded. -/
def dtUnfold (O : OWL.Ontology) : Option OWL.Ontology :=
  if (splitDef O.axioms).isSome then dtLoop O.axioms.length O else some O

/-- The decline of `sroiq-c2a` after the unfolding of datatype definitions. -/
def sroiqDeclineD (O : OWL.Ontology) (prep : OWL.Ontology → OWL.Ontology) : String :=
  match dtUnfold O with
  | some O' => sroiqDeclineS (prep O')
  | none => "not recognised: a DatatypeDefinition of a datatype of the map, a recursive " ++
      "definition, two definitions of one datatype, or HasKey"

/-- Print the consistency verdict of `owlSROIQDC2aConsistent`
(`owlSROIQDAConsistent_sound`). -/
def publishConsistentS (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlC3DConsistent O hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-consistency-v1\",\"consistent\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- Print the verdict of `owlSROIQDTypeRow` (`owlSROIQDATypeRow_sound`). -/
def publishTypeS (C a : OWL.IRI) (v : Bool) {O : OWL.Ontology} {hint : Option RawHint}
    (_h : owlC3DTypeRow O C a hint = some v) : IO UInt32 := do
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
    let ⟨res, hres⟩ ← timedPhase timing "type" (fun _ => owlC3DTypeRow O C a hint)
    match res, hres with
    | some v, h => publishTypeS C a v h.symm
    | none, _ =>
      IO.eprintln (sroiqDeclineD O (fun O => addAxs (anonOff [a] (duOff O)) (typeAxs C a)))
      return 3
  | none =>
    let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlC3DConsistent O hint)
    match res, hres with
    | some v, h => publishConsistentS v h.symm
    | none, _ =>
      IO.eprintln (sroiqDeclineD O (fun O => anonOff [] (duOff O)))
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
        if (← IO.getEnv "KM_CHAIN_STATS") == some "1" then
          let B0 := objC T L E
          let rs := SROIQ.rules B0
          let tab := SROIQ.Proc.mkTab B0
          let le := SROIQ.Proc.leF tab
          let qs := SROIQ.Proc.allsQT rs le B0
          let tb := SROIQ.Proc.reachTab (SROIQ.Proc.succsT rs le) qs
          IO.eprintln s!"chain-stats n {T.obj.conceptCount} m {T.obj.roleCount} clauses {B0.length} rules {rs.length} alls {qs.length} roles {tb.length} stacks {(tb.map (·.2.length)).sum} pairs {(SROIQ.Proc.pairsPF B0).length}"
        let ⟨D1, _⟩ ← timedPhase timing "chain-encode" (fun _ => chC T L E)
        let ⟨B1, _⟩ ← timedPhase timing "chain-obj" (fun _ => SRIQD.objPart (SRIQN.dbase D1))
        let sc1 := scC T L E SC
        let ⟨hm1, _⟩ ← timedPhase timing "role-table"
          (fun _ => Std.HashMap.ofList (SROIQ.Proc.mkTab B1))
        let le1 := SROIQ.Proc.leH hm1
        let ⟨lam, _⟩ ← timedPhase timing "loop-set" (fun _ => SROIQ.Proc.lamOfL le1 B1 sc1)
        let ⟨irr, _⟩ ← timedPhase timing "irr-set" (fun _ => SROIQ.Proc.irrOfL le1 sc1)
        let ⟨r4, _⟩ ← timedPhase timing "loop-roles" (fun _ => SROIQ.Proc.lamOKBL le1 B1 sc1 lam irr)
        if !r4 then return false
        let ⟨D, _⟩ ← timedPhase timing "encode" (fun _ => SRIQN.encSelfD D1 sc1 lam irr)
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
  /-- `sroiq-hint`: print the clauses a hint is checked against. -/
  printClauses : Bool := false
  /-- `sroiq-hint`: the row, in words (`parseRow`). -/
  row : Option String := none
  /-- `sroiq-hint`: a batch file of (row, hint) pairs, `-` for stdin. -/
  batch : Option String := none
  /-- `sroiq-hint`: the row read from a file (words separated by blanks or newlines). -/
  rowFile : Option String := none
  /-- `sroiq-hint`: print the reason of a rejection on stderr. -/
  explain : Bool := false
  /-- `sroiq-hint`: the witness table of the global witness row. -/
  witness : Option String := none
  /-- `sroiq-hint`: the output file of the witness row. -/
  out : Option String := none
  /-- `sroiq-hint`: the requested classes of the witness row (default: all). -/
  classes : Option String := none
  /-- `sroiq-hint`: `--print-index`, `--print-clauses` of the witness route. -/
  witnessRoute : Bool := false
  /-- `sroiq-hint --witness`: print the property rows (stage H4). -/
  propertyRows : Bool := false
  /-- `sroiq-hint --witness`: a document of axioms to refute on the model (stage H4). -/
  axioms : Option String := none
  /-- `sroiq-hint --witness`: print only the counts of the class and individual rows. -/
  countsOnly : Bool := false
  /-- `sroiq-hint --witness`: print the data property rows (stage H5). -/
  dataPropertyRows : Bool := false
  /-- `sroiq-hint --witness`: classes by position in a `class_index` line. -/
  compact : Bool := false

def parseArgs (acc : Args) : List String → Option Args
  | [] => if acc.path.isSome then some acc else none
  | "--procedure" :: "sriqd" :: rest => parseArgs { acc with dataRoute := some "sriqd" } rest
  | "--procedure" :: "sriqd-kb" :: rest => parseArgs { acc with dataRoute := some "sriqd-kb" } rest
  | "--procedure" :: "shoiq-c2a" :: rest =>
    parseArgs { acc with dataRoute := some "shoiq-c2a" } rest
  | "--procedure" :: "sroiq-c2a" :: rest =>
    parseArgs { acc with dataRoute := some "sroiq-c2a" } rest
  | "--procedure" :: "sroiq-hint" :: rest =>
    parseArgs { acc with dataRoute := some "sroiq-hint" } rest
  | "--print-clauses" :: rest => parseArgs { acc with printClauses := true } rest
  | "--row" :: r :: rest => parseArgs { acc with row := some r } rest
  | "--batch" :: f :: rest => parseArgs { acc with batch := some f } rest
  | "--row-file" :: f :: rest => parseArgs { acc with rowFile := some f } rest
  | "--explain" :: rest => parseArgs { acc with explain := true } rest
  | "--witness" :: f :: rest => parseArgs { acc with witness := some f } rest
  | "--out" :: f :: rest => parseArgs { acc with out := some f } rest
  | "--classes" :: f :: rest => parseArgs { acc with classes := some f } rest
  | "--witness-route" :: rest => parseArgs { acc with witnessRoute := true } rest
  | "--property-rows" :: rest => parseArgs { acc with propertyRows := true } rest
  | "--axioms" :: f :: rest => parseArgs { acc with axioms := some f } rest
  | "--counts-only" :: rest => parseArgs { acc with countsOnly := true } rest
  | "--data-property-rows" :: rest => parseArgs { acc with dataPropertyRows := true } rest
  | "--compact" :: rest => parseArgs { acc with compact := true } rest
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

/-- A concept index found through a table (printing only; `nameIx` is the
first position of the IRI in `T.named`). -/
structure NIx where
  val : Nat

def nameIxMap (named : List String) : Std.HashMap String Nat :=
  named.zipIdx.foldl (fun mp p => mp.insertIfNew p.1 p.2) {}

def nameIxH (mp : Std.HashMap String Nat) (a : OWL.IRI) : Option NIx := (mp.get? a).map NIx.mk

/-- The `nominal` lines (printing only: `nmOf` with its base computed once). -/
def nomLines (nmap : Std.HashMap String Nat) (X : OWL.Ontology) (req : List OWL.IRI) : List String :=
  let base := OWLFrontend.SHOIQ.nomBase X req
  X.individualNames.zipIdx.filterMap fun (a, j) =>
    (nameIxH nmap (OWLFrontend.SHOIQ.nomName base j)).map fun i => s!"nominal {i.val} {a}"

/-- The index lines of a knowledge-base translation: concept and role
indices of the IRIs, sorted by index. -/
def indexLines (T : SRIQKBTranslation) : List String :=
  let cs := (T.cnames.toArray.qsort (fun a b => a.2 < b.2)).toList
  let rs := (T.rnames.toArray.qsort (fun a b => a.2 < b.2)).toList
  (cs.map fun p => s!"concept {p.2} {p.1}") ++ (rs.map fun p => s!"role {p.2} {p.1}")

/-- The index lines of the route with `ObjectHasSelf` (input renamed by `anonOff`). -/
def printIndexHS (O : OWL.Ontology) : IO UInt32 := do
  let out ← IO.getStdout
  let emit (ls : List String) : IO Unit := do for l in ls do out.putStrLn l
  let O0 := O
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
      let nmap := nameIxMap T.obj.named
      emit (nomLines nmap (roleOff (selfOff O)) (pairNames P))
      -- the class of `ObjectHasSelf(r)`: `hasself I IRI` or `hasself I inv IRI`
      emit (P.filterMap fun p =>
        (nameIxH nmap p.1).map fun i =>
          match p.2 with
          | .inv r => s!"hasself {i.val} inv {r}"
          | r => s!"hasself {i.val} {r.name}")
      emit [s!"loops {n1}", s!"splits {n1 + 2 * m}", s!"guards {n1 + 2 * m + 3 * nc}",
        s!"fresh-nominal {n1 + 2 * m + 3 * nc + n1 + 1}"]
      out.flush
      return 0
    | _, _, _ => decline (hsDecline O0)

/-- The index lines of the Self route (input renamed by `anonOff`). -/
def printIndexSelf (O : OWL.Ontology) : IO UInt32 := do
  let out ← IO.getStdout
  let emit (ls : List String) : IO Unit := do for l in ls do out.putStrLn l
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
      let nmap := nameIxMap T.obj.named
      emit (nomLines nmap (roleOff (selfOff O)) [])
      -- the Self encoding: loop names from n1 (role j: n1 + j, its inverse n1 + m + j),
      -- split names, nominal guards, the fresh nominal
      emit [s!"loops {n1}", s!"splits {n1 + 2 * m}", s!"guards {n1 + 2 * m + 3 * nc}",
        s!"fresh-nominal {n1 + 2 * m + 3 * nc + n1 + 1}"]
      out.flush
      return 0
    | _, _ => decline (selfDecline O)

/-- The index lines of the at-most-zero route (input renamed by `anonOff`). -/
def printIndexZero (O : OWL.Ontology) : IO UInt32 := do
  let out ← IO.getStdout
  let emit (ls : List String) : IO Unit := do for l in ls do out.putStrLn l
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
      let nmap := nameIxMap T.obj.named
      emit (nomLines nmap (roleOff O) [])
      -- the at-most-zero rewriting: one name per object clause from n1
      emit [s!"zeros {n1}"]
      out.flush
      return 0

/-- The index lines of the chain route (input renamed by `anonOff`). -/
def printIndexChain (O : OWL.Ontology) : IO UInt32 := do
  let out ← IO.getStdout
  let emit (ls : List String) : IO Unit := do for l in ls do out.putStrLn l
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
      let nmap := nameIxMap T.obj.named
      emit (nomLines nmap (roleOff O) [])
      out.flush
      return 0

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
  let O := if route == "sroiq-c2a" then duOff ((dtUnfold O).getD O) else O
  if route == "sroiq-c2a" && !(selfPairs (anonOff [] O)).isEmpty &&
      !(anonOff [] O).isSROIQDSKB then
    printIndexHS (anonOff [] O)
  else if route == "sroiq-c2a" && !(← checkS false (anonOff [] O)) && (anonOff [] O).isSROIQDSKB &&
      !(selfAxs (anonOff [] O)).isEmpty then
    printIndexSelf (anonOff [] O)
  else if route == "sroiq-c2a" && !(← checkS false (anonOff [] O)) && (← checkZero false (anonOff [] O)) then
    printIndexZero (anonOff [] O)
  else if route == "sroiq-c2a" then
    printIndexChain (anonOff [] O)
  else if route == "shoiq-c2a" then
    match translateSHOIQD O [] with
    | none => decline (shoiqDecline O)
    | some T =>
      let L := OWLFrontend.SHOIQ.nomNames O []
      emit [s!"concepts {T.obj.conceptCount + SRIQN.Proc.encKD (dosn T L)}",
        s!"roles {T.obj.roleCount}"]
      emit (indexLines T.obj)
      let nmap := nameIxMap T.obj.named
      emit (nomLines nmap O [])
      out.flush
      return 0
  else if route == "sriqd-kb" then
    match translateSRIQDKB O [] [] with
    | none => decline (sriqdKBDecline O)
    | some T =>
      emit [s!"concepts {T.obj.conceptCount}", s!"roles {T.obj.roleCount}"]
      emit (indexLines T.obj)
      let nmap := nameIxMap T.obj.named
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


/-! ### The hint-only route (`--procedure sroiq-hint`, stage C5) -/

/-- An object property in a row: `IRI` or `^IRI` (its inverse). -/
def parseProp (w : String) : OWL.ObjProp :=
  if w.startsWith "^" then .inv (w.drop 1).toString else .named w

/-- A row in words: `consistent`, `nontype C a`, `nonsame a b`, `nonsub A B`,
`nondiff a b`, `nonrole r a b`, `nonnrole r a b`, `nonsubs A B1 B2 ...`,
`nontypes a C1 C2 ...` (a property `r` is `IRI` or `^IRI`). -/
def parseRow0 (ws : List String) : Except String HintRowSpec :=
  match ws with
  | [] | ["consistent"] => .ok .consistent
  | ["nontype", C, a] => .ok (.nontype C a)
  | ["nonsame", a, b] => .ok (.nonsame a b)
  | ["nonsub", A, B] => .ok (.nonsub A B)
  | ["nondiff", a, b] => .ok (.nondiff a b)
  | ["nonrole", r, a, b] => .ok (.nonrole (parseProp r) a b)
  | ["nonnrole", r, a, b] => .ok (.nonnrole (parseProp r) a b)
  | "nonsubs" :: A :: Bs => .ok (.nonsubs A Bs)
  | "nontypes" :: a :: Cs => .ok (.nontypes a Cs)
  | _ => .error s!"bad row: {" ".intercalate ws}"


/-- A row with a built-in IRI where its OWL meaning differs from the free
name the row axioms would read (`HintBuiltin.lean`): `owl:Thing` as the
object of a subsumption or type, `owl:Nothing` as the subject of a
subsumption, `owl:topObjectProperty` and `owl:bottomObjectProperty` as
properties. Such a row would certify a statement about a free name, so it
is refused. `owl:Nothing` as object and `owl:Thing` as subject keep their
meaning (`hintNonSubC_sound`, `hintNonTypeC_sound`). -/
def rowBuiltin (r : HintRowSpec) : Option String :=
  let T := OWL.Parse.owlThing
  let N := OWL.Parse.owlNothing
  let msgT := "owl:Thing as object: every subsumption and type with owl:Thing holds; the row is refused"
  let msgN := "owl:Nothing as subject: owl:Nothing is below every class; the row is refused"
  let topP (p : OWL.ObjProp) : Bool := match p with
    | .named w | .inv w => w == OWL.Parse.owlTopObjectProperty || w == OWL.Parse.owlBottomObjectProperty
    | _ => true
  match r with
  | .nontype C _ => if C == T then some msgT else none
  | .nonsub A B => if A == N then some msgN else if B == T then some msgT else none
  | .nonsubs A Bs => if A == N then some msgN else if Bs.contains T then some msgT else none
  | .nontypes _ Cs => if Cs.contains T then some msgT else none
  | .nonrole p _ _ | .nonnrole p _ _ =>
    if topP p then some "owl:topObjectProperty or owl:bottomObjectProperty as a row property is refused" else none
  | _ => none

def parseRow (ws : List String) : Except String HintRowSpec :=
  match parseRow0 ws with
  | .ok r => match rowBuiltin r with
    | some e => .error e
    | none => .ok r
  | .error e => .error e

def wordsOf (line : String) : List String :=
  ((line.split fun c => c == ' ' || c == '\t' || c == '\r' || c == '\n').toList.map (·.toString)).filter (· ≠ "")

/-- The words of a batch line up to a comment: a word that starts with `#`
starts a comment, a `#` inside a word (an IRI) does not. -/
def batchWords (line : String) : List String :=
  (wordsOf line).takeWhile fun w => !w.startsWith "#"

/-- The ontology a row's hint is checked against (`none`: an axiom of the
extension is a `HasKey`). -/
def rowOntology (O : OWL.Ontology) (r : HintRowSpec) : Option OWL.Ontology :=
  match r.axs O with
  | none => some O
  | some L => if (addAxs O L).noKey then some (addAxs O L) else none

/-- The hint route's fragment on an ontology, as the route sees it after
unfolding, the disjoint-union rewriting and the renaming of anonymous
individuals: `none` when datatype definitions cannot be unfolded. -/
def hintPrep (O : OWL.Ontology) : Option OWL.Ontology :=
  (dtUnfold O).map fun O' => anonOff [] (duOff O')

/-- Why the hint route declines a prepared ontology. -/
def hintDecline (X : OWL.Ontology) : String :=
  let base (O : OWL.Ontology) (requested : List OWL.IRI) (sc : Bool) : String :=
    if !O.isSROIQDSKB then
      s!"not recognised: not an OWL SROIQ(D) knowledge base ({firstFailing O OWL.Axiom.isSROIQDSKB})"
    else match translateSHOIQD (roleOff (if sc then selfOff O else O)) requested with
      | none => "not recognised: the SHOIQ(D) translation failed"
      | some _ =>
        "checks failed: role regularity, chain elimination (closed automata, simple counting " ++
        "roles), the Self conditions, a role index, or a data range outside the supported sub-theory"
  if !(selfPairs X).isEmpty then base (hsOff X) (pairNames (selfPairs X)) true
  else if !(selfAxs X).isEmpty then base X [] true
  else if !X.isSROIQDKB then
    s!"not recognised: not an OWL SROIQ(D) knowledge base ({firstFailing X OWL.Axiom.isSROIQDKB})"
  else base X [] false

/-- The text of a row in the output. -/
def rowText (ws : List String) : String := if ws.isEmpty then "consistent" else " ".intercalate ws

/-- Print a certified row (`hintRowAns_sound`: the row holds at the OWL 2
datatype map, for every reading of `xsd:pattern`). -/
def publishHintRow (row : String) {O : OWL.Ontology} {r : HintRowSpec} {hint : RawHint}
    (_h : hintRowAns O r hint = some true) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-hint-v1\",\"row\":" ++ (Json.str row).compress ++
    ",\"certified\":true}")
  out.flush
  return 0

/-- Why a named data part is not a part (diagnostic, `--explain`): `ncell`
split cells of the given sizes, `G` groups. -/
def partWhy (hint : RawHint) (sizes : List (Option Nat)) (G : Nat) : Option String :=
  if !hint.partNamed then none else
  let ncell := sizes.length
  match hint.part.find? fun e => e.1 ≥ ncell || e.2.1 ≥ G with
  | some e => some s!"named part: line `part {e.1} {e.2.1} {e.2.2}` is outside the {ncell} split cells and {G} groups"
  | none =>
    (sizes.zipIdx.findSome? fun (sz, i) =>
      let tot := ((hint.part.filter fun e => e.1 == i).map (·.2.2)).sum
      if tot == sz.getD 0 then none
      else some s!"named part: the counts of split cell {i} add up to {tot}, its size is {sz.getD 0}")

/-- The first core element whose given data star fails, on the named part
(diagnostic, `--explain`; stage H4): the test of `hintPartsP` element by
element, with no search. -/
def starWhyD {n m p q s : Nat} {K : Type} [DecidableEq K] (O : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q))
    (cells : List K) (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hint : RawHint) : Option String :=
  match hint.toHintS (n + SRIQN.Proc.encKD O) m with
  | none => none
  | some h =>
    let Dd := SRIQN.HF.dataOnly (SRIQN.dbase (SRIQN.Proc.encTransDN O))
    let sc := cells.filter sp
    -- the named part, or the first part (the reason is then for that part)
    let x? := if h.partNamed then some (SRIQN.HF.namedPart sc (ContextCalculus.SRIQD.allG s).length h.part)
      else (ContextCalculus.SRIQD.partsOf size s sc).head?
    match x? with
    | none => none
    | some x =>
    let card := SRIQN.HF.partCardT (SRIQN.HF.partTab cells size sp E (ContextCalculus.SRIQD.toPart s x))
    let stars := SRIQN.HF.starsOf (p := p) (q := q) h
    let show_ := fun (e : ContextCalculus.SRIQD.DNbr (Fin p) (Fin q)) =>
      s!"{(e.1.sort (· ≤ ·)).map (·.val)} / {(e.2.sort (· ≤ ·)).map (·.val)}"
    (List.finRange h.k).findSome? fun b =>
      match (stars[b.val]?).getD none with
      | none => none
      | some l =>
        if !(l.all Option.isSome) then
          some s!"core element {b.val}: a dstar entry names a data property or an atom out of range"
        else
          let Dn := l.filterMap id
          let t := h.tyF b
          if Dn.length > ContextCalculus.SRIQD.dbnd Dd then
            some s!"core element {b.val}: {Dn.length} dstar entries, more than the bound {ContextCalculus.SRIQD.dbnd Dd}"
          else match Dn.find? (fun e => !decide (ContextCalculus.SRIQD.Proc.dcandOK Dd card t e)) with
            | some e => some s!"core element {b.val}: the dstar entry {show_ e} is not a possible entry (a data sub-property, a value-type count, a universal or an upper bound fails for it alone, or it serves no data clause of the type)"
            | none =>
              if decide (ContextCalculus.SRIQD.DOK Dd card t Dn) then none
              else some s!"core element {b.val}: the dstar entries together fail the star conditions (a lower bound is not met, or counts exceed an upper bound or a value-type count)"

/-- Why a hint is rejected on an encoded ontology (diagnostic, `--explain`);
`dataWhy` is the reason when the object part checks. -/
def explainOn {n m p q : Nat} (D : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (hint : RawHint)
    (loops : Bool) (dataWhy : Option String := none) : String :=
  let E := SRIQN.Proc.encTransDN D
  match hint.toHintS (n + SRIQN.Proc.encKD D) m with
  | none => "an index outside the translation (a concept, role or record index out of range)"
  | some h =>
    match SRIQN.HF.explainS (SRIQD.objPart (SRIQN.dbase E)) (SRIQN.dnoms E) h loops with
    | some w => w
    | none => dataWhy.getD (if hint.partNamed then
        "the object part checks; the data-star test fails on the named data part"
      else "the object part checks; the data-star test fails on every data part")

/-- The split cells (their sizes) and the number of groups of a translation. -/
def splitSizes (T : SRIQDKBTranslation) (L : List OWL.IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) (bound : Nat) :
    List (Option Nat) × Nat :=
  let sp := SHIQD.spec T.tab
  let as := OWL.Datatypes.allBases sp
  let cs := OWL.Datatypes.cellsOf as
  let sc := cs.filter (ContextCalculus.SRIQD.splitCell cs (OWL.Datatypes.cellSize as) bound (OWL.Datatypes.owlE sp))
  (sc.map (OWL.Datatypes.cellSize as), (ContextCalculus.SRIQD.allG (OWL.Datatypes.allFrees sp).length).length)

/-- Why a hint is rejected on a prepared ontology (`hintPrep`), along the
core the route uses (diagnostic, `--explain`). -/
def explainHint (O : OWL.Ontology) (hint : RawHint) : String :=
  if !(selfPairs O).isEmpty then
    let P := selfPairs O
    let O1 := hsOff O
    match translateSHOIQD (roleOff (selfOff O1)) (pairNames P) with
    | none => "not recognised"
    | some T =>
      match roleCls T (selfOff O1), selfCls T O1, pairCls T P with
      | some E, some SC, some PC =>
        explainOn (encS T (OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O1)) (pairNames P)) E (SC ++ PC))
          hint true
      | _, _, _ => "not recognised"
  else if !(owlChainHint O {}).isSome then
    match translateSHOIQD (roleOff (selfOff O)) [] with
    | none => "not recognised"
    | some T =>
      match roleCls T (selfOff O), selfCls T O with
      | some E, some SC => explainOn (encS T (OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) []) E SC) hint true
      | _, _ => "not recognised"
  else
    match translateSHOIQD (roleOff O) [] with
    | none => "not recognised"
    | some T =>
      match roleCls T O with
      | some E =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff O) []
        let (sz, G) := splitSizes T L E (sroiqBound T L E)
        explainOn (encC T L E) hint false (partWhy hint sz G)
      | none => "not recognised"

/-- `--procedure sroiq-hint --hint FILE [--row ROW]`: one hint, one row. -/
def runHintOne (timing : Bool) (O : OWL.Ontology) (rowWs : List String) (hint : RawHint)
    (explain : Bool := false) : IO UInt32 := do
  match parseRow rowWs with
  | .error e =>
    IO.eprintln e
    return 2
  | .ok r =>
    let ⟨res, hres⟩ ← timedPhase timing "hint-row" (fun _ => hintRowAns O r hint)
    match res, hres with
    | some true, h => publishHintRow (rowText rowWs) h.symm
    | _, _ =>
      match rowOntology O r with
      | none => decline "not recognised: HasKey in the ontology or the row"
      | some X =>
        match hintPrep X with
        | none => decline ("not recognised: a DatatypeDefinition of a datatype of the map, a " ++
            "recursive definition, or two definitions of one datatype")
        | some X' =>
          match hintP X hint with
          | some false =>
            if explain then IO.eprintln s!"hint: reason: {explainHint X' hint}"
            decline "hint: rejected (an index outside the translation, or the check fails)"
          | _ => decline (hintDecline X')

/-- A batch file: pairs `row ...` / hint lines / `end`. -/
def parseBatch (text : String) : Except String (List (List String × RawHint)) := do
  let mut acc : Array (List String × RawHint) := #[]
  let mut cur : Option (List String × Array String) := none
  for line in text.splitOn "\n" do
    let ws := batchWords line
    let body := " ".intercalate ws
    match cur, ws with
    | none, [] => pure ()
    | none, "row" :: rw => cur := some (rw, #[])
    | none, _ => throw s!"batch: expected `row ...`, got: {line}"
    | some (rw, ls), ["end"] =>
      match RawHint.parseHint ("\n".intercalate ls.toList) with
      | .ok h => acc := acc.push (rw, h)
      | .error e => throw s!"batch: bad hint for row {rowText rw}: {e}"
      cur := none
    | some (rw, ls), _ => cur := some (rw, ls.push body)
  if cur.isSome then throw "batch: missing `end`"
  return acc.toList

/-- `--procedure sroiq-hint --batch FILE`: every pair, one result line each,
in input order. Pairs with the same row share one translation of the
extended ontology and all its tables (`hintRowsB`, `hintRowsB_eq`). -/
def runHintBatch (timing : Bool) (O : OWL.Ontology) (pairs : List (List String × RawHint))
    (explain : Bool := false) : IO UInt32 := do
  let out ← IO.getStdout
  -- the distinct rows, in order of first occurrence
  let rows := (pairs.map (·.1)).eraseDups
  let mut results : Std.HashMap Nat String := {}
  let idx := (List.range pairs.length).zip pairs
  for rw in rows do
    let mine := idx.filter (·.2.1 == rw)
    match parseRow rw with
    | .error e =>
      for (i, _) in mine do results := results.insert i s!"\"declined\",\"reason\":{(Json.str e).compress}"
    | .ok r =>
      let hs := mine.map (·.2.2)
      match rowOntology O r with
      | none =>
        for (i, _) in mine do
          results := results.insert i "\"declined\",\"reason\":\"HasKey\""
      | some X =>
        -- `hintPB X hs = hs.map (hintP X)` (`hintPB_eq`); a `some true` is the
        -- certified answer of `hintRowAns O r` (`hintRowsB_eq`, `hintRowAns_sound`)
        let ⟨rs, _⟩ ← timedPhase timing "hint-batch" (fun _ => hintPB X hs)
        for ((i, (_, hi)), v) in mine.zip rs do
          let t := match v with
            | some true => "\"certified\""
            | some false =>
              if explain then
                let why := match hintPrep X with
                  | some X' => explainHint X' hi
                  | none => "DatatypeDefinition"
                "\"rejected\",\"reason\":" ++ (Json.str why).compress
              else "\"rejected\""
            | none => "\"declined\""
          results := results.insert i t
  for (i, (rw, _)) in idx do
    let t := results.getD i "\"declined\""
    out.putStrLn ("{\"format\":\"owl-hint-batch-v1\",\"pair\":" ++ toString i ++ ",\"row\":" ++
      (Json.str (rowText rw)).compress ++ ",\"result\":" ++ t ++ "}")
  out.flush
  return 0

/-- `--procedure sroiq-hint --check [--row ROW]`: the fragment checks of the
hint route (an empty hint is checked, so the answer is `none` or `some false`). -/
def checkHint (O : OWL.Ontology) (rowWs : List String) : IO UInt32 := do
  match parseRow rowWs with
  | .error e => IO.eprintln e; return 2
  | .ok r =>
    match rowOntology O r with
    | none => decline "not recognised: HasKey in the ontology or the row"
    | some X =>
      match hintPrep X with
      | none => decline ("not recognised: a DatatypeDefinition of a datatype of the map, a " ++
          "recursive definition, or two definitions of one datatype")
      | some X' =>
        -- `hintPFrag_eq`: the fragment check is `(hintP X h).isSome` for every hint
        if hintPFrag X then
          IO.println "accepted"
          return 0
        else decline (hintDecline X')

/-- `--procedure sroiq-hint --print-index [--row ROW]`: the index tables of
the core the hint route uses on the (extended) ontology. -/
def printIndexHint (O : OWL.Ontology) (rowWs : List String) : IO UInt32 := do
  match parseRow rowWs with
  | .error e => IO.eprintln e; return 2
  | .ok r =>
    let X := match r.axs O with
      | none => O
      | some L => addAxs O L
    match hintPrep X with
    | none => decline ("not recognised: a DatatypeDefinition of a datatype of the map, a " ++
        "recursive definition, or two definitions of one datatype")
    | some X' =>
      if !(selfPairs X').isEmpty then printIndexHS X'
      else if (owlChainHint X' {}).isSome then printIndexChain X'
      else printIndexSelf X'


/-- A role in the hint text format. -/
def rtText {m : Nat} : SRI.RoleT (Fin m) → String
  | .pos r => s!"+{r.val}"
  | .inv r => s!"-{r.val}"

/-- A normalised clause, for `--print-clauses` (diagnostic, not part of any
proved statement). -/
def clauseText {n m : Nat} : SRIQ.Clause (Fin n) (Fin m) → String
  | .gci b h => s!"gci {" ".intercalate (b.map (toString ·.val))} -> {" ".intercalate (h.map (toString ·.val))}"
  | .exRight a R b => s!"some {a.val} {rtText R} {b.val}"
  | .allRight a R b => s!"all {a.val} {rtText R} {b.val}"
  | .atLeast a k R b => s!"atleast {a.val} {k} {rtText R} {b.val}"
  | .atMost a k R b => s!"atmost {a.val} {k} {rtText R} {b.val}"
  | .chain body S => s!"chain {" ".intercalate (body.map rtText)} {rtText S}"

/-- Print the object clauses and nominal names a hint is checked against
(`checkRedN`), and the number of data clauses. -/
def emitClauses {n m p q : Nat} (D : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) : IO UInt32 := do
  let out ← IO.getStdout
  let E := SRIQN.Proc.encTransDN D
  for cl in SRIQD.objPart (SRIQN.dbase E) do out.putStrLn (clauseText cl)
  for a in SRIQN.dnoms E do out.putStrLn s!"nom {a.val}"
  out.putStrLn s!"data-clauses {(SRIQN.dbase E).length - (SRIQD.objPart (SRIQN.dbase E)).length}"
  out.flush
  return 0

/-- A data clause, for `--print-clauses` (diagnostic). `p` data property,
atoms by their index in the `atom` lines; `(j, false)` is the complement. -/
def dclauseText {n m p q : Nat} : SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q) → Option String
  | .obj _ => none
  | .dEx a u pos neg => some s!"dsome {a.val} {u.val} {" ".intercalate (pos.map (toString ·.val))} / {" ".intercalate (neg.map (toString ·.val))}"
  | .dAll a u hd => some s!"dall {a.val} {u.val} {" ".intercalate (hd.map fun e => (if e.2 then "" else "~") ++ toString e.1.val)}"
  | .dAtLeast a k u pos neg => some s!"datleast {a.val} {k} {u.val} {" ".intercalate (pos.map (toString ·.val))} / {" ".intercalate (neg.map (toString ·.val))}"
  | .dAtMost a k u pos neg => some s!"datmost {a.val} {k} {u.val} {" ".intercalate (pos.map (toString ·.val))} / {" ".intercalate (neg.map (toString ·.val))}"
  | .dSub u v => some s!"dsub {u.val} {v.val}"

/-- The data clauses, the data atoms, the free datatypes, the groups and
the split cells of the data part a hint names (`part I G N`: count `N` of
group `G` in split cell `I`). -/
def emitData (T : SRIQDKBTranslation) (L : List OWL.IRI)
    (E : List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount))) : IO Unit := do
  let out ← IO.getStdout
  let D := encC T L E
  for cl in SRIQN.dbase (SRIQN.Proc.encTransDN D) do
    match dclauseText cl with
    | some t => out.putStrLn t
    | none => pure ()
  let sp := SHIQD.spec T.tab
  for j in List.finRange T.tab.length do out.putStrLn s!"atom {j.val} {(reprStr (sp j)).replace "\n" " "}"
  let fr := OWL.Datatypes.allFrees sp
  for (f, i) in fr.zipIdx do out.putStrLn s!"free {i} {f}"
  let gs := ContextCalculus.SRIQD.allG fr.length
  out.putStrLn s!"groups {gs.length}"
  if gs.length ≤ 4096 then
    for (g, i) in gs.zipIdx do
      out.putStrLn s!"group {i} {String.join ((List.finRange fr.length).map fun j => if g j then "1" else "0")}"
  let as := OWL.Datatypes.allBases sp
  let cs := OWL.Datatypes.cellsOf as
  let sc := cs.filter (ContextCalculus.SRIQD.splitCell cs (OWL.Datatypes.cellSize as) (sroiqBound T L E) (OWL.Datatypes.owlE sp))
  for (c, i) in sc.zipIdx do
    out.putStrLn s!"cell {i} {((OWL.Datatypes.cellSize as c).map toString).getD "inf"} {(reprStr c).replace "\n" " "}"
  out.flush

/-- `--procedure sroiq-hint --print-clauses [--row ROW]`. -/
def printClausesHint (O : OWL.Ontology) (rowWs : List String) : IO UInt32 := do
  match parseRow rowWs with
  | .error e => IO.eprintln e; return 2
  | .ok r =>
    let X := match r.axs O with
      | none => O
      | some L => addAxs O L
    match hintPrep X with
    | none => decline "not recognised: DatatypeDefinition"
    | some O =>
      if !(selfPairs O).isEmpty then
        let P := selfPairs O
        let O1 := hsOff O
        match translateSHOIQD (roleOff (selfOff O1)) (pairNames P) with
        | none => decline "not recognised"
        | some T =>
          match roleCls T (selfOff O1), selfCls T O1, pairCls T P with
          | some E, some SC, some PC =>
            emitClauses (encS T (OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O1)) (pairNames P)) E (SC ++ PC))
          | _, _, _ => decline "not recognised"
      else if !(owlChainHint O {}).isSome then
        match translateSHOIQD (roleOff (selfOff O)) [] with
        | none => decline "not recognised"
        | some T =>
          match roleCls T (selfOff O), selfCls T O with
          | some E, some SC => emitClauses (encS T (OWLFrontend.SHOIQ.nomNames (roleOff (selfOff O)) []) E SC)
          | _, _ => decline "not recognised"
      else
        match translateSHOIQD (roleOff O) [] with
        | none => decline "not recognised"
        | some T =>
          match roleCls T O with
          | some E =>
            let c ← emitClauses (encC T (OWLFrontend.SHOIQ.nomNames (roleOff O) []) E)
            emitData T (OWLFrontend.SHOIQ.nomNames (roleOff O) []) E
            return c
          | none => decline "not recognised"

/-! ### The global witness row (stage H2, item 5) -/

/-- The witness table: `witness CLASS W` lines (`#` words start comments). -/
def parseWitness (text : String) : Except String (List (OWL.IRI × Nat)) := do
  let mut acc : Array (OWL.IRI × Nat) := #[]
  for line in text.splitOn "\n" do
    match batchWords line with
    | [] => pure ()
    | ["witness", A, w] =>
      match w.toNat? with
      | some k => acc := acc.push (A, k)
      | none => throw s!"witness: not a number: {w}"
    | ["ind", _, _] => pure ()
    | _ => throw s!"witness: expected `witness CLASS W`, got: {line}"
  return acc.toList

def jsonList (l : List String) : String := "[" ++ ",".intercalate (l.map fun x => (Json.str x).compress) ++ "]"

/-- The name of a property expression in the output (`^IRI` an inverse). -/
def propName : OWL.ObjProp → String
  | .named i => i
  | .inv i => "^" ++ i
  | .top => OWL.Parse.owlNs ++ "topObjectProperty"
  | .bot => OWL.Parse.owlNs ++ "bottomObjectProperty"

/-- The name of an axiom kind in the output. -/
def axKind : OWL.Axiom → String
  | .subClassOf .. => "SubClassOf"
  | .equivalentClasses .. => "EquivalentClasses"
  | .disjointClasses .. => "DisjointClasses"
  | .domain .. => "ObjectPropertyDomain"
  | .range .. => "ObjectPropertyRange"
  | .subObjectPropertyOf .. => "SubObjectPropertyOf"
  | .equivalentObjectProperties .. => "EquivalentObjectProperties"
  | .inverseObjectProperties .. => "InverseObjectProperties"
  | .transitive .. => "TransitiveObjectProperty"
  | .symmetric .. => "SymmetricObjectProperty"
  | .disjointObjectProperties .. => "DisjointObjectProperties"
  | .functional .. => "FunctionalObjectProperty"
  | .inverseFunctional .. => "InverseFunctionalObjectProperty"
  | .reflexive .. => "ReflexiveObjectProperty"
  | .irreflexive .. => "IrreflexiveObjectProperty"
  | .asymmetric .. => "AsymmetricObjectProperty"
  | .sameIndividual .. => "SameIndividual"
  | .differentIndividuals .. => "DifferentIndividuals"
  | .classAssertion .. => "ClassAssertion"
  | .objectPropertyAssertion .. => "ObjectPropertyAssertion"
  | .negativeObjectPropertyAssertion .. => "NegativeObjectPropertyAssertion"
  | .subDataPropertyOf .. => "SubDataPropertyOf"
  | .equivalentDataProperties .. => "EquivalentDataProperties"
  | .disjointDataProperties .. => "DisjointDataProperties"
  | .dataDomain .. => "DataPropertyDomain"
  | .dataRange .. => "DataPropertyRange"
  | .functionalData .. => "FunctionalDataProperty"
  | .dataPropertyAssertion .. => "DataPropertyAssertion"
  | .negativeDataPropertyAssertion .. => "NegativeDataPropertyAssertion"
  | _ => "other"

/-- The IRIs of a list without repetitions, in first-occurrence order. -/
def dedupS (l : List OWL.IRI) : List OWL.IRI :=
  (l.foldl (fun (acc : Std.HashSet OWL.IRI × Array OWL.IRI) a =>
    if acc.1.contains a then acc else (acc.1.insert a, acc.2.push a)) ({}, #[])).2.toList

/-- The data rows of stage H5 (`hintRefuteDMM_sound`): every printed
non-entailment is `refuteD KD ax = true` for the axiom `ax` named by the
line, with `KD = ckxMemo (ckOfDM W ckFuel (splitDef O.axioms).isNone props) dps`. -/
def publishData (out : IO.FS.Stream) (W : OWLFrontend.WTab) (KD : OWLFrontend.CKX W.k)
    (elems : List (Fin W.k)) (dps : List OWL.IRI) (dOn : Bool) : IO Unit := do
  let given := (List.finRange W.k).filter fun w => (W.dst w).isSome
  out.putStrLn ("{\"data_rows\":{\"data\":" ++ toString dOn ++
    ",\"properties\":" ++ toString dps.length ++ ",\"given\":" ++ toString given.length ++ "}}")
  -- the values of the individuals' elements: one entry per value, its atoms
  let mut vals : Array String := #[]
  for w in elems do
    match W.dst w with
    | none => pure ()
    | some S =>
      for P in dps do
        let s := KD.dv (.named P) w
        if !s.1.isEmpty then
          let cells := s.1.map fun i => match S[i]? with
            | some e => "[" ++ ",".intercalate (((List.finRange W.q).filter (· ∈ e.2)).map (toString ·.val)) ++ "]"
            | none => "[]"
          vals := vals.push ("[" ++ toString w.val ++ "," ++ (Json.str P).compress ++ ",[" ++
            ",".intercalate cells ++ "]," ++ toString s.2 ++ "]")
  out.putStrLn ("{\"individual_values\":[" ++ ",".intercalate vals.toList ++ "]}")
  let clsI := dedupS (W.cls.map (·.1))
  for P in dps do
    let p := OWL.DataProp.named P
    let others := (dps.filter (· != P)).map OWL.DataProp.named
    let dname : OWL.DataProp → String := fun q => match q with
      | .named i => i
      | .top => OWL.Parse.owlNs ++ "topDataProperty"
      | .bot => OWL.Parse.owlNs ++ "bottomDataProperty"
    let nonsub := others.filter fun t => OWLFrontend.refuteD KD (.subDataPropertyOf p t)
    let noneq := others.filter fun t => OWLFrontend.refuteD KD (.equivalentDataProperties [p, t])
    let nondis := others.filter fun t => OWLFrontend.refuteD KD (.disjointDataProperties [p, t])
    let nonempty := OWLFrontend.refuteD KD (.subDataPropertyOf p .bot)
    let notE := if OWLFrontend.refuteD KD (.functionalData p) then ["functional"] else []
    let domNot := clsI.filter fun C => OWLFrontend.refuteD KD (.dataDomain p (.cls C))
    let ranNot := (List.finRange W.q).filter fun j => OWLFrontend.refuteD KD (.dataRange p (W.dsp j))
    out.putStrLn ("{\"data_property\":" ++ (Json.str P).compress ++ ",\"nonempty\":" ++
      toString nonempty ++ ",\"nonsub\":" ++ jsonList (nonsub.map dname) ++
      ",\"nonequiv\":" ++ jsonList (noneq.map dname) ++
      ",\"nondisjoint\":" ++ jsonList (nondis.map dname) ++
      ",\"not_entailed\":" ++ jsonList notE ++ ",\"domain_not\":" ++ jsonList domNot ++
      ",\"range_not_atoms\":[" ++ ",".intercalate (ranNot.map (toString ·.val)) ++ "]}")

/-- The role rows of stage H4 (`hintRefuteM_sound`, `hintRefuteMR_sound`):
every printed non-entailment is `refute K ax = true` for the axiom `ax`
named by the line, with `K = ckMemo (ckOf W ckFuel) props`. -/
def publishRoles (out : IO.FS.Stream) (W : OWLFrontend.WTab) (showInd : OWL.IRI → Bool)
    (propRows : Bool) (axs : List OWL.Axiom) (KD : Option (OWLFrontend.CKX W.k) := none)
    (dataRows : Bool := false) (dOn : Bool := false) : IO Unit := do
  let props := W.rprops.map (·.1)
  let K := OWLFrontend.ckMemo (OWLFrontend.ckOf W OWLFrontend.ckFuel) props
  let rtStr : SRI.RoleT (Fin W.M) → String := fun R => match R with
    | .pos r => s!"+{r.val}"
    | .inv r => s!"-{r.val}"
  out.putStrLn ("{\"role_rows\":{\"route\":" ++ (if W.chainR then "\"chain\"" else "\"other\"") ++
    ",\"flat\":" ++ toString (W.chainR && W.flat) ++ ",\"properties\":" ++ toString props.length ++ "}}")
  out.putStrLn ("{\"properties\":[" ++ ",".intercalate (W.rprops.map fun (r, R) =>
    "[" ++ (Json.str (propName r)).compress ++ "," ++ (Json.str (rtStr R)).compress ++ "]") ++ "]}")
  -- the elements of the individuals, read as `refute` reads them (`ckInd`)
  let indEls : List (Fin W.k) := (W.inds.filter (showInd ·.1)).filterMap fun p => K.ind p.1
  let elems := (OWLFrontend.dedupH indEls).reverse
  let elemSet : Std.HashSet Nat := elems.foldl (fun st w => st.insert w.val) {}
  -- `ObjectPropertyAssertion(P a b)` refuted: P exact at `a`'s element and
  -- `b`'s element not listed; `NegativeObjectPropertyAssertion(P a b)`
  -- refuted: listed
  let exact := props.filter fun p => elems.all fun w => (K.succ p w).2
  let mut edges : Array String := #[]
  for w in elems do
    let per : List (Nat × OWL.ObjProp) := props.flatMap fun p =>
      ((K.succ p w).1.filter fun v => elemSet.contains v.val).map fun v => (v.val, p)
    let tgt : Std.HashMap Nat (List String) :=
      per.foldl (fun mp e => mp.insert e.1 (propName e.2 :: mp.getD e.1 [])) {}
    for (v, ps) in tgt.toList do
      edges := edges.push ("[" ++ toString w.val ++ "," ++ toString v ++ "," ++ jsonList ps.reverse ++ "]")
  out.putStrLn ("{\"individual_edges_all\":[" ++ ",".intercalate edges.toList ++
    "],\"exact_properties\":" ++ jsonList (exact.map propName) ++ "}")
  if propRows then
    let named := props.filter fun p => match p with | .named _ => true | _ => false
    let clsI := (OWLFrontend.dedupH (W.cls.map (·.1))).reverse
    for p in named do
      let others := named.filter (· != p)
      let nonsub := (others ++ [OWL.ObjProp.top]).filter fun t => OWLFrontend.refute K (.subObjectPropertyOf [p] t)
      let noneq := others.filter fun t => OWLFrontend.refute K (.equivalentObjectProperties [p, t])
      let nondis := (others ++ [OWL.ObjProp.top]).filter fun t => OWLFrontend.refute K (.disjointObjectProperties [p, t])
      let chars : List (String × OWL.Axiom) := [("functional", .functional p),
        ("inverseFunctional", .inverseFunctional p), ("symmetric", .symmetric p),
        ("asymmetric", .asymmetric p), ("reflexive", .reflexive p), ("irreflexive", .irreflexive p),
        ("transitive", .transitive p)]
      let notE := (chars.filter fun c => OWLFrontend.refute K c.2).map (·.1)
      let nonempty := OWLFrontend.refute K (.subObjectPropertyOf [p] .bot)
      let domNot := clsI.filter fun C => OWLFrontend.refute K (.domain p (.cls C))
      let ranNot := clsI.filter fun C => OWLFrontend.refute K (.range p (.cls C))
      out.putStrLn ("{\"property\":" ++ (Json.str (propName p)).compress ++ ",\"nonempty\":" ++
        toString nonempty ++ ",\"nonsub\":" ++ jsonList (nonsub.map propName) ++
        ",\"nonequiv\":" ++ jsonList (noneq.map propName) ++
        ",\"nondisjoint\":" ++ jsonList (nondis.map propName) ++
        ",\"not_entailed\":" ++ jsonList notE ++ ",\"domain_not\":" ++ jsonList domNot ++
        ",\"range_not\":" ++ jsonList ranNot ++ "}")
  if dataRows then
    match KD with
    | some KD => publishData out W KD elems (dedupS W.dpsA.toList) dOn
    | none => out.putStrLn "{\"data_rows\":{\"data\":false,\"properties\":0,\"given\":0}}"
  -- with the data table (an ontology), `refuteD` (`hintRefuteDMM_sound`);
  -- with keys and rules, `refute` (`hintRefuteMR_sound`)
  let mut i := 0
  for ax in axs do
    let r := match KD with
      | some KD => OWLFrontend.refuteD KD ax
      | none => OWLFrontend.refute K ax
    out.putStrLn ("{\"axiom\":" ++ toString i ++ ",\"kind\":" ++ (Json.str (axKind ax)).compress ++
      ",\"refuted\":" ++ toString r ++ "}")
    i := i + 1

/-- The array is strictly increasing. -/
def incA (a : Array Nat) : Bool := Id.run do
  let mut ok := true
  for i in [1:a.size] do
    if a[i-1]! ≥ a[i]! then ok := false
  return ok

/-- Print the rows the witness hint certifies (`hintWitnessC_sound`: rows
between the class expressions of the requested IRIs; `owl:Thing` and
`owl:Nothing`, when requested, with their OWL meaning:
`not_entails_nothing_of_consistent`, `not_thing_sub_nothing_of_consistent`). -/
def publishWitness (out : IO.FS.Stream) (table : List (OWL.IRI × Nat)) (thingReq nothingReq : Bool)
    {O : OWL.Ontology} {R : OWL.OntologyR} (showInd : OWL.IRI → Bool := fun _ => true)
    {req : List OWL.IRI} {hint : RawHint} (W : OWLFrontend.WTab)
    (_h : OWLFrontend.wTabA O req hint = some W ∨ OWLFrontend.wTabR R req hint = some W)
    (propRows : Bool := false) (axs : List OWL.Axiom := []) (countsOnly compact : Bool := false)
    (parseMs : Nat := 0) (KD : Option (OWLFrontend.CKX W.k) := none) (dataRows : Bool := false)
    (dOn : Bool := false) :
    IO UInt32 := do
  let thingI := OWL.Parse.owlThing
  let nothingI := OWL.Parse.owlNothing
  let cix : Std.HashMap OWL.IRI (Fin W.N) := W.cls.foldl (fun mp p => mp.insertIfNew p.1 p.2) {}
  let nreq := W.cls.length + (if thingReq then 1 else 0) + (if nothingReq then 1 else 0)
  -- the requested classes by concept index (a type is short, the class list long)
  let byIx : Std.HashMap Nat (List OWL.IRI) := W.cls.foldl (fun mp p => mp.insert p.2.val (p.1 :: mp.getD p.2.val [])) {}
  -- the requested classes an element is in: those in its type, and owl:Thing
  -- the sorted type of each core element, from the hint's `ty` lines (printing
  -- only: `W.ty w` is the set of these indices; stage H4, no sort per query)
  let tyRaw : Array (List Nat) := hint.ty.foldl (fun A e =>
    if e.1 < W.k then A.modify e.1 (e.2 ++ ·) else A) (Array.replicate W.k [])
  let tyL : Array (List (Fin W.N)) := tyRaw.map fun l =>
    -- a strictly increasing `ty` line needs no sort (the producers write them so)
    let a0 := l.toArray
    let a := if incA a0 then a0 else a0.qsort (· < ·)
    let d := a.toList.foldr (fun x acc => match acc with
      | y :: _ => if x == y then acc else x :: acc
      | [] => [x]) []
    d.filterMap fun x => if h : x < W.N then some ⟨x, h⟩ else none
  let sortedTy := fun (w : Fin W.k) => tyL[w.val]?.getD []
  let insideOfL := fun (l : List (Fin W.N)) =>
    (if thingReq then [thingI] else []) ++ l.flatMap fun x => byIx.getD x.val []
  -- the requested classes an element is not in: those outside its type, and owl:Nothing
  let outsideOf := fun (M : Fin W.N → Bool) =>
    (W.cls.filter fun p => !M p.2).map (·.1) ++ (if nothingReq then [nothingI] else [])
  let mut nNon := 0
  let mut nBad := 0
  let mut nType := 0
  out.putStrLn ("{\"format\":\"owl-witness-v1\",\"consistent\":true,\"classes\":" ++ toString nreq ++
    ",\"individuals\":" ++ toString (W.inds.filter (showInd ·.1)).length ++ ",\"core\":" ++ toString W.k ++ "}")
  -- `--counts-only`: no class or individual lines; `--compact`: classes by
  -- their position in the `class_index` line (stage H4)
  let emit : (Unit → String) → IO Unit := fun l => if countsOnly then pure () else out.putStrLn (l ())
  let cnames : List OWL.IRI := (if thingReq then [thingI] else []) ++ (OWLFrontend.dedupH (W.cls.map (·.1))).reverse ++
    (if nothingReq then [nothingI] else [])
  let cpos : Std.HashMap OWL.IRI Nat := cnames.zipIdx.foldl (fun mp e => mp.insertIfNew e.1 e.2) {}
  let nm : OWL.IRI → String := fun A =>
    if compact then (match cpos.get? A with | some i => toString i | none => (Json.str A).compress)
    else (Json.str A).compress
  let jl : List OWL.IRI → String := fun l => if compact then "[" ++ ",".intercalate (l.map nm) ++ "]" else jsonList l
  if compact && !countsOnly then out.putStrLn ("{\"class_index\":" ++ jsonList cnames ++ "}")
  -- owl:Thing as subject: every requested B some core element lacks
  if thingReq then
    let cnt : Array Nat := (List.finRange W.k).foldl (fun A w =>
      (sortedTy w).foldl (fun A x => A.modify x.val (· + 1)) A) (Array.replicate W.N 0)
    let outside := (W.cls.filter fun p => cnt[p.2.val]! < W.k).map (·.1) ++
      (if nothingReq then [nothingI] else [])
    nNon := nNon + outside.length
    emit fun _ => ("{\"class\":" ++ nm thingI ++ ",\"nonsub\":" ++ jl outside ++ "}")
  for (A, w) in table do
    if A == thingI then pure () else
    if A == nothingI then
      nBad := nBad + 1
      emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
        ",\"error\":\"owl:Nothing has no witness\"}")
    else
    match cix.get? A with
    | none =>
      nBad := nBad + 1
      emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
        ",\"error\":\"not a requested class of the translation\"}")
    | some iA =>
      if hw : w < W.k then
        let t := W.ty ⟨w, hw⟩
        -- one membership test: a scan of the type (stage H5: no hash set per witness)
        if decide (iA ∈ t) then
          let inside := insideOfL (sortedTy ⟨w, hw⟩)
          let nout := nreq - inside.length
          nNon := nNon + nout
          if nout * 2 ≤ nreq then
            -- the requested classes A shares the witness with: A ⊓ B satisfiable
            emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
              ",\"nonsub\":" ++ jl (outsideOf (SRIQN.HF.memTS t).f) ++ ",\"sat_with\":" ++
              jl ((inside.filter fun B => B != A && B != thingI)) ++ "}")
          else
            emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
              ",\"nonsub_except\":" ++ jl inside ++ "}")
        else
          nBad := nBad + 1
          emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
            ",\"error\":\"the class is not in the type of the witness\"}")
      else
        nBad := nBad + 1
        emit fun _ => ("{\"class\":" ++ nm A ++ ",\"witness\":" ++ toString w ++
          ",\"error\":\"no such core element\"}")
  -- individuals: the core element holding the nominal index
  let mut groups : Std.HashMap Nat (List OWL.IRI) := {}
  let inom : Std.HashSet Nat := W.inds.foldl (fun st p => st.insert p.2.val) {}
  let owner : Std.HashMap Nat (Fin W.k) := if W.inds.isEmpty then {} else (List.finRange W.k).foldl (fun mp w =>
    (sortedTy w).foldl (fun mp x => if inom.contains x.val then mp.insertIfNew x.val w else mp) mp) {}
  for (a, ia) in W.inds.filter (showInd ·.1) do
    match owner.get? ia.val with
    | none => pure ()
    | some w =>
      groups := groups.insert w.val (a :: groups.getD w.val [])
      let MS := SRIQN.HF.memTS (W.ty w)
      let M := MS.f
      let inside := insideOfL (sortedTy w)
      let nout := nreq - inside.length
      nType := nType + nout
      if nout * 2 ≤ nreq then
        emit fun _ => ("{\"individual\":" ++ (Json.str a).compress ++ ",\"element\":" ++ toString w.val ++
          ",\"nontype\":" ++ jl (outsideOf M) ++ "}")
      else
        emit fun _ => ("{\"individual\":" ++ (Json.str a).compress ++ ",\"element\":" ++ toString w.val ++
          ",\"nontype_except\":" ++ jl inside ++ "}")
  let gs := groups.toList.map (·.2.reverse)
  out.putStrLn ("{\"nonsame_groups\":[" ++ ",".intercalate (gs.map jsonList) ++ "]}")
  -- `hintWitnessMore_sound`: individuals in one group are not entailed
  -- different; for a listed simple property r and individuals a, b on
  -- different elements, r(a, b) is not entailed unless r is in the label
  -- between their elements (the labels between individual elements follow)
  let rtStr : SRI.RoleT (Fin W.M) → String := fun R => match R with
    | .pos r => s!"+{r.val}"
    | .inv r => s!"-{r.val}"
  let propStr : OWL.ObjProp → String := fun r => match r with
    | .named i => i
    | .inv i => "^" ++ i
    | _ => ""
  out.putStrLn ("{\"simple_properties\":[" ++ ",".intercalate (W.props.map fun (r, R) =>
    "[" ++ (Json.str (propStr r)).compress ++ "," ++ (Json.str (rtStr R)).compress ++ "]") ++ "]}")
  let elems := (groups.toList.map (·.1)).filterMap fun i => if h : i < W.k then some (⟨i, h⟩ : Fin W.k) else none
  let edges := elems.flatMap fun w => elems.filterMap fun v =>
    if w.val ≠ v.val then
      let L := W.lab w v
      if L = ∅ then none else
        some ("[" ++ toString w.val ++ "," ++ toString v.val ++ "," ++
          jsonList ((W.props.filter fun p => decide (p.2 ∈ L)).map fun p => propStr p.1) ++ "]")
    else none
  out.putStrLn ("{\"individual_edges\":[" ++ ",".intercalate edges ++ "]}")
  out.putStrLn ("{\"counts\":{\"nonsub\":" ++ toString nNon ++ ",\"nontype\":" ++ toString nType ++
    ",\"table_errors\":" ++ toString nBad ++ ",\"element_groups\":" ++ toString gs.length ++
    (if parseMs > 0 then ",\"hint_parse_ms\":" ++ toString parseMs else "") ++ "}}")
  publishRoles out W (fun a => showInd a) propRows axs KD dataRows dOn
  out.flush
  return 0

/-- The witness route's target (`OWLFrontend.wCoreA`): datatype definitions
unfolded, the strengthening, disjoint unions, anonymous individuals
renamed; then the route with `ObjectHasSelf`, the chain route, or the Self
route. `kC` gets the chain route's translation, `kS` the Self route's
(the ontology `Y` it translates and the requested names `rq`). -/
def withWitnessTarget (O : OWL.Ontology) (req : List OWL.IRI)
    (kC : (T : SRIQDKBTranslation) → (L : List OWL.IRI) →
      List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)) → OWL.Ontology → IO UInt32)
    (kS : (T : SRIQDKBTranslation) → (L : List OWL.IRI) →
      List (SRIQ.Clause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)) →
      List (SRIQN.SClause (Fin T.obj.conceptCount) (Fin T.obj.roleCount)) →
      OWL.Ontology → List OWL.IRI → IO UInt32) : IO UInt32 := do
  match OWLFrontend.wDT O with
  | none => decline "witness route: a DatatypeDefinition of a datatype of the map, a recursive definition, or two definitions of one datatype"
  | some O1 =>
  let Pre := duOff (OWLFrontend.edgeP O1)
  if !(Pre.noKey && (anonOff [] Pre).noKey) then
    return ← decline "witness route: HasKey (keys and rules take the rules path)"
  let X := anonOff [] Pre
  let selfRoute (Y : OWL.Ontology) (P : List (OWL.IRI × OWL.ObjProp)) : IO UInt32 :=
    if !Y.isSROIQDSKB then decline ("witness route: " ++ hintDecline X) else
    let rq := req ++ pairNames P
    match translateSHOIQD (roleOff (selfOff Y)) rq with
    | none => decline ("witness route: " ++ hintDecline X)
    | some T =>
      match roleCls T (selfOff Y), selfCls T Y, pairCls T P with
      | some E, some SC, some PC =>
        let L := OWLFrontend.SHOIQ.nomNames (roleOff (selfOff Y)) rq
        if sroiqSHOK T L E (SC ++ PC) then kS T L E (SC ++ PC) Y rq
        else decline ("witness route: " ++ hintDecline X)
      | _, _, _ => decline ("witness route: " ++ hintDecline X)
  if !(selfPairs X).isEmpty then return ← selfRoute (hsOff X) (selfPairs X)
  let chain : Option (IO UInt32) :=
    if X.isSROIQDKB then
      match translateSHOIQD (roleOff X) req with
      | none => none
      | some T =>
        match roleCls T X with
        | none => none
        | some E =>
          let L := OWLFrontend.SHOIQ.nomNames (roleOff X) req
          if sroiqHOK T L E then some (kC T L E X) else none
    else none
  match chain with
  | some act => act
  | none => selfRoute X []

/-- The requested classes: `--classes FILE`, or every class of the ontology. -/
def witnessReq (args : Args) (O : OWL.Ontology) : IO (List OWL.IRI) := do
  match args.classes with
  | some f => pure (wordsOf (← IO.FS.readFile f))
  | none => pure O.classNames

/-- The index of the hint space of an encoded ontology. -/
def conceptsOf {n m p q : Nat} (D : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)) : Nat :=
  n + SRIQN.Proc.encKD D

/-- `--print-index --witness-route`: the index of the witness route. -/
def printIndexW (O : OWL.Ontology) (req : List OWL.IRI) : IO UInt32 := do
  let out ← IO.getStdout
  let emitT (T : SRIQDKBTranslation) (N : Nat) (Y : OWL.Ontology) (rq : List OWL.IRI) : IO UInt32 := do
    out.putStrLn s!"concepts {N}"
    out.putStrLn s!"roles {T.obj.roleCount}"
    for l in indexLines T.obj do out.putStrLn l
    let nmap := nameIxMap T.obj.named
    for l in nomLines nmap Y rq do out.putStrLn l
    out.flush
    return 0
  withWitnessTarget O req
    (fun T L E X => emitT T (conceptsOf (encC T L E)) (roleOff X) req)
    (fun T L E SC Y rq => emitT T (conceptsOf (encS T L E SC)) (roleOff (selfOff Y)) rq)

/-- `--check --witness-route`: the scope of the witness route without a
hint (diagnostic: the conditions `wTabA` checks before the hint). -/
def checkW (O : OWL.Ontology) (req : List OWL.IRI) : IO UInt32 :=
  withWitnessTarget O req (fun _ _ _ _ => do IO.println "accepted chain"; return 0)
    (fun _ _ _ _ _ _ => do IO.println "accepted self"; return 0)

/-- `--print-clauses --witness-route`. -/
def printClausesW (O : OWL.Ontology) (req : List OWL.IRI) : IO UInt32 :=
  withWitnessTarget O req
    (fun T L E _ => do
      let c ← emitClauses (encC T L E)
      emitData T L E
      return c)
    (fun T L E SC _ _ => emitClauses (encS T L E SC))

/-- The list without repeated entries, first occurrences kept. -/
def dedupH (l : List OWL.IRI) : List OWL.IRI :=
  (l.foldl (fun (acc : Std.HashSet OWL.IRI × Array OWL.IRI) a =>
    if acc.1.contains a then acc else (acc.1.insert a, acc.2.push a)) ({}, #[])).2.toList

/-- The numbers of `[i, e)`: decimal digits separated by blanks, tabs and
carriage returns, up to a `#`; `none` at any other byte. Tail recursive. -/
def numsB (bs : ByteArray) (e : Nat) (i cur : Nat) (inNum : Bool) (acc : Array Nat) :
    Option (Array Nat) :=
  if h : i < e then
    let c := bs[i]!
    if 48 ≤ c && c ≤ 57 then numsB bs e (i + 1) (cur * 10 + (c - 48).toNat) true acc
    else if c == 32 || c == 9 || c == 13 then
      numsB bs e (i + 1) 0 false (if inNum then acc.push cur else acc)
    else if c == 35 then some (if inNum then acc.push cur else acc)
    else none
  else some (if inNum then acc.push cur else acc)
termination_by e - i

/-- A `ty B C ...` line read from the bytes `[s, e)` without building
strings (stage H5): `some (B, [C ...])` when the line is `ty` followed by
decimal numbers (blanks, tabs and carriage returns between them, an
optional `#` comment); `none` otherwise (the line then goes through
`RawHint.parseLine`, with the same result as before). -/
def tyLineB (bs : ByteArray) (s e : Nat) : Option (Nat × List Nat) :=
  if s + 2 < e && bs[s]! == 116 && bs[s+1]! == 121 && (bs[s+2]! == 32 || bs[s+2]! == 9) then
    match numsB bs e (s + 2) 0 false #[] with
    | some nums => if h : 0 < nums.size then some (nums[0], (nums.extract 1 nums.size).toList) else none
    | none => none
  else none

/-- The end of the line starting at `i`. -/
def lineEnd (bs : ByteArray) (i : Nat) : Nat :=
  if h : i < bs.size then (if bs[i]! == 10 then i else lineEnd bs (i + 1)) else i
termination_by bs.size - i

/-- The lines from `s` on. -/
def linesB (bs : ByteArray) (s : Nat) (h : RawHint) : Except String RawHint :=
  if hs : s < bs.size then
    let e := lineEnd bs s
    let h' : Except String RawHint :=
      if s < e then
        match tyLineB bs s e with
        | some (b, cs) => .ok { h with ty := (b, cs) :: h.ty }
        | none =>
          let line := String.fromUTF8! (bs.extract s e)
          let body := (line.splitOn "#").headD ""
          let ws := ((body.split fun c => c == ' ' || c == '\t' || c == '\r').toList.map
            (·.toString)).filter (· ≠ "")
          RawHint.parseLine h ws
      else .ok h
    match h' with
    | .ok h' => if e + 1 > s then linesB bs (e + 1) h' else .ok h'
    | .error err => .error err
  else .ok h
termination_by bs.size - s
decreasing_by all_goals omega

/-- The text format read from bytes (stage H5): `ty` lines by `tyLineB`,
every other line by `RawHint.parseLine`, as `RawHint.parseHint` reads the
text. -/
def parseHintBytes (bs : ByteArray) : Except String RawHint :=
  (linesB bs 0 {}).map RawHint.inOrder

/-- `--procedure sroiq-hint --witness TABLE --hint FILE [--out FILE] [--classes FILE]`. -/
def runWitness (timing : Bool) (args : Args) (O : OWL.Ontology) (R? : Option OWL.OntologyR := none) :
    IO UInt32 := do
  let some tf := args.witness | return 2
  let some hf := args.hint
    | IO.eprintln "sroiq-hint: --witness needs --hint FILE"; return 2
  let tP ← IO.monoNanosNow
  let hint ← match parseHintBytes (← IO.FS.readBinFile hf) with
    | .ok h => pure h
    | .error e => IO.eprintln s!"bad hint {hf}: {e}"; return 2
  let parseMs := ((← IO.monoNanosNow) - tP) / 1000000 + 1
  let table ← match parseWitness (← IO.FS.readFile tf) with
    | .ok t => pure t
    | .error e => IO.eprintln e; return 2
  let axs ← match args.axioms with
    | none => pure []
    | some f =>
      match OWL.parse (← IO.FS.readFile f) with
      | .ok A => pure A.axioms
      | .error e => IO.eprintln s!"bad axioms {f}: {e}"; return 2
  let req0 := dedupH (← witnessReq args O)
  let thingReq := req0.contains OWL.Parse.owlThing
  let nothingReq := req0.contains OWL.Parse.owlNothing
  -- owl:Thing and owl:Nothing are not class names of the translation (`wReq`)
  let req := OWLFrontend.wReq req0
  -- `hintWitnessA_sound` (an ontology) or `hintWitnessR_sound` (keys and rules)
  let outS ← match args.out with
    | some f => do let hdl ← IO.FS.Handle.mk f .write; pure (IO.FS.Stream.ofHandle hdl)
    | none => IO.getStdout
  let done : Option UInt32 ← match R? with
    | none =>
      let ⟨res, hres⟩ ← timedPhase timing "witness" (fun _ => OWLFrontend.wTabA O req hint)
      match res, hres with
      | some W, h =>
        -- the data table of `hintRefuteDMM_sound`
        let KD := OWLFrontend.ckxMemo (OWLFrontend.ckOfDM W OWLFrontend.ckFuel (splitDef O.axioms).isNone
          (W.rprops.map (·.1))) ((dedupS W.dpsA.toList).map OWL.DataProp.named)
        some <$> (publishWitness (O := O) (R := ⟨O, []⟩) (showInd := fun _ => true) outS table thingReq nothingReq W
          (Or.inl h.symm) args.propertyRows axs args.countsOnly args.compact (if args.out.isSome then parseMs else 0)
          (some KD) args.dataPropertyRows (W.chainR && (splitDef O.axioms).isNone))
      | none, _ => pure none
    | some R =>
      let ⟨res, hres⟩ ← timedPhase timing "witness" (fun _ => OWLFrontend.wTabR R req hint)
      match res, hres with
      | some W, h =>
        -- the individuals of the input: not the fresh individual of the grounding
        let names := Std.HashSet.ofList R.named
        some <$> (publishWitness (O := O) (R := R) (showInd := names.contains) outS table thingReq
          nothingReq W (Or.inr h.symm) args.propertyRows axs args.countsOnly args.compact (if args.out.isSome then parseMs else 0)
          none args.dataPropertyRows)
      | none, _ => pure none
  match done with
  | some c => return c
  | none =>
    if args.explain then
      let _ ← withWitnessTarget O req
        (fun T L E _ => do
          let (sz, G) := splitSizes T L E (sroiqBound T L E)
          let sp := SHIQD.spec T.tab
          let as := OWL.Datatypes.allBases sp
          let cs := OWL.Datatypes.cellsOf as
          let why := (partWhy hint sz G).orElse fun _ => starWhyD (encC T L E) cs (OWL.Datatypes.cellSize as)
            (ContextCalculus.SRIQD.splitCell cs (OWL.Datatypes.cellSize as) (sroiqBound T L E) (OWL.Datatypes.owlE sp))
            (OWL.Datatypes.owlE sp) hint
          IO.eprintln s!"hint: reason: {explainOn (encC T L E) hint false why}"
          return 0)
        (fun T L E SC _ _ => do
          IO.eprintln s!"hint: reason: {explainOn (encS T L E SC) hint true}"
          return 0)
    decline ("witness: not certified (outside the chain route, keys, datatype definitions, " ++
      "ObjectHasSelf, or the hint does not check)")

/-- The hint route on a parsed ontology. -/
def runHint (timing : Bool) (args : Args) (O : OWL.Ontology) : IO UInt32 := do
  if args.witness.isSome then return ← runWitness timing args O
  if args.witnessRoute then
    let req := OWLFrontend.wReq (dedupH (← witnessReq args O))
    if args.printIndex then return ← printIndexW O req
    if args.printClauses then return ← printClausesW O req
    if args.checkOnly then return ← checkW O req
  -- asymmetric and disjoint properties: the hint is checked against the
  -- strengthening `edgeOff O`, whose certified rows are rows of `O`
  -- (`model_of_edgeOff`, `holds_of_models`, `hintRowAnsE_sound`)
  let O := if hasEdgeAx O then edgeOff O else O
  let rowWs ← match args.rowFile with
    | some f => pure (wordsOf (← IO.FS.readFile f))
    | none => pure ((args.row.map wordsOf).getD [])
  if args.printIndex then return ← printIndexHint O rowWs
  if args.printClauses then return ← printClausesHint O rowWs
  if args.checkOnly then return ← checkHint O rowWs
  match args.batch with
  | some f =>
    let text ← if f == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else IO.FS.readFile f
    match parseBatch text with
    | .error e => IO.eprintln e; return 2
    | .ok pairs => runHintBatch timing O pairs args.explain
  | none =>
    match args.hint with
    | none => IO.eprintln "sroiq-hint: --hint FILE or --batch FILE is required"; return 2
    | some f =>
      match RawHint.parseHint (← IO.FS.readFile f) with
      | .error e => IO.eprintln s!"bad hint {f}: {e}"; return 2
      | .ok hint => runHintOne timing O rowWs hint args.explain


/-! ### DL-safe rules (stage C5, item 3) -/

/-- The text with its rules, when `OWL.parse` rejected it for a rule. -/
def parseRules? (text reason : String) : Option (Except String OWL.OntologyR) :=
  if (reason.splitOn "DLSafeRule").length > 1 then some (OWL.parseR text) else none

def rulesDeclineR (R0 : OWL.OntologyR) : String :=
  match (if R0.onto.noKey then some R0 else keyOff R0) with
  | none => "keys: a HasKey with data properties"
  | some R =>
  let N := R.named.eraseDups
  let k := (R.rules.map fun ρ => N.length ^ ρ.ivars.eraseDups.length).sum
  if k > ruleCap then s!"rules: {k} ground instances over {N.length} named individuals (more than {ruleCap})"
  else "rules: an instance with a data variable, a data range atom, a built-in atom or an " ++
    "anonymous individual"

/-- Print the verdict of `owlKeysC2a` (`owlKeysC2a_sound`: consistency of
the ontology with its DL-safe rules, for every reading of the built-ins). -/
def publishConsistentR (v : Bool) {O : OWL.OntologyR} {hint : Option RawHint}
    (_h : owlKeysC2a O hint = some v) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn ("{\"format\":\"owl-consistency-v1\",\"consistent\":" ++
    (if v then "true" else "false") ++ "}")
  out.flush
  return 0

/-- The fragment checks of `sroiq-c2a` on an ontology. -/
def checkC2a (O : OWL.Ontology) : IO UInt32 := do
  let O := duOff ((dtUnfold O).getD O)
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

/-- Print a certified consistency of an ontology with rules
(`owlKeysHint_sound`). -/
def publishHintRules {O : OWL.OntologyR} {hint : RawHint}
    (_h : owlKeysHint O hint = some true) : IO UInt32 := do
  let out ← IO.getStdout
  out.putStrLn "{\"format\":\"owl-hint-v1\",\"row\":\"consistent\",\"certified\":true}"
  out.flush
  return 0

/-- The hint route on an ontology with rules: the consistency row only; the
indices and checks are those of the encoding (`rulesOnto`). -/
def runHintRules (timing : Bool) (args : Args) (R : OWL.OntologyR) : IO UInt32 := do
  if args.witness.isSome || args.witnessRoute then
    match rulesOntoK R with
    | none => return ← decline (rulesDeclineR R)
    | some O' =>
      if args.witness.isSome then return ← runWitness timing args O' (some R)
      let req := OWLFrontend.wReq (dedupH (← witnessReq args R.onto))
      if args.printIndex then return ← printIndexW O' req
      if args.printClauses then return ← printClausesW O' req
      if args.checkOnly then return ← checkW O' req
  let rowWs := (args.row.map wordsOf).getD []
  if !(rowWs.isEmpty || rowWs == ["consistent"]) then
    return ← decline "rules: rows over an ontology with rules or keys are not done"
  match rulesOntoK R with
  | none => decline (rulesDeclineR R)
  | some O' =>
    -- `owlKeysHint R h` is `owlHintConsistent O' h`; with asymmetric or disjoint
    -- properties the strengthening `edgeOff O'` (`model_of_edgeOff`)
    let O' := if hasEdgeAx O' then edgeOff O' else O'
    if args.printIndex then return ← printIndexHint O' []
    if args.printClauses then return ← printClausesHint O' []
    if args.checkOnly then return ← checkHint O' []
    match args.batch with
    | some f =>
      let text ← if f == "-" then (do let stdin ← IO.getStdin; stdin.readToEnd) else IO.FS.readFile f
      match parseBatch text with
      | .error e => IO.eprintln e; return 2
      | .ok pairs =>
        let out ← IO.getStdout
        let idx := (List.range pairs.length).zip pairs
        let mine := idx.filter fun p => p.2.1.isEmpty || p.2.1 == ["consistent"]
        -- `owlKeysHint R h = (rulesOntoK R).bind (owlHintConsistent · h)`, and
        -- `hintPB O' hs = hs.map (hintP O')` (`hintPB_eq`)
        let ⟨rs, _⟩ ← timedPhase timing "hint-batch" (fun _ => hintPB O' (mine.map (·.2.2)))
        let res : Std.HashMap Nat String := (mine.zip rs).foldl (fun m (p, v) =>
          m.insert p.1 (match v with
            | some true => "\"certified\""
            | some false => "\"rejected\""
            | none => "\"declined\"")) {}
        for (i, (rw, _)) in idx do
          let t := res.getD i "\"declined\",\"reason\":\"rows over an ontology with rules are not done\""
          out.putStrLn ("{\"format\":\"owl-hint-batch-v1\",\"pair\":" ++ toString i ++ ",\"row\":" ++
            (Json.str (rowText rw)).compress ++ ",\"result\":" ++ t ++ "}")
        out.flush
        return 0
    | none =>
      match args.hint with
      | none => IO.eprintln "sroiq-hint: --hint FILE or --batch FILE is required"; return 2
      | some f =>
        match RawHint.parseHint (← IO.FS.readFile f) with
        | .error e => IO.eprintln s!"bad hint {f}: {e}"; return 2
        | .ok hint =>
          let ⟨res, hres⟩ ← timedPhase timing "hint" (fun _ => owlKeysHint R hint)
          match res, hres with
          | some true, h => publishHintRules h.symm
          | _, _ =>
            -- with asymmetric or disjoint properties: `owlHintConsistent_sound` on
            -- `edgeOff O'`, then `model_of_edgeOff` and `consistentAtR_rulesOntoK`
            if owlHintConsistent O' hint == some true then do
              IO.println "{\"format\":\"owl-hint-v1\",\"row\":\"consistent\",\"certified\":true}"
              return 0
            else decline "hint: rejected (an index outside the translation, or the check fails)"

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
  -- `--type owl:Thing a`: the type routes read the class IRI as a free name,
  -- while owl:Thing(a) always holds; refused (owl:Nothing keeps its meaning:
  -- a free name holds at a exactly when the ontology is inconsistent)
  if let some (C, _) := args.query then
    if C == OWL.Parse.owlThing then
      IO.eprintln "--type: owl:Thing(a) is entailed by every ontology; the query is refused"
      return 2
  let timing ← timingEnabled
  let t0 ← IO.monoNanosNow
  -- the witness row reads its hint itself (`runWitness`), so it is not parsed twice
  match ← readHint (if args.witness.isSome then none else args.hint) with
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
    let run : IO UInt32 := if args.dataRoute == some "sroiq-hint" then do
        let ⟨parsed, _⟩ ← timedPhase timing "parse" (fun _ => OWL.parse text)
        match parsed with
        | .error reason =>
          match parseRules? text reason with
          | none => decline s!"parse rejected: {reason}"
          | some (.error e) => decline s!"parse rejected: {e}"
          | some (.ok R) => runHintRules timing args R
        | .ok O => if O.noKey then runHint timing args O else runHintRules timing args ⟨O, []⟩
      else if args.checkOnly then do
        match OWL.parse text with
        | .error reason =>
          if args.dataRoute == some "sroiq-c2a" then
            match parseRules? text reason with
            | none => decline s!"parse rejected: {reason}"
            | some (.error e) => decline s!"parse rejected: {e}"
            | some (.ok R) =>
              match rulesOntoK R with
              | none => decline (rulesDeclineR R)
              | some O' => checkC2a O'
          else decline s!"parse rejected: {reason}"
        | .ok O =>
          if args.dataRoute == some "sroiq-c2a" then
            if O.noKey then checkC2a O
            else
              let R : OWL.OntologyR := ⟨O, []⟩
              match rulesOntoK R with
              | none => decline (rulesDeclineR R)
              | some O' => checkC2a O'
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
        | .error reason =>
          match route == "sroiq-c2a", parseRules? text reason with
          | true, some (.ok R) =>
            if args.query.isSome then decline "rules: rows over an ontology with rules or keys are not done"
            else
              let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlKeysC2a R hint)
              match res, hres with
              | some v, h => publishConsistentR v h.symm
              | none, _ => decline (rulesDeclineR R)
          | true, some (.error e) => decline s!"parse rejected: {e}"
          | _, _ => decline s!"parse rejected: {reason}"
        | .ok O =>
          if route == "sroiq-c2a" && !O.noKey && args.query.isNone then
            let R : OWL.OntologyR := ⟨O, []⟩
            let ⟨res, hres⟩ ← timedPhase timing "consistency" (fun _ => owlKeysC2a R hint)
            match res, hres with
            | some v, h => publishConsistentR v h.symm
            | none, _ => decline (rulesDeclineR R)
          else runOntologyD timing route hint args.query O
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
  let usage := "usage: km-owl-reference [--procedure el|sri|el-then-sri|sriq|el-then-sriq|alc|el-then-alc|sriq-kb|sriqd|sriqd-kb|shoiq-c2a|sroiq-c2a|sroiq-hint] [--hint FILE] [--batch FILE] [--row ROW] [--check] [--type CLASS INDIVIDUAL] [--print-index] <file.ofn> (default el-then-sri; --hint, --type and --print-index with sriq-kb, sriqd-kb and shoiq-c2a only)"
  match KMOWLReferenceCheck.parseArgs {} args with
  | some a =>
    match a.path with
    | some path =>
      if (a.hint.isSome || a.query.isSome || a.printIndex || a.checkOnly || a.row.isSome ||
          a.batch.isSome || a.rowFile.isSome || a.explain || a.witness.isSome || a.witnessRoute) &&
          !((a.procedure == .sriqKB && a.dataRoute.isNone) || a.dataRoute == some "sriqd-kb" ||
            a.dataRoute == some "shoiq-c2a" || a.dataRoute == some "sroiq-c2a" ||
            a.dataRoute == some "sroiq-hint") then
        IO.eprintln usage
        return 2
      else KMOWLReferenceCheck.runFile a path
    | none =>
      IO.eprintln usage
      return 2
  | none =>
    IO.eprintln usage
    return 2
