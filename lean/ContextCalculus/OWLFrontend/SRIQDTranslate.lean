import ContextCalculus.OWLFrontend.SRIQModels
import ContextCalculus.OWLFrontend.SRIQKBTranslate
import ContextCalculus.OWL.EntailsAt
import ContextCalculus.OWL.Datatypes.Oracle
import ContextCalculus.SRIQD.Transitivity

/-!
# OWL SHIQ(D) into the `SRIQD` normal clauses (v1.7.0 stage C4, part D)

The SHIQ(D) part (`OWL.Ontology.isSHIQD`) is the SHIQ part with data:
class expressions `DataSomeValuesFrom`, `DataAllValuesFrom`,
`DataHasValue`, `DataMinCardinality`, `DataMaxCardinality`,
`DataExactCardinality` over a named data property (any data range), and
the axioms `SubDataPropertyOf`, `EquivalentDataProperties`,
`DataPropertyDomain`, `DataPropertyRange`, `FunctionalDataProperty` over
named data properties. Declined: `owl:topDataProperty`,
`owl:bottomDataProperty`, `DisjointDataProperties`, `DatatypeDefinition`,
`HasKey`, assertions (the knowledge-base route is open).

`translateSRIQD O requested` works in four steps.

1. Data property axioms become class axioms (`rwAxiom`):
   `DataPropertyDomain(p C)` is `SubClassOf(∃p.rdfs:Literal C)`,
   `DataPropertyRange(p R)` is `SubClassOf(owl:Thing ∀p.R)`,
   `FunctionalDataProperty(p)` is `SubClassOf(owl:Thing ≤1 p.rdfs:Literal)`;
   `SubDataPropertyOf` and `EquivalentDataProperties` become `dSub`
   clauses.
2. Every data class expression becomes a fresh class IRI (`absC`): a
   *data expression* (`DExpr`: `∃p.R`, `∀p.R`, `≥n p.R` with `n ≥ 1`,
   `≤n p.R`) `e` at position `j` of the table `tab` (all data expressions,
   without repetitions) gets the name `F_e = defName base (2j)` and a
   complement name `W_e = defName base (2j+1)`. `DataHasValue(p l)` is
   `∃p.{l}`, `DataMinCardinality(0 ..)` is `owl:Thing`,
   `DataExactCardinality(n p R)` is `≥n p.R ⊓ ≤n p.R` (`≤0 p.R` for `n = 0`).
   The object ontology (`objOnt`) is the abstracted axioms and
   `SubClassOf(owl:Thing F_e ⊔ W_e)` for every `e`.
3. The SHIQ translation of the object ontology, with the requested IRIs and
   all fresh names requested (so that each has a concept index).
4. The data clauses on the indices of `F_e` and `W_e`: `F_e ⊑ e` and
   `W_e ⊑ ¬e` (`dataClauses`). Data atom `j` is the data range of `tab[j]`
   (`spec`), data property `u` is `dprops[u]`.

In a model, `F_e ⊑ e`, `W_e ⊑ ¬e` and `⊤ ⊑ F_e ⊔ W_e` make `F_e` exactly
`e`; conversely a model of `O` gives `F_e` the extension of `e` and `W_e`
its complement.
-/

namespace ContextCalculus.OWL

/-! ## Equality of data ranges -/

mutual
/-- Structural equality of data ranges. -/
def drBeq : DataRange → DataRange → Bool
  | .datatype a, .datatype b => a == b
  | .and rs, .and ss => drListBeq rs ss
  | .or rs, .or ss => drListBeq rs ss
  | .not r, .not s => drBeq r s
  | .oneOf ls, .oneOf ms => ls == ms
  | .restriction t fs, .restriction u gs => t == u && fs == gs
  | _, _ => false
/-- Structural equality of lists of data ranges. -/
def drListBeq : List DataRange → List DataRange → Bool
  | [], [] => true
  | r :: rs, s :: ss => drBeq r s && drListBeq rs ss
  | _, _ => false
end

mutual
theorem drBeq_eq : ∀ r s : DataRange, drBeq r s = true → r = s
  | .datatype a, .datatype b, h => by simp [drBeq] at h; rw [h]
  | .and rs, .and ss, h => by rw [drBeq] at h; rw [drListBeq_eq rs ss h]
  | .or rs, .or ss, h => by rw [drBeq] at h; rw [drListBeq_eq rs ss h]
  | .not r, .not s, h => by rw [drBeq] at h; rw [drBeq_eq r s h]
  | .oneOf ls, .oneOf ms, h => by simp [drBeq] at h; rw [h]
  | .restriction t fs, .restriction u gs, h => by simp [drBeq] at h; rw [h.1, h.2]
  | .datatype _, .and _, h | .datatype _, .or _, h | .datatype _, .not _, h
  | .datatype _, .oneOf _, h | .datatype _, .restriction .., h => by simp [drBeq] at h
  | .and _, .datatype _, h | .and _, .or _, h | .and _, .not _, h | .and _, .oneOf _, h
  | .and _, .restriction .., h => by simp [drBeq] at h
  | .or _, .datatype _, h | .or _, .and _, h | .or _, .not _, h | .or _, .oneOf _, h
  | .or _, .restriction .., h => by simp [drBeq] at h
  | .not _, .datatype _, h | .not _, .and _, h | .not _, .or _, h | .not _, .oneOf _, h
  | .not _, .restriction .., h => by simp [drBeq] at h
  | .oneOf _, .datatype _, h | .oneOf _, .and _, h | .oneOf _, .or _, h | .oneOf _, .not _, h
  | .oneOf _, .restriction .., h => by simp [drBeq] at h
  | .restriction .., .datatype _, h | .restriction .., .and _, h | .restriction .., .or _, h
  | .restriction .., .not _, h | .restriction .., .oneOf _, h => by simp [drBeq] at h
theorem drListBeq_eq : ∀ rs ss : List DataRange, drListBeq rs ss = true → rs = ss
  | [], [], _ => rfl
  | r :: rs, s :: ss, h => by
    simp only [drListBeq, Bool.and_eq_true] at h
    rw [drBeq_eq r s h.1, drListBeq_eq rs ss h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [drListBeq] at h
end

mutual
theorem drBeq_refl : ∀ r : DataRange, drBeq r r = true
  | .datatype _ => by simp [drBeq]
  | .and rs => by rw [drBeq]; exact drListBeq_refl rs
  | .or rs => by rw [drBeq]; exact drListBeq_refl rs
  | .not r => by rw [drBeq]; exact drBeq_refl r
  | .oneOf _ => by simp [drBeq]
  | .restriction _ _ => by simp [drBeq]
theorem drListBeq_refl : ∀ rs : List DataRange, drListBeq rs rs = true
  | [] => rfl
  | r :: rs => by
    simp only [drListBeq, Bool.and_eq_true]
    exact ⟨drBeq_refl r, drListBeq_refl rs⟩
end

instance : DecidableEq DataRange := fun a b =>
  if h : drBeq a b = true then isTrue (drBeq_eq a b h)
  else isFalse fun e => by subst e; exact h (drBeq_refl a)

/-! ## The SHIQ(D) part -/

/-- A named data property. -/
def DataProp.isNamed : DataProp → Bool
  | .named _ => true
  | _ => false

/-- ALCIQ class expressions with data class expressions over named data
properties. -/
def ClassExpr.isALCIQD : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCIQD
  | .not c => c.isALCIQD
  | .some r c | .all r c => r.isBasic && c.isALCIQD
  | .min _ r c | .max _ r c | .exact _ r c => r.isBasic && c.isALCIQD
  | .dataSome p _ | .dataAll p _ | .dataHasValue p _ => p.isNamed
  | .dataMin _ p _ | .dataMax _ p _ | .dataExact _ p _ => p.isNamed
  | .oneOf _ | .hasValue .. | .hasSelf _ => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- The axioms of the SHIQ(D) part. -/
def Axiom.isSHIQD : Axiom → Bool
  | .subClassOf c d => c.isALCIQD && d.isALCIQD
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCIQD
  | .domain r c | .range r c => r.isBasic && c.isALCIQD
  | .functional r | .inverseFunctional r => r.isBasic
  | .subDataPropertyOf p q => p.isNamed && q.isNamed
  | .equivalentDataProperties ps => ps.all DataProp.isNamed
  | .dataDomain p c => p.isNamed && c.isALCIQD
  | .dataRange p _ | .functionalData p => p.isNamed
  | ax => ax.isSHI

/-- The SHIQ(D) part. -/
def Ontology.isSHIQD (O : Ontology) : Bool := O.axioms.all Axiom.isSHIQD

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

namespace SHIQD

/-! ## Data expressions -/

/-- A data expression: `kind` `0` is `∃p.R`, `1` is `∀p.R`, `2` is
`≥n p.R`, `3` is `≤n p.R`. -/
structure DExpr where
  kind : Fin 4
  n : Nat
  p : IRI
  R : DataRange
deriving DecidableEq

/-- The class expression of a data expression. -/
def DExpr.toCE (e : DExpr) : ClassExpr :=
  match e.kind with
  | 0 => .dataSome (.named e.p) e.R
  | 1 => .dataAll (.named e.p) e.R
  | 2 => .dataMin e.n (.named e.p) e.R
  | _ => .dataMax e.n (.named e.p) e.R

/-- The data property IRI of a data property expression. -/
def dpIRI : DataProp → IRI
  | .named p => p
  | _ => ""

/-- The data expressions of a class expression, in order. -/
def dexprs : ClassExpr → List DExpr
  | .and cs | .or cs => cs.attach.flatMap fun ⟨c, _⟩ => dexprs c
  | .not c | .some _ c | .all _ c => dexprs c
  | .min _ _ c | .max _ _ c | .exact _ _ c => dexprs c
  | .dataSome p R => [⟨0, 0, dpIRI p, R⟩]
  | .dataAll p R => [⟨1, 0, dpIRI p, R⟩]
  | .dataHasValue p l => [⟨0, 0, dpIRI p, .oneOf [l]⟩]
  | .dataMin 0 _ _ => []
  | .dataMin (k + 1) p R => [⟨2, k + 1, dpIRI p, R⟩]
  | .dataMax k p R => [⟨3, k, dpIRI p, R⟩]
  | .dataExact 0 p R => [⟨3, 0, dpIRI p, R⟩]
  | .dataExact (k + 1) p R => [⟨2, k + 1, dpIRI p, R⟩, ⟨3, k + 1, dpIRI p, R⟩]
  | _ => []
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-- Replace every data class expression by the class IRI `nm e` of its data
expression `e`. -/
def absC (nm : DExpr → IRI) : ClassExpr → ClassExpr
  | .cls a => .cls a
  | .thing => .thing
  | .nothing => .nothing
  | .and cs => .and (cs.attach.map fun ⟨c, _⟩ => absC nm c)
  | .or cs => .or (cs.attach.map fun ⟨c, _⟩ => absC nm c)
  | .not c => .not (absC nm c)
  | .some r c => .some r (absC nm c)
  | .all r c => .all r (absC nm c)
  | .min k r c => .min k r (absC nm c)
  | .max k r c => .max k r (absC nm c)
  | .exact k r c => .exact k r (absC nm c)
  | .dataSome p R => .cls (nm ⟨0, 0, dpIRI p, R⟩)
  | .dataAll p R => .cls (nm ⟨1, 0, dpIRI p, R⟩)
  | .dataHasValue p l => .cls (nm ⟨0, 0, dpIRI p, .oneOf [l]⟩)
  | .dataMin 0 _ _ => .thing
  | .dataMin (k + 1) p R => .cls (nm ⟨2, k + 1, dpIRI p, R⟩)
  | .dataMax k p R => .cls (nm ⟨3, k, dpIRI p, R⟩)
  | .dataExact 0 p R => .cls (nm ⟨3, 0, dpIRI p, R⟩)
  | .dataExact (k + 1) p R => .and [.cls (nm ⟨2, k + 1, dpIRI p, R⟩), .cls (nm ⟨3, k + 1, dpIRI p, R⟩)]
  | .oneOf _ | .hasValue .. | .hasSelf _ => .thing
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)

/-! ## Axioms -/

/-- `rdfs:Literal` as a data range. -/
def litRange : DataRange := .datatype rdfsLiteral

/-- Data property axioms as class axioms (sub- and equivalent data
properties give none: they become `dSub` clauses). -/
def rwAxiom : Axiom → List Axiom
  | .dataDomain p c => [.subClassOf (.dataSome p litRange) c]
  | .dataRange p R => [.subClassOf .thing (.dataAll p R)]
  | .functionalData p => [.subClassOf .thing (.dataMax 1 p litRange)]
  | .subDataPropertyOf .. | .equivalentDataProperties _ => []
  | ax => [ax]

/-- The data expressions of an axiom. -/
def axDexprs : Axiom → List DExpr
  | .subClassOf c d => dexprs c ++ dexprs d
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap dexprs
  | .domain _ c | .range _ c => dexprs c
  | _ => []

/-- Abstract the class expressions of an axiom. -/
def absAx (nm : DExpr → IRI) : Axiom → Axiom
  | .subClassOf c d => .subClassOf (absC nm c) (absC nm d)
  | .equivalentClasses cs => .equivalentClasses (cs.map (absC nm))
  | .disjointClasses cs => .disjointClasses (cs.map (absC nm))
  | .domain r c => .domain r (absC nm c)
  | .range r c => .range r (absC nm c)
  | ax => ax

/-- The `dSub` pairs of the data property axioms. -/
def subPairs : Axiom → List (IRI × IRI)
  | .subDataPropertyOf p q => [(dpIRI p, dpIRI q)]
  | .equivalentDataProperties ps =>
    ps.flatMap fun p => ps.map fun q => (dpIRI p, dpIRI q)
  | _ => []

/-- The rewritten axioms. -/
def rwAxioms (O : Ontology) : List Axiom := O.axioms.flatMap rwAxiom

/-- The table of data expressions, without repetitions. -/
def table (O : Ontology) : List DExpr := ((rwAxioms O).flatMap axDexprs).dedup

/-- The data property IRIs. -/
def dprops (O : Ontology) : List IRI :=
  ((table O).map DExpr.p ++ (O.axioms.flatMap subPairs).flatMap fun pq => [pq.1, pq.2]).dedup

/-- The name of a data expression. -/
def fName (base : String) (tab : List DExpr) (e : DExpr) : IRI :=
  SRIQKB.defName base (2 * tab.idxOf e)

/-- The complement name of a data expression. -/
def wName (base : String) (tab : List DExpr) (e : DExpr) : IRI :=
  SRIQKB.defName base (2 * tab.idxOf e + 1)

/-- The object ontology. -/
def objOnt (O : Ontology) (base : String) : Ontology :=
  ⟨(rwAxioms O).map (absAx (fName base (table O))) ++
    (table O).map fun e => .subClassOf .thing
      (.or [.cls (fName base (table O) e), .cls (wName base (table O) e)])⟩

/-- The fresh names, requested so that each has a concept index. -/
def freshNames (base : String) (tab : List DExpr) : List IRI :=
  tab.flatMap fun e => [fName base tab e, wName base tab e]

/-- The data atoms: the data range of each table entry. -/
def spec (tab : List DExpr) : Fin tab.length → DataRange := fun j => tab[j].R

/-- The concept index of an IRI among the named IRIs. -/
def nameIx (T : SRIQTranslation) (a : IRI) : Option (Fin T.conceptCount) :=
  if h : T.named.idxOf a < T.named.length then
    some ⟨_, Nat.lt_of_lt_of_le h T.hnamed⟩
  else none

/-- The index of a data property IRI. -/
def dpIx (dps : List IRI) (p : IRI) : Option (Fin dps.length) :=
  if h : dps.idxOf p < dps.length then some ⟨_, h⟩ else none

abbrev DClause (n m p q : Nat) := ContextCalculus.SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q)

/-- The two data clauses of table entry `j` on the indices `F`, `W`, `u`. -/
def entryClauses {n m p q : Nat} (e : DExpr) (F W : Fin n) (u : Fin p) (j : Fin q) :
    List (DClause n m p q) :=
  match e.kind with
  | 0 => [.dEx F u [j] [], .dAll W u [(j, false)]]
  | 1 => [.dAll F u [(j, true)], .dEx W u [] [j]]
  | 2 => [.dAtLeast F e.n u [j] [], .dAtMost W (e.n - 1) u [j] []]
  | _ => [.dAtMost F e.n u [j] [], .dAtLeast W (e.n + 1) u [j] []]

/-- The data clauses of a table entry `(e, j)`. -/
def dataClauseOf (T : SRIQTranslation) (base : String) (tab : List DExpr) (dps : List IRI)
    (jt : DExpr × Nat) : Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match nameIx T (fName base tab jt.1), nameIx T (wName base tab jt.1), dpIx dps jt.1.p with
  | some F, some W, some u =>
    if h : jt.2 < tab.length then some (entryClauses (m := T.roleCount) jt.1 F W u ⟨jt.2, h⟩)
    else none
  | _, _, _ => none

/-- The `dSub` clause of a sub-property pair. -/
def subClauseOf (T : SRIQTranslation) (dps : List IRI) (tab : List DExpr) (pq : IRI × IRI) :
    Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match dpIx dps pq.1, dpIx dps pq.2 with
  | some u, some w => some [.dSub u w]
  | _, _ => none

end SHIQD

open SHIQD

/-- The result of the SHIQ(D) translation. -/
structure SRIQDTranslation where
  /-- The SHIQ translation of the object ontology. -/
  obj : SRIQTranslation
  /-- The requested IRIs, without repetitions (a prefix of `obj.named`). -/
  named : List OWL.IRI
  dps : List OWL.IRI
  tab : List DExpr
  ontology : ContextCalculus.SRIQD.Ontology (Fin obj.conceptCount) (Fin obj.roleCount)
    (Fin dps.length) (Fin tab.length)

/-- **The SHIQ(D) translation**; `none` outside the SHIQ(D) part or if an
index lookup fails (it does not on the fragment). -/
def translateSRIQD (O : OWL.Ontology) (requested : List OWL.IRI) : Option SRIQDTranslation :=
  if O.isSHIQD then
    let base := SRIQKB.defBase O requested
    let tab := table O
    let dps := dprops O
    match translateSRIQ (objOnt O base) (requested ++ freshNames base tab) with
    | none => none
    | some T =>
      let dataCl := SRIQKB.collect (dataClauseOf T base tab dps) tab.zipIdx
      let subCl := SRIQKB.collect (subClauseOf T dps tab) (O.axioms.flatMap subPairs)
      match dataCl, subCl with
      | some dc, some sc =>
        some { obj := T, named := requested.eraseDups, dps := dps, tab := tab,
               ontology := T.ontology.map .obj ++ dc ++ sc }
      | _, _ => none
  else none

end ContextCalculus.OWLFrontend
