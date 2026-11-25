import ContextCalculus.OWLFrontend.SRIQDComplete
import ContextCalculus.OWLFrontend.SRIQKBReference
import ContextCalculus.SRIQD.KBParts

/-!
# OWL SHIQ(D) knowledge bases into `SRIQD` clauses and assertions (v1.7.0 stage C4)

The SHIQ(D) knowledge-base part (`Ontology.isSHIQDKB`) is the SHIQ(D) part
with the assertions of the SHIQ knowledge-base part (class assertions over
ALCIQD class expressions, object property assertions and their negations,
same and different individuals, all over named individuals) and the data
property assertions `DataPropertyAssertion(p a l)` and
`NegativeDataPropertyAssertion(p a l)` over a named data property and a
named individual.

`translateSRIQDKB O requested extra` is `translateSRIQD` with assertions:

1. a data property assertion becomes the class assertion
   `ClassAssertion(DataHasValue(p l) a)`, its negation
   `ClassAssertion(ObjectComplementOf(DataHasValue(p l)) a)` (same
   satisfaction, `rwAxiomK`);
2. class assertions are abstracted like every other class expression
   (`absAxK`), so the data expressions of assertions join the table;
3. the SHIQ knowledge-base translation `translateSRIQKB` does the object
   part, with the fresh names requested;
4. the clauses of the table entries and the `dSub` clauses are added as in
   `translateSRIQD`; the assertions are the object assertions of
   `translateSRIQKB` (`Assertion.obj`).
-/

namespace ContextCalculus.OWL

/-- The axioms of the SHIQ(D) knowledge-base part. -/
def Axiom.isSHIQDKB : Axiom → Bool
  | .classAssertion c a => c.isALCIQD && a.isNamed
  | .objectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .negativeObjectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .sameIndividual as | .differentIndividuals as => as.all Individual.isNamed
  | .declareNamedIndividual _ => true
  | .dataPropertyAssertion p a _ | .negativeDataPropertyAssertion p a _ => p.isNamed && a.isNamed
  | ax => ax.isSHIQD

/-- The SHIQ(D) knowledge-base part. -/
def Ontology.isSHIQDKB (O : Ontology) : Bool := O.axioms.all Axiom.isSHIQDKB

end ContextCalculus.OWL

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL

namespace SHIQD

/-- Data property assertions as class assertions; the other axioms as in
`rwAxiom`. -/
def rwAxiomK : Axiom → List Axiom
  | .dataPropertyAssertion p a l => [.classAssertion (.dataHasValue p l) a]
  | .negativeDataPropertyAssertion p a l => [.classAssertion (.not (.dataHasValue p l)) a]
  | ax => rwAxiom ax

/-- The data expressions of an axiom, class assertions included. -/
def axDexprsK : Axiom → List DExpr
  | .classAssertion c _ => dexprs c
  | ax => axDexprs ax

/-- The abstraction of an axiom, class assertions included. -/
def absAxK (nm : DExpr → IRI) : Axiom → Axiom
  | .classAssertion c a => .classAssertion (absC nm c) a
  | ax => absAx nm ax

def rwAxiomsK (O : Ontology) : List Axiom := O.axioms.flatMap rwAxiomK

def tableK (O : Ontology) : List DExpr := ((rwAxiomsK O).flatMap axDexprsK).dedup

def dpropsK (O : Ontology) : List IRI :=
  ((tableK O).map DExpr.p ++ (O.axioms.flatMap subPairs).flatMap fun pq => [pq.1, pq.2]).dedup

/-- The object knowledge base. -/
def objOntK (O : Ontology) (base : String) : Ontology :=
  ⟨(rwAxiomsK O).map (absAxK (fName base (tableK O)))⟩

/-- The concept index of an IRI among the named IRIs of a knowledge-base
translation. -/
def nameIxK (T : SRIQKBTranslation) (a : IRI) : Option (Fin T.conceptCount) :=
  if h : T.named.idxOf a < T.named.length then
    some ⟨_, Nat.lt_of_lt_of_le h T.hnamed⟩
  else none

/-- The data clauses of a table entry. -/
def dataClauseOfK (T : SRIQKBTranslation) (base : String) (tab : List DExpr) (dps : List IRI)
    (jt : DExpr × Nat) : Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match nameIxK T (fName base tab jt.1), nameIxK T (wName base tab jt.1), dpIx dps jt.1.p with
  | some F, some W, some u =>
    if h : jt.2 < tab.length then some (entryClauses (m := T.roleCount) jt.1 F W u ⟨jt.2, h⟩)
    else none
  | _, _, _ => none

/-- The `dSub` clause of a sub-property pair. -/
def subClauseOfK (T : SRIQKBTranslation) (dps : List IRI) (tab : List DExpr) (pq : IRI × IRI) :
    Option (List (DClause T.conceptCount T.roleCount dps.length tab.length)) :=
  match dpIx dps pq.1, dpIx dps pq.2 with
  | some u, some w => some [.dSub u w]
  | _, _ => none

end SHIQD

open SHIQD

/-- The result of the SHIQ(D) knowledge-base translation. -/
structure SRIQDKBTranslation where
  obj : SRIQKBTranslation
  named : List OWL.IRI
  dps : List OWL.IRI
  tab : List DExpr
  ontology : ContextCalculus.SRIQD.Ontology (Fin obj.conceptCount) (Fin obj.roleCount)
    (Fin dps.length) (Fin tab.length)

/-- The assertions: the object assertions of the knowledge-base translation. -/
def SRIQDKBTranslation.abox (T : SRIQDKBTranslation) :
    ContextCalculus.SRIQD.ABox (Fin T.obj.conceptCount) (Fin T.obj.roleCount) (Fin T.dps.length)
      (Fin T.tab.length) (Fin T.obj.inds.length) :=
  T.obj.abox.map ContextCalculus.SRIQD.Assertion.obj

/-- **The SHIQ(D) knowledge-base translation.** -/
def translateSRIQDKB (O : OWL.Ontology) (requested : List OWL.IRI) (extra : List OWL.IRI := []) :
    Option SRIQDKBTranslation :=
  if O.isSHIQDKB then
    let base := SRIQKB.defBase O requested
    let tab := tableK O
    let dps := dpropsK O
    match translateSRIQKB (objOntK O base) (requested ++ freshNames base tab) extra with
    | none => none
    | some T =>
      let dataCl := SRIQKB.collect (dataClauseOfK T base tab dps) tab.zipIdx
      let subCl := SRIQKB.collect (subClauseOfK T dps tab) (O.axioms.flatMap subPairs)
      match dataCl, subCl with
      | some dc, some sc =>
        some { obj := T, named := requested.eraseDups, dps := dps, tab := tab,
               ontology := T.ontology.map .obj ++ dc ++ sc }
      | _, _ => none
  else none

end ContextCalculus.OWLFrontend
