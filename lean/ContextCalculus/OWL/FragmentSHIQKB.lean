import ContextCalculus.OWL.FragmentSHIQ

/-!
# SHIQ knowledge bases: the SHIQ part with individuals (v1.7.0 stage C1b)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`. `Ontology.isSHIQKB` is the SHIQ part
(`Ontology.isSHIQ`) with these assertion axioms:

- `ClassAssertion(C a)` with `C` an ALCIQ class expression
  (`ClassExpr.isALCIQ`);
- `ObjectPropertyAssertion(r a b)` and
  `NegativeObjectPropertyAssertion(r a b)` over a basic property (a
  property IRI or its inverse);
- `SameIndividual(a1 ... an)` and `DifferentIndividuals(a1 ... an)`;
- `Declaration(NamedIndividual(a))`.

Every individual in an assertion is a named individual. Anonymous
individuals are declined for now: their direct semantics is existential,
and the translation gives each individual an index of its own.

The simple-role restriction of OWL 2 DL for negative property assertions
(no transitive property below the asserted property or below its inverse)
is not part of this predicate; the route checks it on the translated
clauses, as it does for number restrictions.
-/

namespace ContextCalculus.OWL

/-- A named individual. -/
def Individual.isNamed : Individual → Bool
  | .named _ => true
  | .anon _ => false

/-- The axioms that the knowledge-base route reads as assertions. -/
def Axiom.isAssertion : Axiom → Bool
  | .classAssertion .. | .objectPropertyAssertion .. | .negativeObjectPropertyAssertion ..
  | .sameIndividual _ | .differentIndividuals _ | .declareNamedIndividual _ => true
  | _ => false

/-- An assertion of the SHIQ knowledge-base part, or an axiom of the SHIQ
part. -/
def Axiom.isSHIQKB : Axiom → Bool
  | .classAssertion c a => c.isALCIQ && a.isNamed
  | .objectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .negativeObjectPropertyAssertion r a b => r.isBasic && a.isNamed && b.isNamed
  | .sameIndividual as | .differentIndividuals as => as.all Individual.isNamed
  | .declareNamedIndividual _ => true
  | ax => ax.isSHIQ

def Ontology.isSHIQKB (O : Ontology) : Bool := O.axioms.all Axiom.isSHIQKB

/-- An axiom of the SHIQ knowledge-base part that is not an assertion is in
the SHIQ part. -/
theorem Axiom.isSHIQ_of_isSHIQKB {ax : Axiom} (h : ax.isSHIQKB = true)
    (hn : ax.isAssertion = false) : ax.isSHIQ = true := by
  cases ax <;> simp_all [isSHIQKB, isAssertion]

/-- The SHIQ part is part of the SHIQ knowledge-base part. -/
theorem Axiom.isSHIQKB_of_isSHIQ {ax : Axiom} (h : ax.isSHIQ = true) : ax.isSHIQKB = true := by
  cases ax <;> simp_all [isSHIQKB, isSHIQ, isSHI, isSRI]

theorem Ontology.isSHIQKB_of_isSHIQ {O : Ontology} (h : O.isSHIQ = true) : O.isSHIQKB = true := by
  simp only [isSHIQKB, isSHIQ, List.all_eq_true] at h ⊢
  exact fun ax hax => Axiom.isSHIQKB_of_isSHIQ (h ax hax)

#print axioms Axiom.isSHIQ_of_isSHIQKB
#print axioms Ontology.isSHIQKB_of_isSHIQ

end ContextCalculus.OWL
