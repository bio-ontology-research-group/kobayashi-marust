import ContextCalculus.OWL.FragmentSRI

/-!
# The SHIQ part of the frontend fragment (v1.7.0 stage C1)

`docs/V1.7.0-C1-SHIQ-DESIGN.md`, section 6. The SHIQ part is the SHI part
(`Ontology.isSHI`) with number restrictions:

- class expressions: those of `ClassExpr.isALCI` plus
  `ObjectMinCardinality`, `ObjectMaxCardinality` and
  `ObjectExactCardinality`, qualified or not, over a property IRI or its
  inverse (`ObjProp.isBasic`);
- axioms: those of `Axiom.isSHI` (with the larger class expressions) plus
  `FunctionalObjectProperty` and `InverseFunctionalObjectProperty` over a
  basic property.

The simple-role restriction of OWL 2 DL (no transitive property below a
property in a number restriction or a functionality axiom) is not part of
this predicate. The SHIQ route checks it on the translated clauses
(`OWLFrontend.isSHIQB`) and declines when it fails.
-/

namespace ContextCalculus.OWL

/-- ALCIQ class expressions: ALC with inverse properties and number
restrictions over basic properties. -/
def ClassExpr.isALCIQ : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCIQ
  | .not c => c.isALCIQ
  | .some r c | .all r c => r.isBasic && c.isALCIQ
  | .min _ r c | .max _ r c | .exact _ r c => r.isBasic && c.isALCIQ
  | .oneOf _ | .hasValue .. | .hasSelf _
  | .dataSome .. | .dataAll .. | .dataHasValue .. | .dataMin .. | .dataMax ..
  | .dataExact .. => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

def Axiom.isSHIQ : Axiom → Bool
  | .subClassOf c d => c.isALCIQ && d.isALCIQ
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCIQ
  | .domain r c | .range r c => r.isBasic && c.isALCIQ
  | .functional r | .inverseFunctional r => r.isBasic
  | ax => ax.isSHI

def Ontology.isSHIQ (O : Ontology) : Bool := O.axioms.all Axiom.isSHIQ

theorem ClassExpr.isALCIQ_of_isALCI : ∀ (c : ClassExpr), c.isALCI = true → c.isALCIQ = true
  | .cls _, _ => by rw [isALCIQ]
  | .thing, _ => by rw [isALCIQ]
  | .nothing, _ => by rw [isALCIQ]
  | .and cs, h => by
      rw [isALCI] at h; rw [isALCIQ]
      simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h ⊢
      exact fun c hc => isALCIQ_of_isALCI c (h c hc)
  | .or cs, h => by
      rw [isALCI] at h; rw [isALCIQ]
      simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h ⊢
      exact fun c hc => isALCIQ_of_isALCI c (h c hc)
  | .not c, h => by
      rw [isALCI] at h; rw [isALCIQ]
      exact isALCIQ_of_isALCI c h
  | .some _ c, h => by
      rw [isALCI, Bool.and_eq_true] at h; rw [isALCIQ, Bool.and_eq_true]
      exact ⟨h.1, isALCIQ_of_isALCI c h.2⟩
  | .all _ c, h => by
      rw [isALCI, Bool.and_eq_true] at h; rw [isALCIQ, Bool.and_eq_true]
      exact ⟨h.1, isALCIQ_of_isALCI c h.2⟩
  | .oneOf _, h | .hasValue .., h | .hasSelf _, h | .min .., h | .max .., h
  | .exact .., h | .dataSome .., h | .dataAll .., h | .dataHasValue .., h
  | .dataMin .., h | .dataMax .., h | .dataExact .., h => by
      rw [isALCI] at h; exact absurd h (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

theorem Axiom.isSHIQ_of_isSHI {ax : Axiom} (h : ax.isSHI = true) : ax.isSHIQ = true := by
  cases ax <;>
    simp_all [isSHI, isSHIQ, isSRI, List.all_eq_true, ClassExpr.isALCIQ_of_isALCI]

/-- SHI is part of SHIQ. -/
theorem Ontology.isSHIQ_of_isSHI {O : Ontology} (h : O.isSHI = true) : O.isSHIQ = true := by
  simp only [isSHIQ, isSHI, List.all_eq_true] at h ⊢
  exact fun ax hax => Axiom.isSHIQ_of_isSHI (h ax hax)

#print axioms Ontology.isSHIQ_of_isSHI

end ContextCalculus.OWL
