import ContextCalculus.OWL.Fragment

/-!
# The SRI part of the frontend fragment

`docs/V1.6.3-HT-PLAN.md`. Class expressions are those of ALC with inverse
properties allowed anywhere (`ObjectInverseOf` inside restrictions); axioms
are the class axioms of `F`, domain and range over any property, and every
object-property axiom of `F` (property chains, equivalent and inverse
properties, transitivity, symmetry). It contains the EL and the ALC parts.

The predicate does not check that the property chains are regular. The
translation to `SRI.Clause` is exact for any chains; the decision
procedure checks regularity and declines otherwise.
-/

namespace ContextCalculus.OWL

/-- A property IRI or the inverse of one (not `owl:topObjectProperty` or
`owl:bottomObjectProperty`). -/
def ObjProp.isBasic : ObjProp → Bool
  | .named _ | .inv _ => true
  | .top | .bot => false

theorem ObjProp.isBasic_of_isNamed {r : ObjProp} (h : r.isNamed = true) : r.isBasic = true := by
  cases r <;> simp_all [isNamed, isBasic]

/-- ALC class expressions over named or inverse properties. -/
def ClassExpr.isALCI : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCI
  | .not c => c.isALCI
  | .some r c | .all r c => r.isBasic && c.isALCI
  | .oneOf _ | .hasValue .. | .hasSelf _ | .min .. | .max .. | .exact ..
  | .dataSome .. | .dataAll .. | .dataHasValue .. | .dataMin .. | .dataMax ..
  | .dataExact .. => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

def Axiom.isSRI : Axiom → Bool
  | .subClassOf c d => c.isALCI && d.isALCI
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCI
  | .domain r c | .range r c => r.isBasic && c.isALCI
  | .subObjectPropertyOf rs r => !rs.isEmpty && rs.all ObjProp.isBasic && r.isBasic
  | .equivalentObjectProperties rs => rs.all ObjProp.isBasic
  | .inverseObjectProperties r s => r.isBasic && s.isBasic
  | .transitive r | .symmetric r => r.isBasic
  | .declareClass _ | .declareObjectProperty _ => true
  | .declareDataProperty _ | .declareNamedIndividual _ | .declareDatatype _
  | .declareAnnotationProperty _ => true
  | .disjointUnion .. | .disjointObjectProperties _ | .functional _
  | .inverseFunctional _ | .reflexive _ | .irreflexive _ | .asymmetric _
  | .subDataPropertyOf .. | .equivalentDataProperties _ | .disjointDataProperties _
  | .dataDomain .. | .dataRange .. | .functionalData _ | .datatypeDefinition ..
  | .hasKey .. | .sameIndividual _ | .differentIndividuals _ | .classAssertion ..
  | .objectPropertyAssertion .. | .negativeObjectPropertyAssertion ..
  | .dataPropertyAssertion .. | .negativeDataPropertyAssertion .. => false

def Ontology.isSRI (O : Ontology) : Bool := O.axioms.all Axiom.isSRI

/-! ## The SHI part

The SHI part keeps the class expressions and axioms of the SRI part and
allows only two kinds of property chains: a plain inclusion
`SubObjectPropertyOf(r s)` and the transitivity chain
`SubObjectPropertyOf(ObjectPropertyChain(r r) r)`. The v1.6.3 SHI route
(`OWLFrontend.owlSRIReference`) publishes on every ontology of this part
(`owlSRIReference_complete`).

The SHI part contains the ALC part (`Ontology.isSHI_of_isALC`) but not the EL
part: OWL EL allows any chain, for example
`SubObjectPropertyOf(ObjectPropertyChain(p q) r)`.
-/

def Axiom.isSHI : Axiom → Bool
  | .subObjectPropertyOf rs r =>
      (rs.length == 1 || rs == [r, r]) && rs.all ObjProp.isBasic && r.isBasic
  | ax => ax.isSRI

def Ontology.isSHI (O : Ontology) : Bool := O.axioms.all Axiom.isSHI

theorem Axiom.isSRI_of_isSHI {ax : Axiom} (h : ax.isSHI = true) : ax.isSRI = true := by
  cases ax with
  | subObjectPropertyOf rs r =>
      simp only [isSHI, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
      simp only [isSRI, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.and_eq_true]
      refine ⟨⟨?_, h.1.2⟩, h.2⟩
      rcases h.1.1 with h | rfl
      · exact List.ne_nil_of_length_pos (by omega)
      · simp
  | _ => exact h

theorem Ontology.isSRI_of_isSHI {O : Ontology} (h : O.isSHI = true) : O.isSRI = true := by
  simp only [isSHI, isSRI, List.all_eq_true] at h ⊢
  exact fun ax hax => Axiom.isSRI_of_isSHI (h ax hax)

theorem ClassExpr.isALCI_of_isALC : ∀ (c : ClassExpr), c.isALC = true → c.isALCI = true
  | .cls _, _ => by rw [isALCI]
  | .thing, _ => by rw [isALCI]
  | .nothing, _ => by rw [isALCI]
  | .and cs, h => by
      rw [isALC] at h; rw [isALCI]
      simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h ⊢
      exact fun c hc => isALCI_of_isALC c (h c hc)
  | .or cs, h => by
      rw [isALC] at h; rw [isALCI]
      simp only [List.all_eq_true, List.mem_attach, true_implies, Subtype.forall] at h ⊢
      exact fun c hc => isALCI_of_isALC c (h c hc)
  | .not c, h => by
      rw [isALC] at h; rw [isALCI]
      exact isALCI_of_isALC c h
  | .some _ c, h => by
      rw [isALC, Bool.and_eq_true] at h; rw [isALCI, Bool.and_eq_true]
      exact ⟨ObjProp.isBasic_of_isNamed h.1, isALCI_of_isALC c h.2⟩
  | .all _ c, h => by
      rw [isALC, Bool.and_eq_true] at h; rw [isALCI, Bool.and_eq_true]
      exact ⟨ObjProp.isBasic_of_isNamed h.1, isALCI_of_isALC c h.2⟩
  | .oneOf _, h | .hasValue .., h | .hasSelf _, h | .min .., h | .max .., h
  | .exact .., h | .dataSome .., h | .dataAll .., h | .dataHasValue .., h
  | .dataMin .., h | .dataMax .., h | .dataExact .., h => by
      rw [isALC] at h; exact absurd h (by simp)
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

theorem Axiom.isSHI_of_isALC {ax : Axiom} (h : ax.isALC = true) : ax.isSHI = true := by
  cases ax <;>
    simp_all [isALC, isSHI, isSRI, List.all_eq_true, ClassExpr.isALCI_of_isALC,
      ObjProp.isBasic_of_isNamed]

/-- OWL ALC is part of SHI. -/
theorem Ontology.isSHI_of_isALC {O : Ontology} (h : O.isALC = true) : O.isSHI = true := by
  simp only [isSHI, isALC, List.all_eq_true] at h ⊢
  exact fun ax hax => Axiom.isSHI_of_isALC (h ax hax)

#print axioms Ontology.isSRI_of_isSHI
#print axioms Ontology.isSHI_of_isALC

end ContextCalculus.OWL
