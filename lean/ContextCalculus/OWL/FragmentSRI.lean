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

/-- ALC class expressions over named or inverse properties. -/
def ClassExpr.isALCI : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALCI
  | .not c => c.isALCI
  | .some _ c | .all _ c => c.isALCI
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

def Axiom.isSRI : Axiom → Bool
  | .subClassOf c d => c.isALCI && d.isALCI
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALCI
  | .domain _ c | .range _ c => c.isALCI
  | .subObjectPropertyOf rs _ => !rs.isEmpty
  | .equivalentObjectProperties _ | .inverseObjectProperties _ _
  | .transitive _ | .symmetric _ => true
  | .declareClass _ | .declareObjectProperty _ => true

def Ontology.isSRI (O : Ontology) : Bool := O.axioms.all Axiom.isSRI

end ContextCalculus.OWL
