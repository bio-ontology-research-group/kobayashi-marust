import ContextCalculus.OWL.Semantics

/-!
# The EL and ALC parts of the frontend fragment

`docs/V1.6.2-FRONTEND-PLAN.md`, section 7. The phase A theorems are stated
for ontologies in one of two parts of `F`, each matching the normal forms
that a v1.6.0 reference procedure decides exactly:

- **EL** (`ELCompletion`, NF1 to NF7): class expressions built from class
  IRIs, `owl:Thing`, `owl:Nothing`, intersection and existential
  restriction over a named object property; axioms SubClassOf,
  EquivalentClasses, DisjointClasses, ObjectPropertyDomain over a named
  property, SubObjectPropertyOf with a chain of named properties,
  EquivalentObjectProperties and TransitiveObjectProperty over named
  properties, and declarations.
- **ALC** (`Ctx`, finite type elimination): every class constructor of
  `F` over named object properties; axioms SubClassOf, EquivalentClasses,
  DisjointClasses, ObjectPropertyDomain and ObjectPropertyRange over named
  properties, and declarations; no object-property axioms.

Both predicates are Boolean so that the frontend can test them and the
completeness theorems can take them as hypotheses.
-/

namespace ContextCalculus.OWL

/-- An object-property expression is a property IRI, not an inverse. -/
def ObjProp.isNamed : ObjProp → Bool
  | .named _ => true
  | .inv _ => false

/-- EL class expressions. -/
def ClassExpr.isEL : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs => cs.attach.all fun ⟨c, _⟩ => c.isEL
  | .some r c => r.isNamed && c.isEL
  | .or _ | .not _ | .all _ _ => false
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

/-- ALC class expressions: every constructor, named properties only. -/
def ClassExpr.isALC : ClassExpr → Bool
  | .cls _ | .thing | .nothing => true
  | .and cs | .or cs => cs.attach.all fun ⟨c, _⟩ => c.isALC
  | .not c => c.isALC
  | .some r c | .all r c => r.isNamed && c.isALC
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ cs›; omega)
    | omega

def Axiom.isEL : Axiom → Bool
  | .subClassOf c d => c.isEL && d.isEL
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isEL
  | .domain r c => r.isNamed && c.isEL
  | .range _ _ => false
  | .subObjectPropertyOf rs r => !rs.isEmpty && rs.all ObjProp.isNamed && r.isNamed
  | .equivalentObjectProperties rs => rs.all ObjProp.isNamed
  | .transitive r => r.isNamed
  | .inverseObjectProperties _ _ | .symmetric _ => false
  | .declareClass _ | .declareObjectProperty _ => true

def Axiom.isALC : Axiom → Bool
  | .subClassOf c d => c.isALC && d.isALC
  | .equivalentClasses cs | .disjointClasses cs => cs.all ClassExpr.isALC
  | .domain r c | .range r c => r.isNamed && c.isALC
  | .subObjectPropertyOf _ _ | .equivalentObjectProperties _
  | .inverseObjectProperties _ _ | .transitive _ | .symmetric _ => false
  | .declareClass _ | .declareObjectProperty _ => true

def Ontology.isEL (O : Ontology) : Bool := O.axioms.all Axiom.isEL
def Ontology.isALC (O : Ontology) : Bool := O.axioms.all Axiom.isALC

/-- The class IRIs one axiom mentions or declares. -/
def Axiom.classIRIs : Axiom → List IRI
  | .subClassOf c d => c.names ++ d.names
  | .equivalentClasses cs | .disjointClasses cs => cs.flatMap ClassExpr.names
  | .domain _ c | .range _ c => c.names
  | .declareClass a => [a]
  | _ => []

/-- `O` mentions the class IRI `A`. -/
def Ontology.mentionsClass (O : Ontology) (A : IRI) : Prop :=
  ∃ ax ∈ O.axioms, A ∈ ax.classIRIs

/-! ## The probe reading of unsatisfiability and inconsistency

Statements fixed by the lead; proofs by the translation task. Both rest on
the agreement lemma: changing the extension of a class IRI that `O` does not
mention preserves being a model of `O`. -/

/-- For distinct IRIs `P`, `Q` not mentioned by `O`, `O` is inconsistent
exactly when it entails `SubClassOf(P Q)`. -/
theorem inconsistent_iff_entailsSub_fresh {O : Ontology} {P Q : IRI}
    (hP : ¬ O.mentionsClass P) (hQ : ¬ O.mentionsClass Q) (hPQ : P ≠ Q) :
    Inconsistent O ↔ EntailsSub O P Q := by
  sorry

/-- For an IRI `Q` not mentioned by `O` and different from `A`, the class
`A` is unsatisfiable exactly when `O` entails `SubClassOf(A Q)`. -/
theorem unsatisfiable_iff_entailsSub_fresh {O : Ontology} {A Q : IRI}
    (hQ : ¬ O.mentionsClass Q) (hAQ : A ≠ Q) :
    Unsatisfiable O A ↔ EntailsSub O A Q := by
  sorry

end ContextCalculus.OWL
