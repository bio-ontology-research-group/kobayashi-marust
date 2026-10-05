import ContextCalculus.HypertableauProductionTaxonomyPublication

/-!
Public query selection restricts the answer matrix, never the ontology.
The semantic predicates below remain those of the complete compiled source.
Only selected subject rows need decisions; private subjects need no answers.
This boundary does not establish source compiler correctness or the runtime's
production decisions, which remain separate certification obligations.
-/
namespace ContextCalculus.Hypertableau

structure ExactSelectedSubjectTaxonomyPublication
    (subjects targets : List Concept)
    (conceptSemantics : Concept → Prop)
    (subsumptionSemantics : Concept → Concept → Prop) where
  conceptAnswer : ∀ concept, concept ∈ subjects → Bool
  conceptExact : ∀ concept hsubject,
    conceptAnswer concept hsubject = true ↔ conceptSemantics concept
  subsumptionAnswer : ∀ sub, sub ∈ subjects → ∀ sup, sup ∈ targets → Bool
  subsumptionExact : ∀ sub hsub sup hsup,
    subsumptionAnswer sub hsub sup hsup = true ↔ subsumptionSemantics sub sup

/-- Exact decisions for visible rows and all targets suffice for the visible
square taxonomy. No decision for a private subject is required. -/
def ExactSelectedSubjectTaxonomyPublication.publicProjection
    {subjects targets visible : List Concept}
    {conceptSemantics : Concept → Prop}
    {subsumptionSemantics : Concept → Concept → Prop}
    (rows : ExactSelectedSubjectTaxonomyPublication subjects targets
      conceptSemantics subsumptionSemantics)
    (publicSubjects : ∀ c, c ∈ visible → c ∈ subjects)
    (publicTargets : ∀ c, c ∈ visible → c ∈ targets) :
    ExactBooleanTaxonomyPublication visible conceptSemantics subsumptionSemantics where
  conceptAnswer c hc := rows.conceptAnswer c (publicSubjects c hc)
  conceptExact c hc := rows.conceptExact c (publicSubjects c hc)
  subsumptionAnswer a ha b hb :=
    rows.subsumptionAnswer a (publicSubjects a ha) b (publicTargets b hb)
  subsumptionExact a ha b hb :=
    rows.subsumptionExact a (publicSubjects a ha) b (publicTargets b hb)

theorem selectedSubjectPublicPublication
    {subjects targets visible : List Concept}
    {conceptSemantics : Concept → Prop}
    {subsumptionSemantics : Concept → Concept → Prop}
    (rows : ExactSelectedSubjectTaxonomyPublication subjects targets
      conceptSemantics subsumptionSemantics)
    (publicSubjects : ∀ c, c ∈ visible → c ∈ subjects)
    (publicTargets : ∀ c, c ∈ visible → c ∈ targets) :
    Nonempty (ExactBooleanTaxonomyPublication visible
      conceptSemantics subsumptionSemantics) :=
  ⟨rows.publicProjection publicSubjects publicTargets⟩

#print axioms selectedSubjectPublicPublication
end ContextCalculus.Hypertableau
