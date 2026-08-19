import ContextCalculus.HypertableauWire

/-!
# Exact hypertableau taxonomy certificates

This module states the semantic target for a complete named-class taxonomy.
Unlike a collection of positive answers, a `CompleteTaxonomyCertificate`
contains one decision for every named concept and every ordered named-concept
pair. Each decision carries the corresponding theorem or countertheorem.

The executable batch wire checker will refine to this structure. Keeping the
semantic target independent of JSON makes the required coverage explicit:
omitting a negative cell cannot certify completeness.
-/

namespace ContextCalculus.Hypertableau

inductive ConceptDecision
    (ontology : List (Clause Variable Concept Role)) (concept : Concept) : Type where
  | unsatisfiable (proof : UnsatisfiableConcept ontology concept)
  | satisfiable (counterexample : ¬UnsatisfiableConcept ontology concept)

def ConceptDecision.answer : ConceptDecision ontology concept → Bool
  | .unsatisfiable _ => true
  | .satisfiable _ => false

theorem ConceptDecision.answer_eq_true_iff
    (decision : ConceptDecision ontology concept) :
    decision.answer = true ↔ UnsatisfiableConcept ontology concept := by
  cases decision with
  | unsatisfiable proof => simp [ConceptDecision.answer, proof]
  | satisfiable counterexample => simp [ConceptDecision.answer, counterexample]

inductive SubsumptionDecision
    (ontology : List (Clause Variable Concept Role)) (sub sup : Concept) : Type where
  | entailed (proof : EntailsSub ontology sub sup)
  | notEntailed (counterexample : ¬EntailsSub ontology sub sup)

def SubsumptionDecision.answer : SubsumptionDecision ontology sub sup → Bool
  | .entailed _ => true
  | .notEntailed _ => false

theorem SubsumptionDecision.answer_eq_true_iff
    (decision : SubsumptionDecision ontology sub sup) :
    decision.answer = true ↔ EntailsSub ontology sub sup := by
  cases decision with
  | entailed proof => simp [SubsumptionDecision.answer, proof]
  | notEntailed counterexample => simp [SubsumptionDecision.answer, counterexample]

/-- Total semantic evidence for every named-class taxonomy cell. -/
structure CompleteTaxonomyCertificate
    (ontology : List (Clause Variable Concept Role)) (named : List Concept) where
  concept : ∀ candidate, candidate ∈ named → ConceptDecision ontology candidate
  subsumption : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    SubsumptionDecision ontology sub sup

/-- Finite checked evidence for one concept-status cell over one shared
ontology. Node counts may differ between query models and refutations. -/
inductive FiniteConceptDecision
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (concept : Fin conceptCount) : Type where
  | unsatisfiable (nodeCount : Nat)
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (sameOntology : certificate.ontology = ontology)
      (root : Fin nodeCount)
      (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
      (rootCheck : certificate.UnsatisfiableRoot root concept)
      (treeCheck : tree.check certificate = true)
  | satisfiable (nodeCount : Nat)
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (sameOntology : certificate.ontology = ontology)
      (root : Fin nodeCount)
      (rootLabel : (root, .pos concept) ∈ certificate.labels)
      (modelCheck : certificate.checkSat = true)

def FiniteConceptDecision.sound
    (decision : FiniteConceptDecision ontology concept) :
    ConceptDecision ontology concept := by
  cases decision with
  | unsatisfiable nodeCount certificate sameOntology root tree rootCheck treeCheck =>
      rw [← sameOntology]
      exact .unsatisfiable
        (tree.check_unsatisfiable_concept certificate root concept rootCheck treeCheck)
  | satisfiable nodeCount certificate sameOntology root rootLabel modelCheck =>
      rw [← sameOntology]
      exact .satisfiable
        (certificate.checkSat_not_unsatisfiableConcept root concept rootLabel modelCheck)

/-- Finite checked evidence for one ordered subsumption cell. -/
inductive FiniteSubsumptionDecision
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (sub sup : Fin conceptCount) : Type where
  | entailed (nodeCount : Nat)
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (sameOntology : certificate.ontology = ontology)
      (root : Fin nodeCount)
      (tree : FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
      (rootCheck : certificate.SubsumptionRoot root sub sup)
      (treeCheck : tree.check certificate = true)
  | notEntailed (nodeCount : Nat)
      (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount)
      (sameOntology : certificate.ontology = ontology)
      (root : Fin nodeCount)
      (subLabel : (root, .pos sub) ∈ certificate.labels)
      (notSupLabel : (root, .negated sup) ∈ certificate.labels)
      (modelCheck : certificate.checkSat = true)

def FiniteSubsumptionDecision.sound
    (decision : FiniteSubsumptionDecision ontology sub sup) :
    SubsumptionDecision ontology sub sup := by
  cases decision with
  | entailed nodeCount certificate sameOntology root tree rootCheck treeCheck =>
      rw [← sameOntology]
      exact .entailed (tree.check_subsumption certificate root sub sup rootCheck treeCheck)
  | notEntailed nodeCount certificate sameOntology root subLabel notSupLabel modelCheck =>
      rw [← sameOntology]
      exact .notEntailed
        (certificate.checkSat_not_entailsSub root sub sup subLabel notSupLabel modelCheck)

/-- Total finite checker evidence for every cell of one named taxonomy. -/
structure FiniteCompleteTaxonomyCertificate
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  concept : ∀ candidate, candidate ∈ named →
    FiniteConceptDecision ontology candidate
  subsumption : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    FiniteSubsumptionDecision ontology sub sup

def FiniteCompleteTaxonomyCertificate.sound
    (certificate : FiniteCompleteTaxonomyCertificate ontology named) :
    CompleteTaxonomyCertificate ontology named where
  concept candidate hnamed := (certificate.concept candidate hnamed).sound
  subsumption sub hsub sup hsup :=
    (certificate.subsumption sub hsub sup hsup).sound

/-- A total taxonomy indexed by a fixed-size named-class vector. This is the
semantic shape used by the executable row-major batch format. -/
structure IndexedCompleteTaxonomyCertificate
    (ontology : List (Clause Variable Concept Role))
    (named : Fin namedCount → Concept) where
  concept : ∀ index, ConceptDecision ontology (named index)
  subsumption : ∀ sub sup, SubsumptionDecision ontology (named sub) (named sup)

/-- Finite checked evidence for every indexed taxonomy cell. -/
structure IndexedFiniteCompleteTaxonomyCertificate
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : Fin namedCount → Fin conceptCount) where
  concept : ∀ index, FiniteConceptDecision ontology (named index)
  subsumption : ∀ sub sup, FiniteSubsumptionDecision ontology (named sub) (named sup)

def IndexedFiniteCompleteTaxonomyCertificate.sound
    (certificate : IndexedFiniteCompleteTaxonomyCertificate ontology named) :
    IndexedCompleteTaxonomyCertificate ontology named where
  concept index := (certificate.concept index).sound
  subsumption sub sup := (certificate.subsumption sub sup).sound

structure SomeFiniteConceptDecision
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) where
  concept : Fin conceptCount
  decision : FiniteConceptDecision ontology concept

structure SomeFiniteSubsumptionDecision
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) where
  sub : Fin conceptCount
  sup : Fin conceptCount
  decision : FiniteSubsumptionDecision ontology sub sup

/-- A finite evidence pool is complete when every named concept and every
ordered named pair occurs. Extra evidence is harmless; missing cells are not. -/
structure FiniteCoveredTaxonomyCertificate
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (named : List (Fin conceptCount)) where
  concepts : List (SomeFiniteConceptDecision ontology)
  subsumptions : List (SomeFiniteSubsumptionDecision ontology)
  conceptCovered : ∀ concept, concept ∈ named →
    { entry // entry ∈ concepts ∧ entry.concept = concept }
  subsumptionCovered : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named →
    { entry // entry ∈ subsumptions ∧ entry.sub = sub ∧ entry.sup = sup }

def FiniteCoveredTaxonomyCertificate.sound
    (certificate : FiniteCoveredTaxonomyCertificate ontology named) :
    CompleteTaxonomyCertificate ontology named where
  concept candidate hnamed := by
    rcases certificate.conceptCovered candidate hnamed with ⟨entry, _, heq⟩
    exact heq ▸ entry.decision.sound
  subsumption sub hsub sup hsup := by
    rcases certificate.subsumptionCovered sub hsub sup hsup with
      ⟨entry, _, hsubEq, hsupEq⟩
    exact hsupEq ▸ hsubEq ▸ entry.decision.sound

def IndexedCompleteTaxonomyCertificate.conceptAnswer
    (certificate : IndexedCompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role))
      (named : Fin namedCount → Concept))
    (index : Fin namedCount) : Bool :=
  (certificate.concept index).answer

def IndexedCompleteTaxonomyCertificate.subsumptionAnswer
    (certificate : IndexedCompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role))
      (named : Fin namedCount → Concept))
    (sub sup : Fin namedCount) : Bool :=
  (certificate.subsumption sub sup).answer

theorem IndexedCompleteTaxonomyCertificate.conceptAnswer_exact
    (certificate : IndexedCompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role))
      (named : Fin namedCount → Concept))
    (index : Fin namedCount) :
    certificate.conceptAnswer index = true ↔
      UnsatisfiableConcept ontology (named index) :=
  (certificate.concept index).answer_eq_true_iff

theorem IndexedCompleteTaxonomyCertificate.subsumptionAnswer_exact
    (certificate : IndexedCompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role))
      (named : Fin namedCount → Concept))
    (sub sup : Fin namedCount) :
    certificate.subsumptionAnswer sub sup = true ↔
      EntailsSub ontology (named sub) (named sup) :=
  (certificate.subsumption sub sup).answer_eq_true_iff

def CompleteTaxonomyCertificate.unsatisfiable
    [DecidableEq Concept]
    (certificate : CompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role)) named) : List Concept :=
  named.filter fun concept =>
    if h : concept ∈ named then (certificate.concept concept h).answer else false

def CompleteTaxonomyCertificate.subsumptions
    [DecidableEq Concept]
    (certificate : CompleteTaxonomyCertificate
      (ontology : List (Clause Variable Concept Role)) named) : List (Concept × Concept) :=
  named.flatMap fun sub =>
    if hsub : sub ∈ named then
      (named.filter fun sup =>
        if hsup : sup ∈ named
        then (certificate.subsumption sub hsub sup hsup).answer
        else false).map fun sup => (sub, sup)
    else []

theorem CompleteTaxonomyCertificate.unsatisfiable_exact
    [DecidableEq Concept]
    (certificate : CompleteTaxonomyCertificate ontology named)
    (concept : Concept) (hnamed : concept ∈ named) :
    concept ∈ certificate.unsatisfiable ↔
      UnsatisfiableConcept ontology concept := by
  simp [CompleteTaxonomyCertificate.unsatisfiable, hnamed,
    (certificate.concept concept hnamed).answer_eq_true_iff]

theorem CompleteTaxonomyCertificate.subsumptions_exact
    [DecidableEq Concept]
    (certificate : CompleteTaxonomyCertificate ontology named)
    (sub sup : Concept) (hsub : sub ∈ named) (hsup : sup ∈ named) :
    (sub, sup) ∈ certificate.subsumptions ↔ EntailsSub ontology sub sup := by
  simp [CompleteTaxonomyCertificate.subsumptions, hsub, hsup,
    (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff]

#print axioms ConceptDecision.answer_eq_true_iff
#print axioms SubsumptionDecision.answer_eq_true_iff
#print axioms CompleteTaxonomyCertificate.unsatisfiable_exact
#print axioms CompleteTaxonomyCertificate.subsumptions_exact
#print axioms FiniteConceptDecision.sound
#print axioms FiniteSubsumptionDecision.sound
#print axioms FiniteCompleteTaxonomyCertificate.sound
#print axioms IndexedFiniteCompleteTaxonomyCertificate.sound
#print axioms IndexedCompleteTaxonomyCertificate.conceptAnswer_exact
#print axioms IndexedCompleteTaxonomyCertificate.subsumptionAnswer_exact
#print axioms FiniteCoveredTaxonomyCertificate.sound

end ContextCalculus.Hypertableau
