import ContextCalculus.HypertableauEqualityNormalization

/-!
# Semantics of hypertableau clause preprocessing

This module certifies the two classical clause transformations used by Rust's
`trigger_absorb` and `contrapositives` functions. Certificates retain the exact
source and target clauses, so a later executable decoder need only check list
equalities and source membership.
-/

namespace ContextCalculus.Hypertableau

theorem Interp.satLit_complement_iff_not
    (I : Interp Domain Concept Role) (lit : Lit Concept) (value : Domain) :
    I.satLit lit.complement value ↔ ¬I.satLit lit value := by
  cases lit with
  | mk concept neg => cases neg <;> simp [Interp.satLit, Lit.complement]

def negativeConceptAtoms (node : Variable) (concepts : List Concept) :
    List (Atom Variable Concept Role) :=
  concepts.map fun concept => .concept (.negated concept) node

def positiveConceptAtoms (node : Variable) (concepts : List Concept) :
    List (Atom Variable Concept Role) :=
  concepts.map fun concept => .concept (.pos concept) node

/-- Checked shape of Rust's trigger absorption. The source is
`⊤ → ¬C₁ ∨ ... ∨ ¬Cₖ ∨ P₁ ∨ ... ∨ Pₘ`; the target is
`C₁ ∧ ... ∧ Cₖ → P₁ ∨ ... ∨ Pₘ`. -/
structure TriggerAbsorption
    (source target : Clause Variable Concept Role) where
  node : Variable
  negative : List Concept
  positive : List Concept
  source_body : source.body = []
  source_head : source.head.Perm
    (negativeConceptAtoms node negative ++ positiveConceptAtoms node positive)
  target_eq : target = {
    body := positiveConceptAtoms node negative
    head := positiveConceptAtoms node positive }

theorem TriggerAbsorption.modelsClause_iff
    {source target : Clause Variable Concept Role}
    (certificate : TriggerAbsorption source target)
    (I : Interp Domain Concept Role) :
    I.modelsClause source ↔ I.modelsClause target := by
  rcases certificate with ⟨node, negative, positive, sourceBody, sourceHead, rfl⟩
  constructor
  · intro hsource assignment hbody
    rcases hsource assignment (by simpa [sourceBody]) with ⟨atom, hatom, hsat⟩
    have hatom := sourceHead.mem_iff.mp hatom
    rw [List.mem_append] at hatom
    rcases hatom with hnegative | hpositive
    · rcases List.mem_map.mp hnegative with ⟨concept, hconcept, rfl⟩
      have hrequired := hbody (.concept (.pos concept) node)
        (List.mem_map.mpr ⟨concept, hconcept, rfl⟩)
      exact False.elim (hsat hrequired)
    · exact ⟨atom, hpositive, hsat⟩
  · intro htarget assignment _
    by_cases hall : ∀ concept ∈ negative,
        I.concept concept (assignment node)
    · rcases htarget assignment (by
          intro atom hatom
          rcases List.mem_map.mp hatom with ⟨concept, hconcept, rfl⟩
          exact hall concept hconcept) with ⟨atom, hatom, hsat⟩
      exact ⟨atom, sourceHead.mem_iff.mpr (List.mem_append_right _ hatom), hsat⟩
    · push Not at hall
      rcases hall with ⟨concept, hconcept, hmissing⟩
      let atom : Atom Variable Concept Role :=
        .concept (.negated concept) node
      have hatom : atom ∈ negativeConceptAtoms node negative :=
        List.mem_map.mpr ⟨concept, hconcept, rfl⟩
      exact ⟨atom, sourceHead.mem_iff.mpr (List.mem_append_left _ hatom), hmissing⟩

theorem TriggerAbsorption.models_iff
    {source target : Clause Variable Concept Role}
    (certificate : TriggerAbsorption source target)
    (I : Interp Domain Concept Role) :
    I.models [source] ↔ I.models [target] := by
  simp only [Interp.models, List.forall_mem_singleton]
  exact certificate.modelsClause_iff I

/-- Exact, order-preserving account of the in-place trigger-absorption pass.
Each clause is either retained byte-for-byte or accompanied by an absorption
proof. -/
inductive OntologyTriggerAbsorption :
    List (Clause Variable Concept Role) →
    List (Clause Variable Concept Role) → Prop
  | nil : OntologyTriggerAbsorption [] []
  | keep (tail : OntologyTriggerAbsorption source target) :
      OntologyTriggerAbsorption (clause :: source) (clause :: target)
  | absorb (proof : TriggerAbsorption sourceClause targetClause)
      (tail : OntologyTriggerAbsorption source target) :
      OntologyTriggerAbsorption (sourceClause :: source) (targetClause :: target)

theorem OntologyTriggerAbsorption.models_iff
    {source target : List (Clause Variable Concept Role)}
    (normalization : OntologyTriggerAbsorption source target)
    (I : Interp Domain Concept Role) :
    I.models source ↔ I.models target := by
  induction normalization with
  | nil => simp [Interp.models]
  | keep tail ih =>
      simp only [Interp.models, List.forall_mem_cons]
      exact and_congr Iff.rfl ih
  | absorb proof tail ih =>
      simp only [Interp.models, List.forall_mem_cons]
      exact and_congr (proof.modelsClause_iff I) ih

def conceptAtoms (node : Variable) (literals : List (Lit Concept)) :
    List (Atom Variable Concept Role) :=
  literals.map fun literal => .concept literal node

/-- One checked contrapositive generated from an all-concept, same-variable
clash clause. `before` and `after` preserve duplicate literals and exact order. -/
structure ClashContrapositive
    (source target : Clause Variable Concept Role) where
  node : Variable
  selected : Lit Concept
  leftLits : List (Lit Concept)
  rightLits : List (Lit Concept)
  source_eq : source = {
    body := conceptAtoms node (leftLits ++ selected :: rightLits)
    head := [] }
  target_eq : target = {
    body := conceptAtoms node (leftLits ++ rightLits)
    head := [.concept selected.complement node] }

theorem ClashContrapositive.entailed
    {source target : Clause Variable Concept Role}
    (certificate : ClashContrapositive source target)
    (I : Interp Domain Concept Role)
    (hsource : I.modelsClause source) : I.modelsClause target := by
  rcases certificate with ⟨node, selected, leftLits, rightLits, rfl, rfl⟩
  intro assignment hbody
  have hrest : ∀ literal ∈ leftLits ++ rightLits,
      I.satLit literal (assignment node) := by
    intro literal hliteral
    exact hbody (.concept literal node)
      (List.mem_map.mpr ⟨literal, hliteral, rfl⟩)
  have hnot : ¬I.satLit selected (assignment node) := by
    intro hselected
    rcases hsource assignment (by
        intro atom hatom
        rcases List.mem_map.mp hatom with ⟨literal, hliteral, rfl⟩
        rw [List.mem_append] at hliteral
        rcases hliteral with hbefore | hselectedOrAfter
        · exact hrest literal (List.mem_append_left _ hbefore)
        · rw [List.mem_cons] at hselectedOrAfter
          rcases hselectedOrAfter with rfl | hafter
          · exact hselected
          · exact hrest literal (List.mem_append_right _ hafter)) with
      ⟨atom, hatom, _⟩
    simp at hatom
  exact ⟨.concept selected.complement node,
    by simp, (I.satLit_complement_iff_not selected _).2 hnot⟩

/-- A source clause and checked derivation for one appended contrapositive. -/
structure ContrapositiveWitness
    (base : List (Clause Variable Concept Role))
    (target : Clause Variable Concept Role) where
  source : Clause Variable Concept Role
  source_mem : source ∈ base
  proof : ClashContrapositive source target

/-- Every appended clause has an explicit source clash clause in the base
ontology and a checked contrapositive derivation from it. -/
structure ContrapositiveExtension
    (base added : List (Clause Variable Concept Role)) where
  witness : ∀ target, target ∈ added →
    ContrapositiveWitness base target

theorem ContrapositiveExtension.models_added
    {base added : List (Clause Variable Concept Role)}
    (certificate : ContrapositiveExtension base added)
    (I : Interp Domain Concept Role) (hbase : I.models base) : I.models added := by
  intro target htarget
  rcases certificate.witness target htarget with ⟨source, hsource, proof⟩
  exact proof.entailed I (hbase source hsource)

theorem ContrapositiveExtension.models_append_iff
    {base added : List (Clause Variable Concept Role)}
    (certificate : ContrapositiveExtension base added)
    (I : Interp Domain Concept Role) :
    I.models (base ++ added) ↔ I.models base := by
  constructor
  · intro hall source hsource
    exact hall source (List.mem_append_left _ hsource)
  · intro hbase clause hclause
    rw [List.mem_append] at hclause
    rcases hclause with hbaseClause | hadded
    · exact hbase clause hbaseClause
    · exact certificate.models_added I hbase clause hadded

def ContrapositiveExtension.modelEquivalent
    {base added : List (Clause Variable Concept Role)}
    (certificate : ContrapositiveExtension base added) :
    ModelEquivalent (base ++ added) base :=
  fun _ I => certificate.models_append_iff I

/-- A proof object for the exact preprocessing order in `Ht::new`: trigger
absorption, append entailed contrapositives, then normalize body equalities. -/
structure PreprocessingCertificate
    (source target : List (Clause Variable Concept Role)) where
  absorbed : List (Clause Variable Concept Role)
  added : List (Clause Variable Concept Role)
  trigger : OntologyTriggerAbsorption source absorbed
  contra : ContrapositiveExtension absorbed added
  equality : OntologyEqualityNormalization (absorbed ++ added) target

theorem PreprocessingCertificate.models_iff
    {source target : List (Clause Variable Concept Role)}
    (certificate : PreprocessingCertificate source target)
    (I : Interp Domain Concept Role) :
    I.models source ↔ I.models target := by
  exact (certificate.trigger.models_iff I).trans
    ((certificate.contra.models_append_iff I).symm.trans
      (certificate.equality.models_iff I))

def PreprocessingCertificate.modelEquivalent
    {source target : List (Clause Variable Concept Role)}
    (certificate : PreprocessingCertificate source target) :
    ModelEquivalent source target :=
  fun _ I => certificate.models_iff I

section Tests

private def interleavedSource : Clause (Fin 1) (Fin 3) (Fin 0) := {
  body := []
  head := [
    .concept (.pos 0) 0,
    .concept (.negated 1) 0,
    .concept (.pos 2) 0] }

private def interleavedTarget : Clause (Fin 1) (Fin 3) (Fin 0) := {
  body := [.concept (.pos 1) 0]
  head := [.concept (.pos 0) 0, .concept (.pos 2) 0] }

private def interleavedProof :
    TriggerAbsorption interleavedSource interleavedTarget := {
  node := 0
  negative := [1]
  positive := [0, 2]
  source_body := rfl
  source_head := by decide
  target_eq := rfl
}

example (I : Interp Domain (Fin 3) (Fin 0)) :
    I.modelsClause interleavedSource ↔ I.modelsClause interleavedTarget :=
  interleavedProof.modelsClause_iff I

end Tests

#print axioms Interp.satLit_complement_iff_not
#print axioms TriggerAbsorption.modelsClause_iff
#print axioms TriggerAbsorption.models_iff
#print axioms OntologyTriggerAbsorption.models_iff
#print axioms ClashContrapositive.entailed
#print axioms ContrapositiveExtension.models_append_iff
#print axioms ContrapositiveExtension.modelEquivalent
#print axioms PreprocessingCertificate.models_iff
#print axioms PreprocessingCertificate.modelEquivalent

end ContextCalculus.Hypertableau
