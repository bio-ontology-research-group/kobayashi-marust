import ContextCalculus.HypertableauRoleBlocking
import ContextCalculus.HypertableauBlockingCertificate

/-!
# Exhaustive HT search with checked blocked terminal models

Blocked leaves need not be raw witness-complete tableau states. Instead, the
runtime supplies an untrusted finite fold, and the existing executable checker
validates the materialized graph against the exact ontology. This module
composes that checked terminal model with finite exhaustive search: every root
is refuted or reaches a leaf carrying an independently checked model.
-/

namespace ContextCalculus.Hypertableau

abbrev HasModel (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role), I.models ontology

def HasCheckedFoldModel
    (nodeCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    Prop :=
  ∃ certificate : FiniteFoldCertificate
      nodeCount conceptCount roleCount variableCount,
    certificate.base.ontology = ontology ∧ certificate.check = true

/-- A checked finite fold is a model of the exact ontology named by the search
terminal, regardless of the producer's blocker choices. -/
theorem hasModel_of_hasCheckedFoldModel
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (hfold : HasCheckedFoldModel (nodeCount := nodeCount) ontology) :
    HasModel ontology := by
  rcases hfold with ⟨certificate, hontology, hcheck⟩
  rcases certificate.check_satisfiable hcheck with ⟨interpretation, hmodels⟩
  exact ⟨Fin nodeCount, interpretation, by simpa [hontology] using hmodels⟩

/-- Finite exhaustive equality-free search can terminate at either a direct
open canonical state or a blocked state whose untrusted fold passes the exact
SAT checker. Closed child families still combine through the HT `Refutes`
constructors. -/
theorem finite_exhaustive_ht_complete_with_checked_folds
    {Fact : Type} [Fintype Fact] [DecidableEq Fact]
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (decode : Finset Fact →
      State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    (next : Finset Fact → List (Finset Fact))
    (hgrowth : ∀ parent child, child ∈ next parent → StrictGrowth child parent)
    (hterminal : ∀ facts, next facts = [] →
      Refutes (Fin nodeCount) ontology (decode facts) ∨
      HasCheckedFoldModel (nodeCount := nodeCount) ontology)
    (hcloseChildren : ∀ facts, next facts ≠ [] →
      (∀ child, child ∈ next facts →
        Refutes (Fin nodeCount) ontology (decode child)) →
      Refutes (Fin nodeCount) ontology (decode facts)) :
    ∀ root, Refutes (Fin nodeCount) ontology (decode root) ∨
      ∃ leaf, SearchDescends next root leaf ∧ HasModel ontology := by
  apply finite_exhaustive_search_total next
    (fun facts => Refutes (Fin nodeCount) ontology (decode facts))
    (fun _ => HasModel ontology)
    hgrowth
  · intro facts hempty
    rcases hterminal facts hempty with hrefutes | hfold
    · exact Or.inl hrefutes
    · exact Or.inr (hasModel_of_hasCheckedFoldModel hfold)
  · exact hcloseChildren

#print axioms hasModel_of_hasCheckedFoldModel
#print axioms finite_exhaustive_ht_complete_with_checked_folds

end ContextCalculus.Hypertableau
