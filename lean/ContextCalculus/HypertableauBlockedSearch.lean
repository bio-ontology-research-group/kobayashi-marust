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

/-- The three results of a finite-prefix equality-free search. `frontier` is
the only inconclusive result: it requests a larger node universe and must not
be interpreted as either a refutation or a model. -/
inductive BoundedSearchOutcome
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) : Type where
  | closed (proof : Refutes (Fin nodeCount) ontology state)
  | model (fold : HasCheckedFoldModel (nodeCount := nodeCount) ontology)
  | frontier

/-- A checked finite fold is a model of the exact ontology named by the search
terminal, regardless of the producer's blocker choices. -/
theorem hasModel_of_hasCheckedFoldModel
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (hfold : HasCheckedFoldModel (nodeCount := nodeCount) ontology) :
    HasModel ontology := by
  rcases hfold with ⟨certificate, hontology, hcheck⟩
  rcases certificate.check_satisfiable hcheck with ⟨interpretation, hmodels⟩
  exact ⟨Fin nodeCount, interpretation, by simpa [hontology] using hmodels⟩

/-- A conclusive bounded-search result has its advertised semantics. The
remaining constructor is explicitly exposed as a frontier, so callers cannot
collapse bounded exhaustion into a semantic open branch. -/
theorem BoundedSearchOutcome.semantic_or_frontier
    {ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (result : BoundedSearchOutcome nodeCount conceptCount roleCount variableCount
      ontology state) :
    Refutes (Fin nodeCount) ontology state ∨ HasModel ontology ∨
      result = .frontier := by
  cases result with
  | closed proof => exact Or.inl proof
  | model fold => exact Or.inr (Or.inl (hasModel_of_hasCheckedFoldModel fold))
  | frontier => exact Or.inr (Or.inr rfl)

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

/-- Equality-free finite search using the producer's exact clause-first
transition policy decides the root semantically. This removes abstract growth
and child-closure premises: strict growth follows from absent branch heads or
a fresh witness, and HT refutation constructors combine every closed child.
The remaining runtime obligation is to enumerate this finite search and supply
a checked fold at every non-refuting terminal. -/
theorem finite_first_obstruction_ht_decides
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (next : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount) (Fin roleCount)) →
      List (Finset (GuardedFact (Fin nodeCount) (Fin conceptCount) (Fin roleCount))))
    (hstep : ∀ facts, next facts ≠ [] →
      FirstObstructionStep ontology (stateOfGuardedFacts facts)
        ((next facts).map stateOfGuardedFacts))
    (hterminal : ∀ facts, next facts = [] →
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts facts) ∨
      HasCheckedFoldModel (nodeCount := nodeCount) ontology) :
    ∀ root, Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      HasModel ontology := by
  intro root
  have hgrowth : ∀ parent child, child ∈ next parent →
      StrictGrowth child parent := by
    intro parent child hchild
    have hnonempty : next parent ≠ [] := by
      intro hempty
      simp [hempty] at hchild
    have step := hstep parent hnonempty
    have hstateChild : stateOfGuardedFacts child ∈
        (next parent).map stateOfGuardedFacts :=
      List.mem_map_of_mem hchild
    have hstrict := step.children_strictGrowth hstateChild
    simpa using hstrict
  have hclose : ∀ facts, next facts ≠ [] →
      (∀ child, child ∈ next facts →
        Refutes (Fin nodeCount) ontology (stateOfGuardedFacts child)) →
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts facts) := by
    intro facts hnonempty hchildren
    apply (hstep facts hnonempty).exhaustiveStep.refutes_of_children
    intro child hchild
    rcases List.mem_map.mp hchild with ⟨childFacts, hchildFacts, rfl⟩
    exact hchildren childFacts hchildFacts
  rcases finite_exhaustive_ht_complete_with_checked_folds ontology
      stateOfGuardedFacts next hgrowth hterminal hclose root with
    hrefutes | ⟨_, _, hmodel⟩
  · exact Or.inl hrefutes
  · exact Or.inr hmodel

#print axioms hasModel_of_hasCheckedFoldModel
#print axioms BoundedSearchOutcome.semantic_or_frontier
#print axioms finite_exhaustive_ht_complete_with_checked_folds
#print axioms finite_first_obstruction_ht_decides

end ContextCalculus.Hypertableau
