import ContextCalculus.ELReferenceSaturation

/-!
# Executable tests for the EL reference saturation

This module exercises `ContextCalculus.ELReference.closure`, `referenceBit`
and `referenceInconsistent` on small EL ontologies covering NF1 chains, NF2
conjunctions, NF3/NF4 existential round trips, backward bottom propagation
along an edge, NF7 role chains, reflexive roles firing NF4, and inconsistent
ontologies.
-/

namespace ContextCalculus.ELReference.Tests

open ContextCalculus.ELCompletion
open ContextCalculus.ELReference

/-- NF1 chain: `A ⊑ B` and `B ⊑ C` entail `A ⊑ C` but not `C ⊑ A`. -/
def nf1ChainOntology : Ontology :=
  [.nf1 2 3, .nf1 3 4]

#eval referenceBit 0 1 [2, 3, 4] nf1ChainOntology 2 4
#eval referenceBit 0 1 [2, 3, 4] nf1ChainOntology 4 2

example : referenceBit 0 1 [2, 3, 4] nf1ChainOntology 2 4 = true := by decide
example : referenceBit 0 1 [2, 3, 4] nf1ChainOntology 4 2 = false := by decide
example : referenceInconsistent 0 1 [2, 3, 4] nf1ChainOntology = false := by decide

/-- NF2 conjunction: `A ⊑ B`, `A ⊑ C` and `B ⊓ C ⊑ D` entail `A ⊑ D`. -/
def nf2Ontology : Ontology :=
  [.nf1 2 3, .nf1 2 4, .nf2 3 4 5]

#eval referenceBit 0 1 [2, 3, 4, 5] nf2Ontology 2 5

example : referenceBit 0 1 [2, 3, 4, 5] nf2Ontology 2 5 = true := by decide
example : referenceBit 0 1 [2, 3, 4, 5] nf2Ontology 3 5 = false := by decide

/-- NF3/NF4 existential round trip: `A ⊑ ∃r.B` and `∃r.B ⊑ C` entail `A ⊑ C`. -/
def nf3Nf4Ontology : Ontology :=
  [.nf3 2 0 3, .nf4 0 3 4]

#eval referenceBit 0 1 [2, 3, 4] nf3Nf4Ontology 2 4
#eval referenceBit 0 1 [2, 3, 4] nf3Nf4Ontology 3 4

example : referenceBit 0 1 [2, 3, 4] nf3Nf4Ontology 2 4 = true := by decide
example : referenceBit 0 1 [2, 3, 4] nf3Nf4Ontology 3 4 = false := by decide

/-- Bottom propagation through an edge: `A ⊑ ∃r.B` and `B ⊑ ⊥` make `A`
unsatisfiable (`A ⊑ ⊥` and `A ⊑ C`) while keeping the ontology consistent. -/
def bottomEdgeOntology : Ontology :=
  [.nf3 2 0 3, .nf5 3]

#eval referenceBit 0 1 [2, 3, 4] bottomEdgeOntology 2 1
#eval referenceBit 0 1 [2, 3, 4] bottomEdgeOntology 2 4
#eval referenceInconsistent 0 1 [2, 3, 4] bottomEdgeOntology

example : referenceBit 0 1 [2, 3, 4] bottomEdgeOntology 2 1 = true := by decide
example : referenceBit 0 1 [2, 3, 4] bottomEdgeOntology 2 4 = true := by decide
example : referenceBit 0 1 [2, 3, 4] bottomEdgeOntology 4 2 = false := by decide
example : referenceInconsistent 0 1 [2, 3, 4] bottomEdgeOntology = false := by decide

/-- NF7 role chain: `A ⊑ ∃r.B`, `B ⊑ ∃s.C`, `r ∘ s ⊑ t` and `∃t.C ⊑ D`
entail `A ⊑ D`. -/
def nf7ChainOntology : Ontology :=
  [.nf3 2 0 3, .nf3 3 1 4, .nf7 0 1 2, .nf4 2 4 5]

#eval (closure 0 1 [2, 3, 4, 5] nf7ChainOntology).hasEdge 2 2 4
#eval referenceBit 0 1 [2, 3, 4, 5] nf7ChainOntology 2 5

example : (closure 0 1 [2, 3, 4, 5] nf7ChainOntology).hasEdge 2 2 4 = true := by decide
example : referenceBit 0 1 [2, 3, 4, 5] nf7ChainOntology 2 5 = true := by decide
example : referenceBit 0 1 [2, 3, 4, 5] nf7ChainOntology 3 5 = false := by decide

/-- Reflexive role firing NF4: `Refl(r)` and `∃r.A ⊑ B` entail `A ⊑ B`. -/
def reflexiveNf4Ontology : Ontology :=
  [.reflexive 0, .nf4 0 2 3]

#eval referenceBit 0 1 [2, 3] reflexiveNf4Ontology 2 3
#eval referenceBit 0 1 [2, 3] reflexiveNf4Ontology 3 2

example : referenceBit 0 1 [2, 3] reflexiveNf4Ontology 2 3 = true := by decide
example : referenceBit 0 1 [2, 3] reflexiveNf4Ontology 3 2 = false := by decide

/-- Inconsistent ontology: `⊤ ⊑ A`, `A ⊑ ∃r.B` and `B ⊑ ⊥` derive `⊤ ⊑ ⊥`. -/
def inconsistentOntology : Ontology :=
  [.nf1 0 2, .nf3 2 0 3, .nf5 3]

#eval referenceInconsistent 0 1 [2, 3] inconsistentOntology

example : referenceInconsistent 0 1 [2, 3] inconsistentOntology = true := by decide

/-- End-to-end semantic entailment via `referenceBit_exact_of_named`. -/
example : EntailsSub (top := 0) (bottom := 1) nf3Nf4Ontology 2 4 :=
  (referenceBit_exact_of_named 0 1 [2, 3, 4] nf3Nf4Ontology (by decide) 4).mp (by decide)

/-- End-to-end semantic unsatisfiability via `referenceInconsistent_exact`. -/
example : Unsatisfiable (top := 0) (bottom := 1) inconsistentOntology :=
  (referenceInconsistent_exact 0 1 [2, 3] inconsistentOntology).mp (by decide)

end ContextCalculus.ELReference.Tests
