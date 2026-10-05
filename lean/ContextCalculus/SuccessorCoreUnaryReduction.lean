/-!
Unary source implications can justify removing redundant successor-core
predicates. Reachability uses only retained seeds and exact source edges.
Deletion is sequential: each deletion must have its own derivation from the
then-retained core, so a cycle cannot justify deleting all its generators.
This proves the model equivalence of a justified deletion, not the extraction
of edges from Rust clauses or the full production certification boundary.
-/
namespace ContextCalculus.SuccessorCoreUnaryReduction

variable {Concept : Type}

inductive Derives (edges : List (Concept × Concept)) (core : List Concept) :
    Concept → Prop
  | seed {concept} : concept ∈ core → Derives edges core concept
  | step {source target} : (source, target) ∈ edges →
      Derives edges core source → Derives edges core target

def ModelsCore (truth : Concept → Prop) (core : List Concept) : Prop :=
  ∀ concept ∈ core, truth concept

def ModelsEdges (truth : Concept → Prop) (edges : List (Concept × Concept)) : Prop :=
  ∀ source target, (source, target) ∈ edges → truth source → truth target

theorem derives_sound {edges : List (Concept × Concept)} {core : List Concept}
    {concept : Concept} (truth : Concept → Prop)
    (sourceModels : ModelsEdges truth edges) (coreModels : ModelsCore truth core)
    (derivation : Derives edges core concept) : truth concept := by
  induction derivation with
  | seed member => exact coreModels _ member
  | step member _ inductionHypothesis =>
      exact sourceModels _ _ member inductionHypothesis

theorem justified_deletion_models_iff
    (truth : Concept → Prop) (edges : List (Concept × Concept))
    (retained : List Concept) (removed : Concept)
    (sourceModels : ModelsEdges truth edges)
    (derivation : Derives edges retained removed) :
    ModelsCore truth (removed :: retained) ↔ ModelsCore truth retained := by
  constructor
  · intro original concept member
    exact original concept (List.mem_cons_of_mem _ member)
  · intro retainedModels concept member
    rcases List.mem_cons.mp member with equal | member
    · subst concept
      exact derives_sound truth sourceModels retainedModels derivation
    · exact retainedModels concept member

#print axioms derives_sound
#print axioms justified_deletion_models_iff
end ContextCalculus.SuccessorCoreUnaryReduction
