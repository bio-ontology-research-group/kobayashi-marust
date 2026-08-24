import ContextCalculus.CheckerTerm

/-!
# Structural invariants for CB clauses
-/

namespace ContextCalculus.CBClauseShape

open ContextCalculus ContextCalculus.CheckerTerm

/-- Every body literal of a clause is a concept or role atom. -/
def PredicateBody (clause : FCL) : Prop :=
  ∀ literal ∈ clause.body, ∃ predicate, literal = .P predicate

def predicateBodyB (clause : FCL) : Bool :=
  clause.body.all fun literal => match literal with
    | .P _ => true
    | _ => false

theorem predicateBodyB_eq_true_iff (clause : FCL) :
    predicateBodyB clause = true ↔ PredicateBody clause := by
  rw [predicateBodyB, List.all_eq_true]
  constructor
  · intro hall literal hliteral
    specialize hall literal hliteral
    cases literal with
    | P predicate => exact ⟨predicate, rfl⟩
    | eq => simp at hall
    | ineq => simp at hall
  · intro hbody literal hliteral
    obtain ⟨predicate, rfl⟩ := hbody literal hliteral
    rfl

theorem all_predicateBodyB_eq_true_iff (clauses : List FCL) :
    clauses.all predicateBodyB = true ↔
      ∀ clause ∈ clauses, PredicateBody clause := by
  rw [List.all_eq_true]
  exact forall_congr' fun clause => forall_congr' fun _ =>
    predicateBodyB_eq_true_iff clause

theorem predicateBody_substCl (substitution : List (Int × FTerm))
    (clause : FCL) (hbody : PredicateBody clause) :
    PredicateBody (substCl substitution clause) := by
  intro literal hliteral
  simp only [substCl, List.mem_map] at hliteral
  obtain ⟨source, hsource, rfl⟩ := hliteral
  obtain ⟨predicate, rfl⟩ := hbody source hsource
  cases predicate with
  | concept concept term =>
      exact ⟨.concept concept (substT substitution term), rfl⟩
  | role role left right =>
      exact ⟨.role role (substT substitution left)
        (substT substitution right), rfl⟩

#print axioms predicateBody_substCl
#print axioms all_predicateBodyB_eq_true_iff

end ContextCalculus.CBClauseShape
