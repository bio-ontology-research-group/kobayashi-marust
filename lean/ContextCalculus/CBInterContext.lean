import ContextCalculus.CBProductionTrace

/-!
# Semantic foundation for production CB inter-context transfer

`Engine::pred_payload` transports a clause from a successor context back to a
predecessor. It applies the edge substitution to the clause and appends the
sender core to the transported body. The appended core is essential: a sender
clause is only known under that context's core assumptions.

This module proves the exact logical transformation independently of queue and
index bookkeeping. The later production wire must check that its serialized
payload is clause-equivalent to `predTransfer` and that every sent payload is
delivered or represented by a retained strengthening.
-/

namespace ContextCalculus.CBInterContext

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace

variable {D : Type}

/-- A clause derived in a context is valid whenever every predicate in that
context's core holds under the same assignment. -/
def ContextValid (model : TModel D) (core : List FPred) (clause : FCL) : Prop :=
  ∀ assignment,
    (∀ predicate ∈ core, model.evalL assignment (.P predicate)) →
    sat (model.evalL assignment) clause

/-- Exact logical payload built by `Engine::pred_payload`, before its
order-insensitive sort/dedup normalization: back-substitute the sender clause
and append the back-substituted sender core to its body. -/
def predTransfer (substitution : List (Int × FTerm))
    (core : List FPred) (clause : FCL) : FCL :=
  substCl substitution
    ⟨clause.body ++ core.map FLit.P, clause.head⟩

/-- Appending the sender core before substitution turns contextual validity
into ordinary validity of the transported payload. This is the semantic
content of both ordinary Pred and nominal r-Pred sender transfer. -/
theorem predTransfer_sound (model : TModel D) (core : List FPred)
    (clause : FCL) (substitution : List (Int × FTerm))
    (hvalid : ContextValid model core clause) :
    valid model (predTransfer substitution core clause) := by
  intro assignment
  rw [predTransfer, sat_substCl]
  intro hbody
  have hcore : ∀ predicate ∈ core,
      model.evalL (fun id => model.evalT assignment
        (substVar substitution id)) (.P predicate) := by
    intro predicate hpredicate
    exact hbody (.P predicate) (by
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨predicate, hpredicate, rfl⟩)
  have hclauseBody : ∀ literal ∈ clause.body,
      model.evalL (fun id => model.evalT assignment
        (substVar substitution id)) literal := by
    intro literal hliteral
    exact hbody literal (by
      simp only [List.mem_append]
      exact Or.inl hliteral)
  exact hvalid
    (fun id => model.evalT assignment (substVar substitution id))
    hcore hclauseBody

/-- The hypothesis installed by every Succ/r-Succ message carries no new
logical assumption: it is a tautology under every model and assignment. -/
def succHypothesis (predicate : FPred) : FCL :=
  ⟨[.P predicate], [.P predicate]⟩

theorem succHypothesis_valid (model : TModel D) (predicate : FPred) :
    valid model (succHypothesis predicate) := by
  intro assignment hbody
  exact ⟨.P predicate, by simp [succHypothesis],
    hbody (.P predicate) (by simp [succHypothesis])⟩

/-- Resolution preserves validity relative to one receiver core. This is the
semantic receiver half used for every provider selected by `pred_from_neighbor`.
-/
theorem resolveContextual_sound (model : TModel D) (core : List FPred)
    (positive negative : FCL) (literal : FLit)
    (hpositive : ContextValid model core positive)
    (hnegative : ContextValid model core negative)
    (hhead : literal ∈ positive.head) (hbody : literal ∈ negative.body) :
    ContextValid model core (resolvent positive negative literal) := by
  intro assignment hcore
  exact resolution_sound (model.evalL assignment) positive negative literal
    (hpositive assignment hcore) (hnegative assignment hcore) hhead hbody

/-- A receiver-core-valid strengthening semantically covers the weaker raw
Cartesian conclusion that production antichain pruning removes. -/
theorem ContextValid.of_strengthens (model : TModel D) (core : List FPred)
    {stronger weaker : FCL} (hstrengthens : Strengthens stronger weaker)
    (hstronger : ContextValid model core stronger) :
    ContextValid model core weaker := by
  intro assignment hcore
  exact HoldsAt.of_strengthens model assignment hstrengthens
    (hstronger assignment hcore)

/-- Finite antichain coverage is sufficient for semantic preservation: every
raw Cartesian result remains valid when some retained result strengthens it. -/
theorem coveredResults_contextValid (model : TModel D) (core : List FPred)
    (retained generated : List FCL)
    (hretained : ∀ clause ∈ retained, ContextValid model core clause)
    (hcoverage : ∀ clause ∈ generated,
      ∃ stronger ∈ retained, Strengthens stronger clause) :
    ∀ clause ∈ generated, ContextValid model core clause := by
  intro clause hclause
  obtain ⟨stronger, hstronger, hstrengthens⟩ := hcoverage clause hclause
  exact ContextValid.of_strengthens model core hstrengthens
    (hretained stronger hstronger)

#print axioms predTransfer_sound
#print axioms succHypothesis_valid
#print axioms resolveContextual_sound
#print axioms ContextValid.of_strengthens
#print axioms coveredResults_contextValid

end ContextCalculus.CBInterContext
