import ContextCalculus.CompletenessOrdered

/-!
# Ordered ground resolution completeness modulo subsumption

Production KM stores an antichain: an inferred resolvent may be discarded when
an already retained clause strengthens it.  The standard ordered-resolution
theorem requires the resolvent itself.  This file proves the matching theorem
for closure modulo that redundancy relation.
-/

namespace ContextCalculus.OrdResModulo

open ContextCalculus.PropRes ContextCalculus.OrdRes

variable {Atom : Type*} [LinearOrder Atom] [WellFoundedLT Atom] [DecidableEq Atom]

def Strengthens (stronger weaker : PClause Atom) : Prop :=
  stronger.neg ⊆ weaker.neg ∧ stronger.pos ⊆ weaker.pos

def ClosedModulo (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom,
    strictMaxPos d a → a ∈ c.neg → (∀ b ∈ lits c, b ≤ a) →
    ∃ retained ∈ S, Strengthens retained (PropRes.resolvent d c a)

/-- A propositional clause is tautological when one atom occurs with both
polarities. Such a resolvent requires no retained representative. -/
def Tautological (clause : PClause Atom) : Prop :=
  ∃ atom, atom ∈ clause.neg ∧ atom ∈ clause.pos

/-- Closure modulo production redundancy and tautology deletion. This is the
exact closure contract implemented by KM's generated-head normalizer. -/
def ClosedModuloTautology (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom,
    strictMaxPos d a → a ∈ c.neg → (∀ b ∈ lits c, b ≤ a) →
    Tautological (PropRes.resolvent d c a) ∨
      ∃ retained ∈ S, Strengthens retained (PropRes.resolvent d c a)

theorem sat_of_strengthens (I : Atom → Prop) {stronger weaker : PClause Atom}
    (hstrengthens : Strengthens stronger weaker) (hstronger : stronger.sat I) :
    weaker.sat I := by
  intro hnegative
  have hstrongNegative : ∀ atom ∈ stronger.neg, I atom := by
    intro atom hatom
    exact hnegative atom (hstrengthens.1 hatom)
  obtain ⟨atom, hatom, htrue⟩ := hstronger hstrongNegative
  exact ⟨atom, hstrengthens.2 hatom, htrue⟩

theorem model_correct_of_closedModuloTautology (S : Finset (PClause Atom))
    (hclosed : ClosedModuloTautology S) (hbot : PClause.bot ∉ S) :
    ∀ clause ∈ S, clause.sat (Itrue S) := by
  have key : ∀ a : Atom, ∀ clause ∈ S,
      (∀ b ∈ lits clause, b ≤ a) → a ∈ lits clause →
      clause.sat (Itrue S) := by
    intro a0
    refine wellFounded_lt.induction
      (C := fun a => ∀ clause ∈ S,
        (∀ b ∈ lits clause, b ≤ a) → a ∈ lits clause →
        clause.sat (Itrue S)) a0 ?_
    intro a ih clause hclause hub hmem hnegative
    by_contra hfalse
    push_neg at hfalse
    by_cases hapos : a ∈ clause.pos
    · by_cases haneg : a ∈ clause.neg
      · exact (hfalse a hapos) (hnegative a haneg)
      · have hmax : strictMaxPos clause a :=
          ⟨hapos, haneg, fun b hb hne => lt_of_le_of_ne (hub b hb) hne⟩
        have htrue : Itrue S a := (Itrue_def S a).mpr
          ⟨clause, hclause, hmax, hnegative,
            fun b hb hne => hfalse b hb⟩
        exact (hfalse a hapos) htrue
    · have haneg : a ∈ clause.neg := by
        rcases mem_lits.mp hmem with h | h
        · exact h
        · exact absurd h hapos
      have htrue : Itrue S a := hnegative a haneg
      obtain ⟨producer, hproducer, hproducerMax, hproducerNeg,
          hproducerPos⟩ := (Itrue_def S a).mp htrue
      let resolvent := PropRes.resolvent producer clause a
      have hresNeg : ∀ atom ∈ resolvent.neg, Itrue S atom := by
        intro atom hatom
        change atom ∈ producer.neg ∪ clause.neg.erase a at hatom
        rcases Finset.mem_union.mp hatom with h | h
        · exact hproducerNeg atom h
        · exact hnegative atom (Finset.mem_of_mem_erase h)
      have hresPos : ∀ atom ∈ resolvent.pos, ¬ Itrue S atom := by
        intro atom hatom
        change atom ∈ producer.pos.erase a ∪ clause.pos at hatom
        rcases Finset.mem_union.mp hatom with h | h
        · exact hproducerPos atom (Finset.mem_of_mem_erase h)
            (Finset.ne_of_mem_erase h)
        · exact hfalse atom h
      rcases hclosed producer hproducer clause hclause a hproducerMax haneg hub with
        htautological | ⟨retained, hretained, hstrengthens⟩
      · obtain ⟨atom, hnegativeAtom, hpositiveAtom⟩ := htautological
        exact (hresPos atom hpositiveAtom) (hresNeg atom hnegativeAtom)
      · have hretainedNeg : ∀ atom ∈ retained.neg, Itrue S atom := by
          intro atom hatom
          exact hresNeg atom (hstrengthens.1 hatom)
        have hretainedPos : ∀ atom ∈ retained.pos, ¬ Itrue S atom := by
          intro atom hatom
          exact hresPos atom (hstrengthens.2 hatom)
        by_cases hretainedBot : retained = PClause.bot
        · exact hbot (hretainedBot ▸ hretained)
        · have hnonempty : (lits retained).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hempty
            exact hretainedBot (lits_eq_empty_bot retained hempty)
          have hresLt : ∀ b ∈ lits resolvent, b < a := by
            intro b hb
            rcases mem_lits.mp hb with h | h
            · change b ∈ producer.neg ∪ clause.neg.erase a at h
              rcases Finset.mem_union.mp h with h | h
              · exact hproducerMax.2.2 b (mem_lits.mpr (Or.inl h))
                  (fun hba => hproducerMax.2.1 (hba ▸ h))
              · exact lt_of_le_of_ne
                  (hub b (mem_lits.mpr (Or.inl (Finset.mem_of_mem_erase h))))
                  (Finset.ne_of_mem_erase h)
            · change b ∈ producer.pos.erase a ∪ clause.pos at h
              rcases Finset.mem_union.mp h with h | h
              · exact hproducerMax.2.2 b
                  (mem_lits.mpr (Or.inr (Finset.mem_of_mem_erase h)))
                  (Finset.ne_of_mem_erase h)
              · exact lt_of_le_of_ne (hub b (mem_lits.mpr (Or.inr h)))
                  (fun hba => hapos (hba ▸ h))
          have hretainedLt : ∀ b ∈ lits retained, b < a := by
            intro b hb
            apply hresLt b
            rcases mem_lits.mp hb with h | h
            · exact mem_lits.mpr (Or.inl (hstrengthens.1 h))
            · exact mem_lits.mpr (Or.inr (hstrengthens.2 h))
          have hmaxMem : (lits retained).max' hnonempty ∈ lits retained :=
            Finset.max'_mem _ hnonempty
          have hmaxLt : (lits retained).max' hnonempty < a :=
            hretainedLt _ hmaxMem
          have hsat := ih _ hmaxLt retained hretained
            (fun b hb => Finset.le_max' _ b hb) hmaxMem hretainedNeg
          obtain ⟨atom, hatom, htrue⟩ := hsat
          exact (hretainedPos atom hatom) htrue
  intro clause hclause
  have hnonempty : (lits clause).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hbot ((lits_eq_empty_bot clause hempty) ▸ hclause)
  exact key ((lits clause).max' hnonempty) clause hclause
    (fun b hb => Finset.le_max' _ b hb) (Finset.max'_mem _ hnonempty)

theorem model_correct (S : Finset (PClause Atom))
    (hclosed : ClosedModulo S) (hbot : PClause.bot ∉ S) :
    ∀ clause ∈ S, clause.sat (Itrue S) :=
  model_correct_of_closedModuloTautology S
    (by
      intro producer hproducer clause hclause atom hmax hnegative hub
      exact Or.inr
        (hclosed producer hproducer clause hclause atom hmax hnegative hub))
    hbot

theorem ordered_model_exists_of_closedModuloTautology
    (S : Finset (PClause Atom))
    (hclosed : ClosedModuloTautology S) (hbot : PClause.bot ∉ S) :
    ∃ interpretation : Atom → Prop,
      ∀ clause ∈ S, clause.sat interpretation :=
  ⟨Itrue S, model_correct_of_closedModuloTautology S hclosed hbot⟩

theorem ordered_model_exists (S : Finset (PClause Atom))
    (hclosed : ClosedModulo S) (hbot : PClause.bot ∉ S) :
    ∃ interpretation : Atom → Prop,
      ∀ clause ∈ S, clause.sat interpretation :=
  ⟨Itrue S, model_correct S hclosed hbot⟩

theorem ordered_completeness (S : Finset (PClause Atom))
    (hclosed : ClosedModulo S) (hunsat : Unsat S) :
    PClause.bot ∈ S := by
  by_contra hbot
  exact hunsat ⟨Itrue S, model_correct S hclosed hbot⟩

#print axioms model_correct_of_closedModuloTautology
#print axioms model_correct
#print axioms ordered_model_exists_of_closedModuloTautology
#print axioms ordered_model_exists
#print axioms ordered_completeness

end ContextCalculus.OrdResModulo
