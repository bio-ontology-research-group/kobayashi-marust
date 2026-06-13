/-
  ContextCalculus/CompletenessOrdered.lean
  ========================================
  **Refutational completeness of *ordered* ground resolution.**

  `CompletenessProp.lean` certifies *unrestricted* propositional resolution
  (resolve on any atom) — which is what licenses the engine's default
  "incomparable, fire on every disjunct" Hyper rule.  That is complete but it is
  the source of the live-disjunction blow-up: incomparable 2–3-literal
  disjunctions all fire and the worked-off set grows without converging.

  The engine's `KM_ORDERED_ALL` mode imposes a total order on same-term concept
  literals and fires Hyper only on the ordering-MAXIMAL disjunct (ordered
  resolution).  This file certifies that the ordering restriction does **not**
  cost completeness: ordered ground resolution still refutes every unsatisfiable
  clause set.

      `ordered_completeness : Unsat S → S derives ⊥ by ordered resolution`.

  Proof: the Bachmair–Ganzinger candidate-model construction.  Because clauses
  here are *finsets* of literals, factoring (`B ∨ B = B`) is automatic, so
  ordered resolution alone suffices.  We build a partial interpretation by
  well-founded recursion on the atom order: an atom is true iff some clause
  *produces* it (it is the strictly-maximal positive literal of a clause whose
  smaller part is already falsified).  A saturated clause set with no empty
  clause is satisfied by this model, so unsatisfiable saturated sets contain ⊥.

  Everything here is `sorry`-free.  Combined with the per-run soundness
  certificate (`CheckerTerm`) — resolution is sound for *any* literal selection
  — this certifies the ordered-resolution engine is sound and complete on the
  clausal core, exactly as the unrestricted version was.
-/
import ContextCalculus.CompletenessProp
import Mathlib.Order.WellFoundedSet

namespace ContextCalculus.OrdRes

open ContextCalculus.PropRes

set_option linter.unusedSectionVars false

variable {Atom : Type*} [LinearOrder Atom] [Fintype Atom] [DecidableEq Atom]

/-- All atoms occurring in a clause (negative or positive). -/
def lits (c : PClause Atom) : Finset Atom := c.neg ∪ c.pos

theorem mem_lits {c : PClause Atom} {a : Atom} : a ∈ lits c ↔ a ∈ c.neg ∨ a ∈ c.pos := by
  simp [lits, Finset.mem_union]

/-- `a` is the **strictly maximal positive** literal of `c`: it occurs
    positively, not negatively, and every other literal of `c` is strictly
    smaller.  (A productive clause's distinguished literal.) -/
def strictMaxPos (c : PClause Atom) (a : Atom) : Prop :=
  a ∈ c.pos ∧ a ∉ c.neg ∧ ∀ b ∈ lits c, b ≠ a → b < a

/-- The well-founded `<` on a finite linear order. -/
instance : WellFoundedLT Atom := Finite.to_wellFoundedLT

/-- **Candidate model** for a clause set `S` (Bachmair–Ganzinger).  An atom `a`
    is true iff some clause of `S` *produces* it: `a` is the strictly-maximal
    positive literal of the clause, every negative literal of the clause is
    already true, and every other positive literal is already false.  The
    recursion is well-founded because all those "already" references are to
    atoms strictly below `a` (forced by `strictMaxPos`). -/
def Itrue (S : Finset (PClause Atom)) : Atom → Prop :=
  wellFounded_lt.fix fun a ih =>
    ∃ c ∈ S, ∃ hsm : strictMaxPos c a,
      (∀ b (hb : b ∈ c.neg), ih b (hsm.2.2 b (mem_lits.2 (Or.inl hb))
          (by rintro rfl; exact hsm.2.1 hb))) ∧
      (∀ b (hb : b ∈ c.pos) (hba : b ≠ a),
          ¬ ih b (hsm.2.2 b (mem_lits.2 (Or.inr hb)) hba))

/-- The defining fixpoint equation of `Itrue`, with the recursive references
    rewritten back to `Itrue` itself. -/
theorem Itrue_def (S : Finset (PClause Atom)) (a : Atom) :
    Itrue S a ↔ ∃ c ∈ S, strictMaxPos c a ∧
      (∀ b ∈ c.neg, Itrue S b) ∧ (∀ b ∈ c.pos, b ≠ a → ¬ Itrue S b) := by
  unfold Itrue
  rw [wellFounded_lt.fix_eq]
  constructor
  · rintro ⟨c, hc, hsm, hneg, hpos⟩
    exact ⟨c, hc, hsm, fun b hb => hneg b hb, fun b hb hba => hpos b hb hba⟩
  · rintro ⟨c, hc, hsm, hneg, hpos⟩
    exact ⟨c, hc, hsm, fun b hb => hneg b hb, fun b hb hba => hpos b hb hba⟩

/-- A clause with no literals is the empty clause `⊥`. -/
theorem lits_eq_empty_bot (q : PClause Atom) (hq : lits q = ∅) : q = PClause.bot := by
  have hn : q.neg = ∅ :=
    Finset.subset_empty.mp (by rw [← hq]; intro y hy; exact mem_lits.mpr (Or.inl hy))
  have hp : q.pos = ∅ :=
    Finset.subset_empty.mp (by rw [← hq]; intro y hy; exact mem_lits.mpr (Or.inr hy))
  cases q; simp_all [PClause.bot]

/-- A clause set is **closed under ordered resolution** when, for every ordered
    pair — `a` strictly maximal positive in `d`, and `a` maximal (and negative)
    in `c` — the resolvent is again in the set.  This is the saturation
    invariant. -/
def Closed (S : Finset (PClause Atom)) : Prop :=
  ∀ d ∈ S, ∀ c ∈ S, ∀ a : Atom,
    strictMaxPos d a → a ∈ c.neg → (∀ b ∈ lits c, b ≤ a) →
    PropRes.resolvent d c a ∈ S

/-- **Model correctness (Bachmair–Ganzinger).**  A clause set closed under
    ordered resolution and not containing `⊥` is satisfied by its candidate
    model `Itrue`.  Proof by well-founded induction on the maximal atom of a
    clause: if a clause were false, either it would *produce* its strictly
    maximal positive atom (making that atom true — contradiction), or its
    maximal atom is negative and already produced by some clause `d`; the
    ordered resolvent of `d` and the clause is then in `S`, is also false, and
    has a strictly smaller maximal atom — contradicting the induction
    hypothesis (or it is `⊥`, excluded). -/
theorem model_correct (S : Finset (PClause Atom))
    (hcl : Closed S) (hbot : PClause.bot ∉ S) :
    ∀ c ∈ S, c.sat (Itrue S) := by
  have key : ∀ a : Atom, ∀ c ∈ S, (∀ b ∈ lits c, b ≤ a) → a ∈ lits c → c.sat (Itrue S) := by
    intro a0
    refine wellFounded_lt.induction
      (C := fun a => ∀ c ∈ S, (∀ b ∈ lits c, b ≤ a) → a ∈ lits c → c.sat (Itrue S)) a0 ?_
    intro a ih c hc hub hmem hbody
    by_contra hcon
    push_neg at hcon
    by_cases hap : a ∈ c.pos
    · by_cases han : a ∈ c.neg
      · exact (hcon a hap) (hbody a han)
      · have hsmp : strictMaxPos c a :=
          ⟨hap, han, fun b hb hne => lt_of_le_of_ne (hub b hb) hne⟩
        have hpa : Itrue S a :=
          (Itrue_def S a).mpr ⟨c, hc, hsmp, hbody, fun b hb hne => hcon b hb⟩
        exact (hcon a hap) hpa
    · have han : a ∈ c.neg := by
        rcases mem_lits.mp hmem with h | h
        · exact h
        · exact absurd h hap
      have hIa : Itrue S a := hbody a han
      obtain ⟨d, hd, hsmpd, hdneg, hdpos⟩ := (Itrue_def S a).mp hIa
      set R : PClause Atom := PropRes.resolvent d c a with hRdef
      have hRneg : R.neg = d.neg ∪ c.neg.erase a := rfl
      have hRpos : R.pos = d.pos.erase a ∪ c.pos := rfl
      have hrS : R ∈ S := hcl d hd c hc a hsmpd han hub
      have hrneg : ∀ x ∈ R.neg, Itrue S x := by
        intro x hx
        rw [hRneg, Finset.mem_union] at hx
        rcases hx with h | h
        · exact hdneg x h
        · exact hbody x (Finset.mem_of_mem_erase h)
      have hrpos : ∀ x ∈ R.pos, ¬ Itrue S x := by
        intro x hx
        rw [hRpos, Finset.mem_union] at hx
        rcases hx with h | h
        · exact hdpos x (Finset.mem_of_mem_erase h) (Finset.ne_of_mem_erase h)
        · exact hcon x h
      by_cases hrbot : R = PClause.bot
      · exact hbot (hrbot ▸ hrS)
      · have hrne : (lits R).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro he
          exact hrbot (lits_eq_empty_bot _ he)
        have hlt : ∀ b ∈ lits R, b < a := by
          intro b hb
          rcases mem_lits.mp hb with h | h
          · rw [hRneg, Finset.mem_union] at h
            rcases h with h | h
            · exact hsmpd.2.2 b (mem_lits.mpr (Or.inl h)) (by rintro rfl; exact hsmpd.2.1 h)
            · exact lt_of_le_of_ne (hub b (mem_lits.mpr (Or.inl (Finset.mem_of_mem_erase h))))
                (Finset.ne_of_mem_erase h)
          · rw [hRpos, Finset.mem_union] at h
            rcases h with h | h
            · exact hsmpd.2.2 b (mem_lits.mpr (Or.inr (Finset.mem_of_mem_erase h)))
                (Finset.ne_of_mem_erase h)
            · exact lt_of_le_of_ne (hub b (mem_lits.mpr (Or.inr h))) (by rintro rfl; exact hap h)
        have ha'mem : (lits R).max' hrne ∈ lits R := Finset.max'_mem _ hrne
        have ha'lt : (lits R).max' hrne < a := hlt _ ha'mem
        have hrsat : R.sat (Itrue S) :=
          ih _ ha'lt R hrS (fun b hb => Finset.le_max' _ b hb) ha'mem
        obtain ⟨x, hxpos, hIx⟩ := hrsat hrneg
        exact (hrpos x hxpos) hIx
  intro c hc
  have hne : (lits c).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact hbot ((lits_eq_empty_bot c he) ▸ hc)
  exact key ((lits c).max' hne) c hc (fun b hb => Finset.le_max' _ b hb) (Finset.max'_mem _ hne)

/-- **Refutational completeness of ordered resolution.**  A clause set closed
    under ordered resolution that is unsatisfiable must contain the empty clause
    `⊥`.  Equivalently: ordered saturation of an unsatisfiable set derives `⊥`,
    so restricting resolution to ordering-maximal literals costs no completeness.
    This is the ordered counterpart of `CompletenessProp.completeness` (which
    certifies *unrestricted* resolution). -/
theorem ordered_completeness (S : Finset (PClause Atom))
    (hcl : Closed S) (hunsat : Unsat S) : PClause.bot ∈ S := by
  by_contra h
  exact hunsat ⟨Itrue S, model_correct S hcl h⟩

/-- **Ordered resolution is satisfiability-preserving**, in model form: a
    closed set without `⊥` has an explicit model (the candidate model). -/
theorem ordered_model_exists (S : Finset (PClause Atom))
    (hcl : Closed S) (hbot : PClause.bot ∉ S) :
    ∃ I : Atom → Prop, ∀ c ∈ S, c.sat I :=
  ⟨Itrue S, model_correct S hcl hbot⟩

end ContextCalculus.OrdRes
