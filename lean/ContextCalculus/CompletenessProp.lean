/-
  ContextCalculus/CompletenessProp.lean
  =====================================
  **Refutational completeness of propositional resolution.**

  The genuine completeness counterpart to the soundness in `Basic.lean`.
  The engine's Hyper rule is clausal resolution; on the function-free
  (propositional) fragment the context structure is irrelevant, so the engine's
  saturation IS propositional resolution.  We prove here, fully and
  `sorry`-free, that propositional resolution refutes every unsatisfiable finite
  clause set:

      `completeness : Unsat S → Derivable S ⊥`.

  With `derivable_sound` this gives **soundness + completeness of the resolution
  core** — exactly the fragment on which the earlier Horn-only reasoner was
  unsound (it deferred disjunctive heads).

  Proof: induction on the number of atoms, Davis-Putnam conditioning on an atom
  `p`, with a lifting lemma pulling a conditioned derivation back to `S`.

  (The full first-order context-calculus completeness — the Herbrand
  canonical-model construction over a saturated context structure — is a far
  larger development and is NOT claimed here.)
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace ContextCalculus.PropRes

variable {Atom : Type*} [DecidableEq Atom]

/-- A propositional clause `body → head`, i.e. `⋁_{a∈neg} ¬a ∨ ⋁_{a∈pos} a`. -/
structure PClause (Atom : Type*) where
  neg : Finset Atom
  pos : Finset Atom
deriving DecidableEq

namespace PClause
/-- Satisfaction: if every body atom is true then some head atom is true. -/
def sat (I : Atom → Prop) (c : PClause Atom) : Prop :=
  (∀ a ∈ c.neg, I a) → (∃ a ∈ c.pos, I a)

/-- The empty clause `⊥`. -/
def bot : PClause Atom := ⟨∅, ∅⟩

theorem not_sat_bot (I : Atom → Prop) : ¬ (bot : PClause Atom).sat I := by
  intro h
  obtain ⟨a, ha, _⟩ := h (by intro a ha; simp [bot] at ha)
  simp [bot] at ha
end PClause

open PClause

/-- The resolvent on atom `a` (`a ∈ c1.pos`, `a ∈ c2.neg`). -/
def resolvent (c1 c2 : PClause Atom) (a : Atom) : PClause Atom :=
  ⟨c1.neg ∪ (c2.neg.erase a), (c1.pos.erase a) ∪ c2.pos⟩

/-- **Resolution is sound.** -/
theorem resolvent_sound (I : Atom → Prop) (c1 c2 : PClause Atom) (a : Atom)
    (h1 : c1.sat I) (h2 : c2.sat I) (ha1 : a ∈ c1.pos) (ha2 : a ∈ c2.neg) :
    (resolvent c1 c2 a).sat I := by
  intro hbody
  have hb1 : ∀ b ∈ c1.neg, I b := by
    intro b hb; exact hbody b (by simp only [resolvent, Finset.mem_union]; exact Or.inl hb)
  obtain ⟨w, hwpos, hIw⟩ := h1 hb1
  by_cases hwa : w = a
  · subst hwa
    have hb2 : ∀ b ∈ c2.neg, I b := by
      intro b hb
      by_cases hba : b = w
      · subst hba; exact hIw
      · exact hbody b (by
          simp only [resolvent, Finset.mem_union, Finset.mem_erase]
          exact Or.inr ⟨hba, hb⟩)
    obtain ⟨v, hvpos, hIv⟩ := h2 hb2
    exact ⟨v, by simp only [resolvent, Finset.mem_union]; exact Or.inr hvpos, hIv⟩
  · exact ⟨w, by
      simp only [resolvent, Finset.mem_union, Finset.mem_erase]
      exact Or.inl ⟨hwa, hwpos⟩, hIw⟩

/-- Resolution derivations from a clause set `S`. -/
inductive Derivable (S : Finset (PClause Atom)) : PClause Atom → Prop where
  | premise {c} : c ∈ S → Derivable S c
  | resolve {c1 c2 a} :
      Derivable S c1 → Derivable S c2 → a ∈ c1.pos → a ∈ c2.neg →
      Derivable S (resolvent c1 c2 a)

/-- **Derivations are sound.** -/
theorem derivable_sound (I : Atom → Prop) (S : Finset (PClause Atom))
    (hS : ∀ c ∈ S, c.sat I) : ∀ {c}, Derivable S c → c.sat I := by
  intro c h
  induction h with
  | premise hc => exact hS _ hc
  | resolve _ _ ha1 ha2 ih1 ih2 => exact resolvent_sound I _ _ _ ih1 ih2 ha1 ha2

/-- Unsatisfiability. -/
def Unsat (S : Finset (PClause Atom)) : Prop := ¬ ∃ I : Atom → Prop, ∀ c ∈ S, c.sat I

/-- The atoms occurring in a clause set. -/
def atoms (S : Finset (PClause Atom)) : Finset Atom :=
  S.biUnion (fun c => c.neg ∪ c.pos)

theorem mem_atoms_of_neg {S : Finset (PClause Atom)} {c : PClause Atom} {a : Atom}
    (hc : c ∈ S) (ha : a ∈ c.neg) : a ∈ atoms S := by
  simp only [atoms, Finset.mem_biUnion]; exact ⟨c, hc, by simp [ha]⟩

theorem mem_atoms_of_pos {S : Finset (PClause Atom)} {c : PClause Atom} {a : Atom}
    (hc : c ∈ S) (ha : a ∈ c.pos) : a ∈ atoms S := by
  simp only [atoms, Finset.mem_biUnion]; exact ⟨c, hc, by simp [ha]⟩

/-- Condition on `p := true`. -/
def condTrue (p : Atom) (S : Finset (PClause Atom)) : Finset (PClause Atom) :=
  (S.filter (fun c => p ∉ c.pos)).image (fun c => ⟨c.neg.erase p, c.pos⟩)

/-- Condition on `p := false`. -/
def condFalse (p : Atom) (S : Finset (PClause Atom)) : Finset (PClause Atom) :=
  (S.filter (fun c => p ∉ c.neg)).image (fun c => ⟨c.neg, c.pos.erase p⟩)

theorem atoms_condTrue_subset (p : Atom) (S : Finset (PClause Atom)) :
    atoms (condTrue p S) ⊆ (atoms S).erase p := by
  intro a ha
  simp only [atoms, condTrue, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at ha
  obtain ⟨c', ⟨c, ⟨hcS, hcp⟩, rfl⟩, hac'⟩ := ha
  simp only [Finset.mem_union, Finset.mem_erase] at hac'
  rw [Finset.mem_erase]
  rcases hac' with ⟨hane, hain⟩ | hain
  · exact ⟨hane, mem_atoms_of_neg hcS hain⟩
  · exact ⟨by rintro rfl; exact hcp hain, mem_atoms_of_pos hcS hain⟩

theorem atoms_condFalse_subset (p : Atom) (S : Finset (PClause Atom)) :
    atoms (condFalse p S) ⊆ (atoms S).erase p := by
  intro a ha
  simp only [atoms, condFalse, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at ha
  obtain ⟨c', ⟨c, ⟨hcS, hcp⟩, rfl⟩, hac'⟩ := ha
  simp only [Finset.mem_union, Finset.mem_erase] at hac'
  rw [Finset.mem_erase]
  rcases hac' with hain | ⟨hane, hain⟩
  · exact ⟨by rintro rfl; exact hcp hain, mem_atoms_of_neg hcS hain⟩
  · exact ⟨hane, mem_atoms_of_pos hcS hain⟩

theorem unsat_condTrue (p : Atom) {S : Finset (PClause Atom)} (h : Unsat S) :
    Unsat (condTrue p S) := by
  rintro ⟨I, hI⟩
  refine h ⟨fun a => if a = p then True else I a, ?_⟩
  intro c hc
  by_cases hcp : p ∈ c.pos
  · intro _; exact ⟨p, hcp, by simp⟩
  · have hc' : (⟨c.neg.erase p, c.pos⟩ : PClause Atom) ∈ condTrue p S := by
      simp only [condTrue, Finset.mem_image, Finset.mem_filter]; exact ⟨c, ⟨hc, hcp⟩, rfl⟩
    have hcsat := hI _ hc'
    intro hbody
    -- hbody : ∀ a ∈ c.neg, extended a ; need ∀ a ∈ c.neg.erase p, I a
    have hb' : ∀ a ∈ c.neg.erase p, I a := by
      intro a ha
      have hane : a ≠ p := Finset.ne_of_mem_erase ha
      have hx := hbody a (Finset.mem_of_mem_erase ha)
      simpa [hane] using hx
    obtain ⟨a, hapos, hIa⟩ := hcsat hb'
    refine ⟨a, hapos, ?_⟩
    have hne : a ≠ p := by rintro rfl; exact hcp hapos
    simpa [hne] using hIa

theorem unsat_condFalse (p : Atom) {S : Finset (PClause Atom)} (h : Unsat S) :
    Unsat (condFalse p S) := by
  rintro ⟨I, hI⟩
  refine h ⟨fun a => if a = p then False else I a, ?_⟩
  intro c hc
  by_cases hcp : p ∈ c.neg
  · intro hbody; exact absurd (hbody p hcp) (by simp)
  · have hc' : (⟨c.neg, c.pos.erase p⟩ : PClause Atom) ∈ condFalse p S := by
      simp only [condFalse, Finset.mem_image, Finset.mem_filter]; exact ⟨c, ⟨hc, hcp⟩, rfl⟩
    have hcsat := hI _ hc'
    intro hbody
    -- hbody : ∀ a ∈ c.neg, extended a (extended p = False); c.neg has no p
    have hb' : ∀ a ∈ c.neg, I a := by
      intro a ha
      have hne : a ≠ p := by rintro rfl; exact hcp ha
      simpa [hne] using hbody a ha
    obtain ⟨a, hapos, hIa⟩ := hcsat hb'
    have hane : a ≠ p := Finset.ne_of_mem_erase hapos
    exact ⟨a, Finset.mem_of_mem_erase hapos, by simpa [hane] using hIa⟩

/-- Invariant: clauses derivable in `condTrue p S` never have `p` in the head. -/
theorem condTrue_pos_no_p (p : Atom) (S : Finset (PClause Atom)) {D : PClause Atom}
    (h : Derivable (condTrue p S) D) : p ∉ D.pos := by
  induction h with
  | @premise c hc =>
    simp only [condTrue, Finset.mem_image, Finset.mem_filter] at hc
    obtain ⟨c0, ⟨_, hc0p⟩, rfl⟩ := hc; exact hc0p
  | @resolve c1 c2 a _ _ _ _ ih1 ih2 =>
    simp only [resolvent, Finset.mem_union, Finset.mem_erase, not_or]
    exact ⟨fun h => ih1 h.2, ih2⟩

/-- Invariant: clauses derivable in `condFalse p S` never have `p` in the body. -/
theorem condFalse_neg_no_p (p : Atom) (S : Finset (PClause Atom)) {D : PClause Atom}
    (h : Derivable (condFalse p S) D) : p ∉ D.neg := by
  induction h with
  | @premise c hc =>
    simp only [condFalse, Finset.mem_image, Finset.mem_filter] at hc
    obtain ⟨c0, ⟨_, hc0p⟩, rfl⟩ := hc; exact hc0p
  | @resolve c1 c2 a _ _ _ _ ih1 ih2 =>
    simp only [resolvent, Finset.mem_union, Finset.mem_erase, not_or]
    exact ⟨ih1, fun h => ih2 h.2⟩

/-- **Lifting (true case).** -/
theorem lift_true (p : Atom) (S : Finset (PClause Atom)) {D : PClause Atom}
    (h : Derivable (condTrue p S) D) :
    Derivable S D ∨ Derivable S ⟨insert p D.neg, D.pos⟩ := by
  induction h with
  | @premise c hc =>
    simp only [condTrue, Finset.mem_image, Finset.mem_filter] at hc
    obtain ⟨c0, ⟨hc0S, _⟩, rfl⟩ := hc
    by_cases hp : p ∈ c0.neg
    · right; rw [Finset.insert_erase hp]; exact Derivable.premise hc0S
    · left; rw [Finset.erase_eq_of_notMem hp]; exact Derivable.premise hc0S
  | @resolve c1 c2 a d1 d2 ha1 ha2 ih1 ih2 =>
    have hane : a ≠ p := fun h => (condTrue_pos_no_p p S d1) (h ▸ ha1)
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · left; exact Derivable.resolve h1 h2 ha1 ha2
    · right
      have ha2' : a ∈ insert p c2.neg := Finset.mem_insert_of_mem ha2
      have hd := Derivable.resolve h1 h2 ha1 ha2'
      have heq : (⟨insert p (resolvent c1 c2 a).neg, (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent c1 ⟨insert p c2.neg, c2.pos⟩ a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd
    · right
      have hd := Derivable.resolve h1 h2 ha1 ha2
      have heq : (⟨insert p (resolvent c1 c2 a).neg, (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent ⟨insert p c1.neg, c1.pos⟩ c2 a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd
    · right
      have ha2' : a ∈ insert p c2.neg := Finset.mem_insert_of_mem ha2
      have hd := Derivable.resolve h1 h2 ha1 ha2'
      have heq : (⟨insert p (resolvent c1 c2 a).neg, (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent ⟨insert p c1.neg, c1.pos⟩ ⟨insert p c2.neg, c2.pos⟩ a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd

/-- **Lifting (false case).** -/
theorem lift_false (p : Atom) (S : Finset (PClause Atom)) {D : PClause Atom}
    (h : Derivable (condFalse p S) D) :
    Derivable S D ∨ Derivable S ⟨D.neg, insert p D.pos⟩ := by
  induction h with
  | @premise c hc =>
    simp only [condFalse, Finset.mem_image, Finset.mem_filter] at hc
    obtain ⟨c0, ⟨hc0S, _⟩, rfl⟩ := hc
    by_cases hp : p ∈ c0.pos
    · right; rw [Finset.insert_erase hp]; exact Derivable.premise hc0S
    · left; rw [Finset.erase_eq_of_notMem hp]; exact Derivable.premise hc0S
  | @resolve c1 c2 a d1 d2 ha1 ha2 ih1 ih2 =>
    have hane : a ≠ p := fun h => (condFalse_neg_no_p p S d2) (h ▸ ha2)
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · left; exact Derivable.resolve h1 h2 ha1 ha2
    · right
      have hd := Derivable.resolve h1 h2 ha1 ha2
      have heq : (⟨(resolvent c1 c2 a).neg, insert p (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent c1 ⟨c2.neg, insert p c2.pos⟩ a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd
    · right
      have ha1' : a ∈ insert p c1.pos := Finset.mem_insert_of_mem ha1
      have hd := Derivable.resolve h1 h2 ha1' ha2
      have heq : (⟨(resolvent c1 c2 a).neg, insert p (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent ⟨c1.neg, insert p c1.pos⟩ c2 a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd
    · right
      have ha1' : a ∈ insert p c1.pos := Finset.mem_insert_of_mem ha1
      have hd := Derivable.resolve h1 h2 ha1' ha2
      have heq : (⟨(resolvent c1 c2 a).neg, insert p (resolvent c1 c2 a).pos⟩ : PClause Atom)
                  = resolvent ⟨c1.neg, insert p c1.pos⟩ ⟨c2.neg, insert p c2.pos⟩ a := by
        simp only [resolvent]
        congr 1 <;>
          first
            | rfl
            | (ext b; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase]; aesop)
      exact heq ▸ hd

/-- Helper: a clause whose atoms are all outside `atoms S` … here, with no atoms,
    a clause in `S` must be `⊥`. -/
theorem eq_bot_of_no_atoms {S : Finset (PClause Atom)} (h : atoms S = ∅)
    {c : PClause Atom} (hc : c ∈ S) : c = PClause.bot := by
  have hsubn : c.neg ⊆ atoms S := fun a ha => mem_atoms_of_neg hc ha
  have hsubp : c.pos ⊆ atoms S := fun a ha => mem_atoms_of_pos hc ha
  have hn : c.neg = ∅ := Finset.subset_empty.mp (h ▸ hsubn)
  have hp : c.pos = ∅ := Finset.subset_empty.mp (h ▸ hsubp)
  cases c; simp_all [PClause.bot]

/-- **Refutational completeness of propositional resolution.** -/
theorem completeness (S : Finset (PClause Atom)) (h : Unsat S) :
    Derivable S PClause.bot := by
  -- strong induction on the number of atoms
  generalize hn : (atoms S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · -- no atoms: some clause is ⊥
      rw [hz] at hn
      have hempty : atoms S = ∅ := Finset.card_eq_zero.mp hn
      have hSne : S.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact h ⟨fun _ => True, by intro c hc; rw [hne] at hc; simp at hc⟩
      obtain ⟨c, hc⟩ := hSne
      have : c = PClause.bot := eq_bot_of_no_atoms hempty hc
      exact this ▸ Derivable.premise hc
    · -- pick an atom p
      have hne : (atoms S).Nonempty := by
        rw [← Finset.card_pos, hn]; exact hpos
      obtain ⟨p, hp⟩ := hne
      -- conditioned sets are unsat with strictly fewer atoms
      have hcardT : (atoms (condTrue p S)).card < n := by
        calc (atoms (condTrue p S)).card
            ≤ ((atoms S).erase p).card := Finset.card_le_card (atoms_condTrue_subset p S)
          _ = (atoms S).card - 1 := Finset.card_erase_of_mem hp
          _ < n := by rw [hn]; omega
      have hcardF : (atoms (condFalse p S)).card < n := by
        calc (atoms (condFalse p S)).card
            ≤ ((atoms S).erase p).card := Finset.card_le_card (atoms_condFalse_subset p S)
          _ = (atoms S).card - 1 := Finset.card_erase_of_mem hp
          _ < n := by rw [hn]; omega
      have hdT : Derivable (condTrue p S) PClause.bot :=
        ih _ hcardT (condTrue p S) (unsat_condTrue p h) rfl
      have hdF : Derivable (condFalse p S) PClause.bot :=
        ih _ hcardF (condFalse p S) (unsat_condFalse p h) rfl
      rcases lift_true p S hdT with hT | hT
      · exact hT
      rcases lift_false p S hdF with hF | hF
      · exact hF
      -- hT : Derivable S ⟨{p}, ∅⟩ , hF : Derivable S ⟨∅, {p}⟩  → resolve to ⊥
      have hTn : (⟨insert p (PClause.bot).neg, (PClause.bot).pos⟩ : PClause Atom)
                  = ⟨{p}, ∅⟩ := by simp [PClause.bot]
      have hFn : (⟨(PClause.bot).neg, insert p (PClause.bot).pos⟩ : PClause Atom)
                  = ⟨∅, {p}⟩ := by simp [PClause.bot]
      rw [hTn] at hT; rw [hFn] at hF
      have hres := Derivable.resolve hF hT (by simp : p ∈ ({p} : Finset Atom)) (by simp : p ∈ ({p} : Finset Atom))
      have : resolvent (⟨∅, {p}⟩ : PClause Atom) ⟨{p}, ∅⟩ p = PClause.bot := by
        simp [resolvent, PClause.bot]
      exact this ▸ hres

end ContextCalculus.PropRes
