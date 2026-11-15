import ContextCalculus.SROIQ.Regular
import ContextCalculus.SRI.FastTy
import Mathlib.Data.Fintype.Sum

/-!
# Regularity of the role hierarchy (stage C3, design section 2)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 2: the OWL 2 structural
specification, section 11.2. `Regular O` is the existence of a strict
partial order `<` on role terms with

* (R1) `R < S ↔ R.flip < S`,
* (R2) `R < S → ¬ S ⊑₁* R`,
* (R3) every chain `[B₁, …, Bₙ] ⊑ S` with `n ≥ 2` is `[S, S] ⊑ S`, or has
  `Bᵢ < S` for all `i`, or `B₁ = S` and `Bᵢ < S` for `i ≥ 2`, or `Bₙ = S`
  and `Bᵢ < S` for `i < n`.

The shape of each chain forces the option (`needOf`), so the least
candidate is the transitive closure `LtC O` of the forced pairs, closed on
the left under `flip`. `regularB` computes it (a stabilising closure over
the finitely many role terms) and checks irreflexivity and R2;
`regularB_iff` says that this is `Regular O`.
-/

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Clause Ontology RoleLe)

variable {n m : Nat}

abbrev RT (m : Nat) := RoleT (Fin m)

/-! ## Role terms form a finite type -/

def rtEquiv (m : Nat) : RT m ≃ Fin m ⊕ Fin m where
  toFun | .pos r => .inl r | .inv r => .inr r
  invFun | .inl r => .pos r | .inr r => .inv r
  left_inv R := by cases R <;> rfl
  right_inv x := by cases x <;> rfl

instance (m : Nat) : Fintype (RT m) := Fintype.ofEquiv _ (rtEquiv m).symm

/-! ## The specification -/

/-- Option (R3) for one chain. -/
def ChainOK (lt : RT m → RT m → Prop) (body : List (RT m)) (S : RT m) : Prop :=
  body = [S, S] ∨ (∀ B ∈ body, lt B S) ∨
    (body.head? = some S ∧ ∀ B ∈ body.tail, lt B S) ∨
    (body.getLast? = some S ∧ ∀ B ∈ body.dropLast, lt B S)

/-- The conditions on the order. -/
structure RegOrder (O : Ontology (Fin n) (Fin m)) (lt : RT m → RT m → Prop) : Prop where
  irrefl : ∀ R, ¬ lt R R
  trans : ∀ R S T, lt R S → lt S T → lt R T
  flip : ∀ R S, lt R S ↔ lt R.flip S
  hier : ∀ R S, lt R S → ¬ RoleLe O S R
  chains : ∀ body S, Clause.chain body S ∈ O → 2 ≤ body.length → ChainOK lt body S

/-- **Regularity** (structural specification, section 11.2). -/
def Regular (O : Ontology (Fin n) (Fin m)) : Prop := ∃ lt, RegOrder O lt

/-! ## The forced pairs -/

/-- The pairs `(Bᵢ, S)` that the shape of a chain forces. -/
def needOf (S : RT m) : List (RT m) → List (RT m × RT m)
  | [] => []
  | [_] => []
  | B₁ :: B₂ :: rest =>
    if B₁ :: B₂ :: rest = [S, S] then []
    else if B₁ = S then (B₂ :: rest).map (·, S)
    else if (B₁ :: B₂ :: rest).getLast? = some S then (B₁ :: B₂ :: rest).dropLast.map (·, S)
    else (B₁ :: B₂ :: rest).map (·, S)

/-- The forced pairs of an ontology, closed on the left under `flip`. -/
def needL (O : Ontology (Fin n) (Fin m)) : List (RT m × RT m) :=
  O.flatMap fun
    | .chain body S => (needOf S body).flatMap fun p => [p, (p.1.flip, p.2)]
    | _ => []

def NeedRel (O : Ontology (Fin n) (Fin m)) (R S : RT m) : Prop := (R, S) ∈ needL O

/-- The least candidate order. -/
def LtC (O : Ontology (Fin n) (Fin m)) : RT m → RT m → Prop := Relation.TransGen (NeedRel O)

theorem mem_needL {O : Ontology (Fin n) (Fin m)} {R S : RT m} :
    NeedRel O R S ↔ ∃ body T, Clause.chain body T ∈ O ∧
      ((R, S) ∈ needOf T body ∨ (R.flip, S) ∈ needOf T body) := by
  unfold NeedRel needL
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨cl, hcl, hp⟩
    cases cl
    case chain body T =>
      simp only [List.mem_flatMap, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hp
      obtain ⟨⟨R', S'⟩, hp, hm⟩ := hp
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨body, T, hcl, Or.inl hp⟩
      · exact ⟨body, T, hcl, Or.inr (by simpa using hp)⟩
    all_goals simp at hp
  · rintro ⟨body, T, hcl, hp | hp⟩
    · exact ⟨_, hcl, List.mem_flatMap.2 ⟨(R, S), hp, by simp⟩⟩
    · exact ⟨_, hcl, List.mem_flatMap.2 ⟨(R.flip, S), hp, by simp⟩⟩

theorem needRel_flip {O : Ontology (Fin n) (Fin m)} {R S : RT m} (h : NeedRel O R S) :
    NeedRel O R.flip S := by
  obtain ⟨body, T, hcl, hp⟩ := mem_needL.1 h
  exact mem_needL.2 ⟨body, T, hcl, by rw [RoleT.flip_flip]; exact hp.symm⟩

theorem ltC_flip {O : Ontology (Fin n) (Fin m)} {R S : RT m} (h : LtC O R S) : LtC O R.flip S := by
  induction h with
  | single h => exact .single (needRel_flip h)
  | tail _ h ih => exact .tail ih h

/-- The second components of the forced pairs of a chain are its head. -/
theorem needOf_snd {S : RT m} : ∀ {body : List (RT m)} {p : RT m × RT m}, p ∈ needOf S body → p.2 = S
  | [], _, h => by simp [needOf] at h
  | [_], _, h => by simp [needOf] at h
  | B₁ :: B₂ :: rest, p, h => by
    simp only [needOf] at h
    split_ifs at h <;> first | (simp at h; done) | (obtain ⟨_, _, rfl⟩ := List.mem_map.1 h; rfl)

/-- The forced pairs follow from any option a valid order satisfies. -/
theorem needOf_lt {lt : RT m → RT m → Prop} (hirr : ∀ R, ¬ lt R R) {S : RT m} :
    ∀ {body : List (RT m)}, 2 ≤ body.length → ChainOK lt body S →
      ∀ p ∈ needOf S body, lt p.1 p.2
  | [], hl, _ => by simp at hl
  | [_], hl, _ => by simp at hl
  | B₁ :: B₂ :: rest, _, hok => by
    intro p hp
    have hlast : (B₁ :: B₂ :: rest).getLast? = some ((B₂ :: rest).getLast (by simp)) := by
      rw [List.getLast?_eq_some_getLast (by simp)]
      simp [List.getLast_cons]
    have hdl : B₁ ∈ (B₁ :: B₂ :: rest).dropLast := by
      rw [List.dropLast_cons_cons]; exact List.mem_cons_self
    have hmemL : (B₂ :: rest).getLast (by simp) ∈ B₁ :: B₂ :: rest :=
      List.mem_cons_of_mem _ (List.getLast_mem _)
    simp only [needOf] at hp
    split_ifs at hp with h1 h2 h3
    · simp at hp
    · -- B₁ = S: only the fourth option
      subst h2
      obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hp
      rcases hok with h | h | ⟨-, h⟩ | ⟨hl, h⟩
      · exact absurd h h1
      · exact absurd (h _ List.mem_cons_self) (hirr _)
      · exact h R hR
      · exact absurd (h _ hdl) (hirr _)
    · -- the last element is `S`: only the fifth option
      obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hp
      rcases hok with h | h | ⟨hh, h⟩ | ⟨-, h⟩
      · exact absurd h h1
      · rw [hlast, Option.some.injEq] at h3
        exact absurd (h _ hmemL) (by rw [h3]; exact hirr _)
      · simp only [List.head?_cons, Option.some.injEq] at hh; exact absurd hh h2
      · exact h R hR
    · obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hp
      rcases hok with h | h | ⟨hh, h⟩ | ⟨hl, h⟩
      · exact absurd h h1
      · exact h R hR
      · simp only [List.head?_cons, Option.some.injEq] at hh; exact absurd hh h2
      · exact absurd hl h3

/-- The forced pairs give the option they were chosen for. -/
theorem chainOK_of_need {lt : RT m → RT m → Prop} {S : RT m} :
    ∀ {body : List (RT m)}, 2 ≤ body.length → (∀ p ∈ needOf S body, lt p.1 p.2) →
      ChainOK lt body S
  | [], hl, _ => by simp at hl
  | [_], hl, _ => by simp at hl
  | B₁ :: B₂ :: rest, _, h => by
    simp only [needOf] at h
    split_ifs at h with h1 h2 h3
    · exact Or.inl h1
    · subst h2
      refine Or.inr (Or.inr (Or.inl ⟨rfl, fun B hB => h (B, B₁) (List.mem_map_of_mem hB)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h3, fun B hB => h (B, S) (List.mem_map_of_mem hB)⟩))
    · exact Or.inr (Or.inl fun B hB => h (B, S) (List.mem_map_of_mem hB))

/-! ## Closure computation -/

section Closure

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Fintype α]

/-- One round: add the successors. -/
def stepF (E : α → Finset α) (A : Finset α) : Finset α := A ∪ A.biUnion E

/-- The closure, after enough rounds to stabilise. -/
def closeF (E : α → Finset α) (A : Finset α) : Finset α := (stepF E)^[Fintype.card α + 1] A

theorem subset_stepF (E : α → Finset α) (A : Finset α) : A ⊆ stepF E A := Finset.subset_union_left

theorem iter_stable {E : α → Finset α} {A : Finset α} {k : Nat}
    (h : (stepF E)^[k + 1] A = (stepF E)^[k] A) : ∀ j, (stepF E)^[k + j] A = (stepF E)^[k] A
  | 0 => rfl
  | j + 1 => by
    rw [show k + (j + 1) = (k + j) + 1 by omega, Function.iterate_succ_apply',
      iter_stable h j, ← Function.iterate_succ_apply' (f := stepF E), h]

theorem card_iter {E : α → Finset α} {A : Finset α} :
    ∀ k, (∃ j < k, (stepF E)^[j + 1] A = (stepF E)^[j] A) ∨ k ≤ ((stepF E)^[k] A).card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rcases card_iter k with ⟨j, hj, h⟩ | hk
    · exact Or.inl ⟨j, by omega, h⟩
    · by_cases hs : (stepF E)^[k + 1] A = (stepF E)^[k] A
      · exact Or.inl ⟨k, by omega, hs⟩
      · right
        have hsub : (stepF E)^[k] A ⊆ (stepF E)^[k + 1] A := by
          rw [Function.iterate_succ_apply']; exact subset_stepF E _
        have hss : (stepF E)^[k] A ⊂ (stepF E)^[k + 1] A :=
          Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h' => hs h'.symm⟩
        have := Finset.card_lt_card hss
        omega

theorem closeF_fix (E : α → Finset α) (A : Finset α) : stepF E (closeF E A) = closeF E A := by
  unfold closeF
  rcases card_iter (E := E) (A := A) (Fintype.card α + 1) with ⟨j, hj, h⟩ | hk
  · have h1 := iter_stable h (Fintype.card α + 1 - j)
    have h2 := iter_stable h (Fintype.card α + 1 - j + 1)
    rw [show j + (Fintype.card α + 1 - j) = Fintype.card α + 1 by omega] at h1
    rw [show j + (Fintype.card α + 1 - j + 1) = Fintype.card α + 1 + 1 by omega,
      Function.iterate_succ_apply'] at h2
    rw [h2, h1]
  · exact absurd (hk.trans (Finset.card_le_univ _)) (by omega)

theorem subset_closeF (E : α → Finset α) (A : Finset α) : A ⊆ closeF E A := by
  unfold closeF
  generalize Fintype.card α + 1 = k
  induction k with
  | zero => exact fun _ h => h
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (subset_stepF E _)

/-- **The closure.** Membership in `closeF E A` is reachability from `A`. -/
theorem mem_closeF {E : α → Finset α} {A : Finset α} {y : α} :
    y ∈ closeF E A ↔ ∃ x ∈ A, Relation.ReflTransGen (fun a b => b ∈ E a) x y := by
  constructor
  · unfold closeF
    generalize Fintype.card α + 1 = k
    induction k generalizing y with
    | zero => intro h; exact ⟨y, h, .refl⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro h
      rcases Finset.mem_union.1 h with h | h
      · exact ih h
      · obtain ⟨z, hz, hy⟩ := Finset.mem_biUnion.1 h
        obtain ⟨x, hx, hp⟩ := ih hz
        exact ⟨x, hx, hp.tail hy⟩
  · rintro ⟨x, hx, hp⟩
    induction hp with
    | refl => exact subset_closeF E A hx
    | tail _ h ih =>
      rw [← closeF_fix]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, ih, h⟩)

end Closure

/-! ## The check -/

section Check

variable (O : Ontology (Fin n) (Fin m))

/-- The direct forced successors of a role term. -/
def needSucc (R : RT m) : Finset (RT m) :=
  ((needL O).filterMap fun p => if p.1 = R then some p.2 else none).toFinset

/-- The role terms strictly above `R` in `LtC O`. -/
def ltAbove (R : RT m) : Finset (RT m) := closeF (needSucc O) (needSucc O R)

/-- `R ⊑₁* S`, computed. -/
def leB (R S : RT m) : Bool := decide (S ∈ SRI.Proc.upFix (SRIQ.sriPart O) R (2 * m + 2) [R])

/-- **The regularity check.** -/
def regularB : Bool :=
  decide (∀ R : RT m, R ∉ ltAbove O R ∧ ∀ S ∈ ltAbove O R, leB O S R = false)

end Check

variable {O : Ontology (Fin n) (Fin m)}

theorem leB_iff {R S : RT m} : leB O R S = true ↔ RoleLe O R S := by
  unfold leB
  rw [decide_eq_true_iff]
  exact SRI.Proc.mem_upFix'

theorem mem_needSucc {R S : RT m} : S ∈ needSucc O R ↔ NeedRel O R S := by
  unfold needSucc NeedRel
  simp only [List.mem_toFinset, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨⟨R', S'⟩, hp, rfl, rfl⟩; exact hp
  · intro h; exact ⟨(R, S), h, rfl, rfl⟩

theorem mem_ltAbove {R S : RT m} : S ∈ ltAbove O R ↔ LtC O R S := by
  unfold ltAbove
  rw [mem_closeF]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [mem_needSucc] at hx
    have : Relation.ReflTransGen (NeedRel O) x S :=
      Relation.ReflTransGen.mono (fun a b h => mem_needSucc.1 h) hp
    exact Relation.TransGen.head'_iff.2 ⟨x, hx, this⟩
  · intro h
    obtain ⟨x, hx, hp⟩ := Relation.TransGen.head'_iff.1 h
    exact ⟨x, mem_needSucc.2 hx, Relation.ReflTransGen.mono (fun a b h => mem_needSucc.2 h) hp⟩

/-- **The check decides regularity.** -/
theorem regularB_iff : regularB O = true ↔ Regular O := by
  unfold regularB
  rw [decide_eq_true_iff]
  simp only [mem_ltAbove, Bool.eq_false_iff, ne_eq, leB_iff]
  constructor
  · intro h
    refine ⟨LtC O, ⟨fun R => (h R).1, fun R S T h1 h2 => h1.trans h2, fun R S => ⟨ltC_flip, ?_⟩,
      fun R S hRS => (h R).2 S hRS, fun body S hcl hl => chainOK_of_need hl fun p hp => ?_⟩⟩
    · intro h'; have := ltC_flip h'; rwa [RoleT.flip_flip] at this
    · rcases p with ⟨R', S'⟩
      have h2 : S' = S := needOf_snd hp
      subst h2
      exact .single (mem_needL.2 ⟨body, _, hcl, Or.inl hp⟩)
  · rintro ⟨lt, hlt⟩
    have hsub : ∀ R S, LtC O R S → lt R S := by
      have h1 : ∀ R S, NeedRel O R S → lt R S := by
        intro R S h
        obtain ⟨body, T, hcl, hp⟩ := mem_needL.1 h
        have hl : 2 ≤ body.length := by
          match body, hp with
          | [], hp => simp [needOf] at hp
          | [_], hp => simp [needOf] at hp
          | _ :: _ :: _, _ => simp
        have hok := needOf_lt hlt.irrefl hl (hlt.chains body T hcl hl)
        rcases hp with hp | hp
        · exact hok _ hp
        · have := hok _ hp
          rw [hlt.flip]; exact this
      intro R S h
      induction h with
      | single h => exact h1 _ _ h
      | tail _ h ih => exact hlt.trans _ _ _ ih (h1 _ _ h)
    intro R
    exact ⟨fun h => hlt.irrefl R (hsub R R h), fun S h => hlt.hier R S (hsub R S h)⟩

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SROIQ.Proc.mem_closeF
#print axioms ContextCalculus.SROIQ.Proc.regularB_iff
