import ContextCalculus.SRI.GoodTypes
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

/-!
# The v1.6.3 decision procedure for ALCHI (plan, section 2b, Steps 2 and 3)

Concepts are `Fin n`, roles `Fin m`. A record `(K, A, t)` is a context
seed `K`, an augment set `A` and a closed type `t` from
`branches (K ∪ A)`. `Gstar` is the least set of records closed under the
root, child and augment rules; `alive` is its greatest self-realising
part. `a ⊑ b` holds iff every alive type that contains `a` contains `b`.

This file gives a direct, unoptimised computation: `Gstar` iterates all
rules until nothing new appears. Soundness and completeness use only
that `Gstar` is closed under the rules and that its types are closed, so
a faster worklist can replace `Gstar` later with a proof of those two
facts.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat}

abbrev Ty (n : Nat) := Finset (Fin n)
abbrev RT (m : Nat) := RoleT (Fin m)

section Defs

variable (O : Ontology (Fin n) (Fin m))

/-! ## Role closure -/

/-- Inclusion steps `R ⊑ S` from chains of length one, and their flips. -/
def stepPairs : List (RT m × RT m) :=
  let base := O.filterMap fun
    | .chain [R] S => some (R, S)
    | _ => none
  base ++ base.map fun p => (p.1.flip, p.2.flip)

def upStep (L : List (RT m)) : List (RT m) :=
  (L ++ (stepPairs O).filterMap fun p => if p.1 ∈ L then some p.2 else none).dedup

/-- The super-roles of `R` (there are at most `2m` role terms). -/
def roleUp (R : RT m) : List (RT m) :=
  (upStep O)^[2 * m + 1] [R]

/-! ## Universal propagation -/

def alls : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .allRight a S c => some (a, S, c)
    | _ => none

/-- Names an `R`-successor of `t` must contain. -/
def fwd (t : Ty n) (R : RT m) : Ty n :=
  (((alls O).filter fun q => decide (q.1 ∈ t) && decide (q.2.1 ∈ roleUp O R)).map
    fun q => q.2.2).toFinset

/-- Names an `R`-predecessor of `s` must contain. -/
def back (s : Ty n) (R : RT m) : Ty n :=
  (((alls O).filter fun q => decide (q.1 ∈ s) && decide (q.2.1 ∈ roleUp O R.flip)).map
    fun q => q.2.2).toFinset

def exs : List (Fin n × RT m × Fin n) :=
  O.filterMap fun
    | .exRight a R b => some (a, R, b)
    | _ => none

/-- The existential demands a type triggers. -/
def demands (t : Ty n) : List (Fin n × RT m × Fin n) :=
  (exs O).filter fun d => decide (d.1 ∈ t)

/-! ## Branches -/

def gcis : List (List (Fin n) × List (Fin n)) :=
  O.filterMap fun
    | .gci body head => some (body, head)
    | _ => none

/-- The head parts a processed gci may add: subsets `Y` of the head with
`Y ∪ (head ∩ cur)` nonempty. An empty head gives no choice (a clash). -/
def choices (head : List (Fin n)) (cur : Ty n) : List (Ty n) :=
  ((head.sublists.map List.toFinset).filter fun Y =>
    decide (Y ∪ (head.toFinset ∩ cur)).Nonempty).dedup

/-- Process the first unprocessed gci whose body holds, branching over
`choices`; stop when none is left. `fuel` bounds the number of gcis. -/
def branchesAux : Nat → Ty n → List Nat → List (Ty n)
  | 0, cur, _ => [cur]
  | fuel + 1, cur, done =>
      match ((gcis O).zipIdx).find? (fun q =>
          decide (q.2 ∉ done) && q.1.1.all (fun a => decide (a ∈ cur))) with
      | none => [cur]
      | some q => (choices q.1.2 cur).flatMap fun Y =>
          branchesAux fuel (cur ∪ Y) (q.2 :: done)

def branches (σ : Ty n) : List (Ty n) :=
  branchesAux O ((gcis O).length + 1) σ []

/-! ## Records and the candidate set -/

structure Rec (n : Nat) where
  K : Ty n
  A : Ty n
  t : Ty n
deriving DecidableEq

def rootRecs (req : List (Fin n)) : Finset (Rec n) :=
  (req.flatMap fun a => (branches O {a}).map fun t => (⟨{a}, ∅, t⟩ : Rec n)).toFinset

def childRecs (G : Finset (Rec n)) : Finset (Rec n) :=
  G.biUnion fun r => ((demands O r.t).flatMap fun d =>
    let K := insert d.2.2 (fwd O r.t d.2.1)
    (branches O K).map fun s => (⟨K, ∅, s⟩ : Rec n)).toFinset

def augRecs (G : Finset (Rec n)) : Finset (Rec n) :=
  G.biUnion fun r => (demands O r.t).toFinset.biUnion fun d =>
    (G.filter fun r' => d.2.2 ∈ r'.K ∧ r'.K ⊆ insert d.2.2 (fwd O r.t d.2.1)).biUnion
      fun r' =>
        let A := r.A ∪ back O r'.t d.2.1
        ((branches O (r.K ∪ A)).map fun t' => (⟨r.K, A, t'⟩ : Rec n)).toFinset

def step (req : List (Fin n)) (G : Finset (Rec n)) : Finset (Rec n) :=
  G ∪ rootRecs O req ∪ childRecs O G ∪ augRecs O G

/-- Records form a finite type (three subsets of `Fin n`). -/
def recEquiv : Rec n ≃ Ty n × Ty n × Ty n where
  toFun r := (r.K, r.A, r.t)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv r := by cases r; rfl
  right_inv p := by rfl

instance : Fintype (Rec n) := Fintype.ofEquiv _ recEquiv.symm

/-- Iterate `step` until it adds nothing. -/
def saturate (req : List (Fin n)) (G : Finset (Rec n)) : Finset (Rec n) :=
  let G' := step O req G
  if h : G' ⊆ G then G else saturate req G'
termination_by (Finset.univ \ G).card
decreasing_by
  have hsub : G ⊆ step O req G := fun x hx => by simp [step, hx]
  obtain ⟨x, hx, hxG⟩ := Finset.not_subset.1 h
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hsub)]
  exact ⟨x, by simp [hxG], by simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]; exact hx⟩

def Gstar (req : List (Fin n)) : Finset (Rec n) :=
  saturate O req ∅

/-! ## Elimination and the answer -/

def witnessed (G : Finset (Rec n)) (r : Rec n) : Prop :=
  ∀ d ∈ demands O r.t, ∃ r' ∈ G, d.2.2 ∈ r'.t ∧
    fwd O r.t d.2.1 ⊆ r'.t ∧ back O r'.t d.2.1 ⊆ r.t

instance (G : Finset (Rec n)) (r : Rec n) : Decidable (witnessed O G r) := by
  unfold witnessed; infer_instance

def prune (G : Finset (Rec n)) : Finset (Rec n) :=
  G.filter (witnessed O G)

/-- Remove unwitnessed records until stable. -/
def eliminate (G : Finset (Rec n)) : Finset (Rec n) :=
  let G' := prune O G
  if h : G' = G then G else eliminate G'
termination_by G.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, h⟩)

def alive (req : List (Fin n)) : Finset (Rec n) :=
  eliminate O (Gstar O req)

/-- The procedure's verdict on `a ⊑ b`. -/
def entails (req : List (Fin n)) (a b : Fin n) : Bool :=
  decide (∀ r ∈ alive O req, a ∈ r.t → b ∈ r.t)

end Defs

/-! ## Facts the proofs of soundness and completeness use (P2, P3) -/

section Facts

variable {O : Ontology (Fin n) (Fin m)}

/-! ### Membership in the clause lists -/

theorem mem_alls {a c : Fin n} {S : RT m} :
    (a, S, c) ∈ alls O ↔ Clause.allRight a S c ∈ O := by
  simp only [alls, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_exs {a b : Fin n} {R : RT m} :
    (a, R, b) ∈ exs O ↔ Clause.exRight a R b ∈ O := by
  simp only [exs, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_gcis {body head : List (Fin n)} :
    (body, head) ∈ gcis O ↔ Clause.gci body head ∈ O := by
  simp only [gcis, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp at he
    obtain ⟨rfl, rfl⟩ := he
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_stepPairs {R S : RT m} : (R, S) ∈ stepPairs O ↔ RoleStep O R S := by
  unfold stepPairs RoleStep
  simp only [List.mem_append, List.mem_map, List.mem_filterMap]
  constructor
  · rintro (⟨cl, hcl, he⟩ | ⟨⟨R', S'⟩, ⟨cl, hcl, he⟩, hp⟩)
    · split at he
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inl hcl
      · simp at he
    · simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      split at he
      · simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inr (by simpa using hcl)
      · simp at he
  · rintro (h | h)
    · exact Or.inl ⟨_, h, rfl⟩
    · exact Or.inr ⟨(R.flip, S.flip), ⟨_, h, rfl⟩, by simp⟩

/-! ### Role closure -/

theorem mem_upStep {L : List (RT m)} {S : RT m} :
    S ∈ upStep O L ↔ S ∈ L ∨ ∃ R ∈ L, RoleStep O R S := by
  unfold upStep
  simp only [List.mem_dedup, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (h | ⟨⟨R, S'⟩, hp, he⟩)
    · exact Or.inl h
    · by_cases hR : R ∈ L
      · simp only [hR, if_true, Option.some.injEq] at he
        subst he
        exact Or.inr ⟨R, hR, mem_stepPairs.1 hp⟩
      · simp [hR] at he
  · rintro (h | ⟨R, hR, hs⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(R, S), mem_stepPairs.2 hs, by simp [hR]⟩

theorem upStep_congr {L L' : List (RT m)} (h : ∀ x, x ∈ L ↔ x ∈ L') (x : RT m) :
    x ∈ upStep O L ↔ x ∈ upStep O L' := by
  simp only [mem_upStep, h]

theorem roleLe_of_mem_iter (R : RT m) :
    ∀ k, ∀ S ∈ (upStep O)^[k] [R], RoleLe O R S := by
  intro k
  induction k with
  | zero =>
    intro S hS
    simp only [Function.iterate_zero, id, List.mem_singleton] at hS
    subst hS
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro S hS
    rw [Function.iterate_succ_apply', mem_upStep] at hS
    rcases hS with hS | ⟨T, hT, hs⟩
    · exact ih S hS
    · exact Relation.ReflTransGen.tail (ih T hT) hs

/-- The role terms over `Fin m` inject into `Bool × Fin m`. -/
def rtCode : RT m → Bool × Fin m
  | .pos r => (true, r)
  | .inv r => (false, r)

theorem rtCode_inj : Function.Injective (rtCode (m := m)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rtCode]

theorem card_toFinset_le (L : List (RT m)) : L.toFinset.card ≤ 2 * m := by
  have := Finset.card_le_card_of_injOn (s := L.toFinset)
    (t := (Finset.univ : Finset (Bool × Fin m))) rtCode
    (fun _ _ => Finset.mem_univ _) (rtCode_inj.injOn)
  simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_bool] using this

theorem mem_roleUp {R S : RT m} : S ∈ roleUp O R ↔ RoleLe O R S := by
  let F : Nat → Finset (RT m) := fun k => ((upStep O)^[k] [R]).toFinset
  have hF : ∀ k x, x ∈ F k ↔ x ∈ (upStep O)^[k] [R] := fun k x => List.mem_toFinset
  have hgrow : ∀ k, F k ⊆ F (k + 1) := by
    intro k x hx
    rw [hF, Function.iterate_succ_apply', mem_upStep]
    exact Or.inl ((hF k x).1 hx)
  have hstable : ∀ k, F k = F (k + 1) → ∀ j, F (k + j) = F (k + j + 1) := by
    intro k hk j
    induction j with
    | zero => simpa using hk
    | succ j ih =>
      ext x
      rw [hF, hF, show k + (j + 1) = k + j + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
      apply upStep_congr
      intro y
      rw [← hF, ← hF, ih]
  have hcard : ∀ K, (∀ k < K, F k ≠ F (k + 1)) → K + 1 ≤ (F K).card := by
    intro K
    induction K with
    | zero => intro _; simp [F]
    | succ K ih =>
      intro hK
      have h1 := ih (fun k hk => hK k (by omega))
      have h2 : F K ⊂ F (K + 1) :=
        Finset.ssubset_iff_subset_ne.2 ⟨hgrow K, hK K (by omega)⟩
      have := Finset.card_lt_card h2
      omega
  have hfix : F (2 * m) = F (2 * m + 1) := by
    by_contra hne
    have hall : ∀ k < 2 * m + 1, F k ≠ F (k + 1) := by
      intro k hk heq
      have := hstable k heq (2 * m - k)
      rw [show k + (2 * m - k) = 2 * m by omega] at this
      exact hne this
    have := hcard (2 * m + 1) hall
    have := card_toFinset_le ((upStep O)^[2 * m + 1] [R])
    simp only [F] at *
    omega
  have hclosed : ∀ x, x ∈ upStep O (roleUp O R) → x ∈ roleUp O R := by
    intro x hx
    have h2 := hstable (2 * m) hfix 1
    have : x ∈ F (2 * m + 1 + 1) := by
      rw [hF, Function.iterate_succ_apply']; exact hx
    rw [← h2] at this
    exact (hF _ x).1 this
  have hR : R ∈ roleUp O R := by
    have : ∀ k, R ∈ (upStep O)^[k] [R] := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Function.iterate_succ_apply', mem_upStep]; exact Or.inl ih
    exact this _
  constructor
  · exact roleLe_of_mem_iter R _ S
  · intro h
    induction h with
    | refl => exact hR
    | tail _ hst ih => exact hclosed _ (mem_upStep.2 (Or.inr ⟨_, ih, hst⟩))

/-! ### Universal propagation -/

theorem mem_fwd {t : Ty n} {R : RT m} {c : Fin n} :
    c ∈ fwd O t R ↔ ∃ a S, Clause.allRight a S c ∈ O ∧ a ∈ t ∧ RoleLe O R S := by
  simp only [fwd, List.mem_toFinset, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, mem_roleUp]
  constructor
  · rintro ⟨⟨a, S, c'⟩, ⟨hq, ha, hS⟩, rfl⟩
    exact ⟨a, S, mem_alls.1 hq, ha, hS⟩
  · rintro ⟨a, S, hcl, ha, hS⟩
    exact ⟨(a, S, c), ⟨mem_alls.2 hcl, ha, hS⟩, rfl⟩

theorem mem_back {s : Ty n} {R : RT m} {c : Fin n} :
    c ∈ back O s R ↔ ∃ a S, Clause.allRight a S c ∈ O ∧ a ∈ s ∧ RoleLe O R.flip S := by
  simp only [back, List.mem_toFinset, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, mem_roleUp]
  constructor
  · rintro ⟨⟨a, S, c'⟩, ⟨hq, ha, hS⟩, rfl⟩
    exact ⟨a, S, mem_alls.1 hq, ha, hS⟩
  · rintro ⟨a, S, hcl, ha, hS⟩
    exact ⟨(a, S, c), ⟨mem_alls.2 hcl, ha, hS⟩, rfl⟩

theorem compat_iff (R : RT m) (t s : Ty n) :
    Compat O R t s ↔ fwd O t R ⊆ s ∧ back O s R ⊆ t := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · obtain ⟨a, S, hcl, ha, hS⟩ := mem_fwd.1 hc
      exact h1 a S c hcl hS ha
    · obtain ⟨a, S, hcl, ha, hS⟩ := mem_back.1 hc
      exact h2 a S c hcl hS ha
  · rintro ⟨h1, h2⟩
    exact ⟨fun a S c hcl hS ha => h1 (mem_fwd.2 ⟨a, S, hcl, ha, hS⟩),
      fun a S c hcl hS ha => h2 (mem_back.2 ⟨a, S, hcl, ha, hS⟩)⟩

theorem mem_demands {t : Ty n} {a b : Fin n} {R : RT m} :
    (a, R, b) ∈ demands O t ↔ Clause.exRight a R b ∈ O ∧ a ∈ t := by
  simp only [demands, List.mem_filter, decide_eq_true_eq, mem_exs]

/-! ### Branches -/

theorem fuel_absurd {done : List Nat} (hnd : done.Nodup)
    (hlt : ∀ i ∈ done, i < (gcis O).length) (hfuel : (gcis O).length + 1 ≤ done.length) :
    False := by
  have h1 : done.toFinset ⊆ Finset.range (gcis O).length := fun i hi =>
    Finset.mem_range.2 (hlt i (List.mem_toFinset.1 hi))
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at h2
  omega

theorem gci_of_mem_zipIdx {q : (List (Fin n) × List (Fin n)) × Nat}
    (hq : q ∈ (gcis O).zipIdx) : Clause.gci q.1.1 q.1.2 ∈ O :=
  mem_gcis.1 (List.fst_mem_of_mem_zipIdx hq)

theorem exists_mem_zipIdx {body head : List (Fin n)} (h : Clause.gci body head ∈ O) :
    ∃ i, ((body, head), i) ∈ (gcis O).zipIdx := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mem_gcis.2 h)
  exact ⟨i, List.mem_zipIdx_iff_getElem?.2 (by rw [List.getElem?_eq_getElem hi, he])⟩

theorem zipIdx_eq {q q' : (List (Fin n) × List (Fin n)) × Nat} (hq : q ∈ (gcis O).zipIdx)
    (hq' : q' ∈ (gcis O).zipIdx) (h : q.2 = q'.2) : q = q' := by
  have h1 := List.mem_zipIdx_iff_getElem?.1 hq
  have h2 := List.mem_zipIdx_iff_getElem?.1 hq'
  rw [h, h2] at h1
  exact Prod.ext (Option.some.inj h1).symm h

theorem mem_choices {head : List (Fin n)} {cur Y : Ty n} :
    Y ∈ choices head cur ↔
      (∃ l : List (Fin n), l.Sublist head ∧ l.toFinset = Y) ∧ (Y ∪ head.toFinset ∩ cur).Nonempty := by
  simp only [choices, List.mem_dedup, List.mem_filter, List.mem_map, List.mem_sublists,
    decide_eq_true_eq]

theorem choices_head {head : List (Fin n)} {cur Y : Ty n} (hY : Y ∈ choices head cur) :
    ∃ b ∈ head, b ∈ cur ∪ Y := by
  obtain ⟨⟨l, hl, rfl⟩, x, hx⟩ := mem_choices.1 hY
  rcases Finset.mem_union.1 hx with hx | hx
  · exact ⟨x, hl.subset (List.mem_toFinset.1 hx), Finset.mem_union_right _ hx⟩
  · rw [Finset.mem_inter] at hx
    exact ⟨x, List.mem_toFinset.1 hx.1, Finset.mem_union_left _ hx.2⟩

theorem branchesAux_closed : ∀ (fuel : Nat) (cur : Ty n) (done : List Nat) (t : Ty n),
    t ∈ branchesAux O fuel cur done → done.Nodup → (∀ i ∈ done, i < (gcis O).length) →
    (gcis O).length + 1 ≤ fuel + done.length →
    (∀ q ∈ (gcis O).zipIdx, q.2 ∈ done → ∃ b ∈ q.1.2, b ∈ cur) →
    Closed O t ∧ cur ⊆ t := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur done t _ hnd hlt hfuel _
    exact (fuel_absurd hnd hlt (by omega)).elim
  | succ fuel ih =>
    intro cur done t ht hnd hlt hfuel hdone
    rw [branchesAux] at ht
    split at ht
    next hnone =>
      rw [List.mem_singleton] at ht
      subst ht
      refine ⟨fun body head hcl hbody => ?_, Finset.Subset.refl _⟩
      obtain ⟨i, hi⟩ := exists_mem_zipIdx hcl
      have hp := List.find?_eq_none.1 hnone _ hi
      by_cases hid : i ∈ done
      · exact hdone _ hi hid
      · exfalso
        apply hp
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨hid, hbody⟩
    next q hq =>
      have hqmem := List.mem_of_find?_eq_some hq
      have hqp := List.find?_some hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqp
      have hlen := List.snd_lt_of_mem_zipIdx hqmem
      obtain ⟨Y, hY, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨hcl, hsub⟩ := ih (cur ∪ Y) (q.2 :: done) t ht (List.nodup_cons.2 ⟨hqp.1, hnd⟩)
        (by
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · omega
          · exact hlt i hi)
        (by simp only [List.length_cons]; omega)
        (by
          intro q' hq' hd
          rcases List.mem_cons.1 hd with he | hd
          · obtain rfl := zipIdx_eq hq' hqmem he
            exact choices_head hY
          · obtain ⟨b, hb, hbc⟩ := hdone q' hq' hd
            exact ⟨b, hb, Finset.mem_union_left _ hbc⟩)
      exact ⟨hcl, fun x hx => hsub (Finset.mem_union_left _ hx)⟩

theorem branches_closed {σ t : Ty n} (h : t ∈ branches O σ) : Closed O t ∧ σ ⊆ t :=
  branchesAux_closed _ σ [] t h List.nodup_nil (by simp) (by simp) (by simp)

/-- The least superset of `σ` that adds `head ∩ T` whenever a gci body
is contained in it (the `C_T` of the plan). -/
noncomputable def guided (O : Ontology (Fin n) (Fin m)) (T σ : Ty n) : Ty n := by
  classical
  exact Finset.univ.filter fun x => ∀ U : Ty n, (σ ⊆ U ∧ ∀ body head,
    Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ U) → head.toFinset ∩ T ⊆ U) → x ∈ U

theorem mem_guided {T σ : Ty n} {x : Fin n} :
    x ∈ guided O T σ ↔ ∀ U : Ty n, (σ ⊆ U ∧ ∀ body head,
      Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ U) → head.toFinset ∩ T ⊆ U) → x ∈ U := by
  unfold guided
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem guided_least {T σ U : Ty n} (hU : σ ⊆ U) (hcl : ∀ body head,
    Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ U) → head.toFinset ∩ T ⊆ U) :
    guided O T σ ⊆ U :=
  fun _ hx => mem_guided.1 hx U ⟨hU, hcl⟩

theorem guided_closed {T σ : Ty n} {body head : List (Fin n)} (hcl : Clause.gci body head ∈ O)
    (hb : ∀ a ∈ body, a ∈ guided O T σ) : head.toFinset ∩ T ⊆ guided O T σ :=
  fun _ hx => mem_guided.2 fun U hU =>
    hU.2 body head hcl (fun a ha => mem_guided.1 (hb a ha) U hU) hx

theorem guided_le {T σ : Ty n} (hσ : σ ⊆ T) : guided O T σ ⊆ T :=
  guided_least hσ (fun _ _ _ _ => Finset.inter_subset_right)

theorem subset_guided {T σ : Ty n} : σ ⊆ guided O T σ :=
  fun _ hx => mem_guided.2 fun _ hU => hU.1 hx

theorem branchesAux_guided {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) :
    ∀ (fuel : Nat) (cur : Ty n) (done : List Nat), done.Nodup →
    (∀ i ∈ done, i < (gcis O).length) → (gcis O).length + 1 ≤ fuel + done.length →
    σ ⊆ cur → cur ⊆ guided O T σ →
    (∀ q ∈ (gcis O).zipIdx, q.2 ∈ done → q.1.2.toFinset ∩ T ⊆ cur) →
    guided O T σ ∈ branchesAux O fuel cur done := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur done hnd hlt hfuel _ _ _
    exact (fuel_absurd hnd hlt (by omega)).elim
  | succ fuel ih =>
    intro cur done hnd hlt hfuel hσc hcg hdone
    rw [branchesAux]
    split
    next hnone =>
      rw [List.mem_singleton]
      refine Finset.Subset.antisymm (guided_least hσc fun body head hcl hbody => ?_) hcg
      obtain ⟨i, hi⟩ := exists_mem_zipIdx hcl
      have hp := List.find?_eq_none.1 hnone _ hi
      by_cases hid : i ∈ done
      · exact hdone _ hi hid
      · exfalso
        apply hp
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨hid, hbody⟩
    next q hq =>
      have hqmem := List.mem_of_find?_eq_some hq
      have hqp := List.find?_some hq
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hqp
      have hlen := List.snd_lt_of_mem_zipIdx hqmem
      have hcl := gci_of_mem_zipIdx hqmem
      have hcT : cur ⊆ T := hcg.trans (guided_le hσ)
      obtain ⟨b, hb, hbT⟩ := hT _ _ hcl (fun a ha => hcT (hqp.2 a ha))
      have hY : q.1.2.toFinset ∩ T ∈ choices q.1.2 cur := by
        refine mem_choices.2 ⟨⟨q.1.2.filter (fun x => decide (x ∈ T)), List.filter_sublist,
          by ext x; simp⟩, ⟨b, ?_⟩⟩
        simp [hb, hbT]
      refine List.mem_flatMap.2 ⟨_, hY, ih _ _ (List.nodup_cons.2 ⟨hqp.1, hnd⟩) ?_ ?_
        (hσc.trans Finset.subset_union_left)
        (Finset.union_subset hcg (guided_closed hcl fun a ha => hcg (hqp.2 a ha))) ?_⟩
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · omega
        · exact hlt i hi
      · simp only [List.length_cons]; omega
      · intro q' hq' hd
        rcases List.mem_cons.1 hd with he | hd
        · obtain rfl := zipIdx_eq hq' hqmem he
          exact Finset.subset_union_right
        · exact (hdone q' hq' hd).trans Finset.subset_union_left

theorem guided_mem_branches {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) :
    guided O T σ ∈ branches O σ :=
  branchesAux_guided hT hσ _ σ [] List.nodup_nil (by simp) (by simp)
    (Finset.Subset.refl _) subset_guided (by simp)

theorem guided_subset {T σ : Ty n} (hT : Closed O T) (hσ : σ ⊆ T) : guided O T σ ⊆ T :=
  guided_le hσ

theorem guided_mono {T σ σ' : Ty n} (h : σ ⊆ σ') : guided O T σ ⊆ guided O T σ' :=
  guided_least (h.trans subset_guided) fun _ _ hcl hb => guided_closed hcl hb

theorem fwd_mono {t t' : Ty n} (R : RT m) (h : t ⊆ t') : fwd O t R ⊆ fwd O t' R := by
  intro c hc
  obtain ⟨a, S, hcl, ha, hS⟩ := mem_fwd.1 hc
  exact mem_fwd.2 ⟨a, S, hcl, h ha, hS⟩

theorem back_mono {s s' : Ty n} (R : RT m) (h : s ⊆ s') : back O s R ⊆ back O s' R := by
  intro c hc
  obtain ⟨a, S, hcl, ha, hS⟩ := mem_back.1 hc
  exact mem_back.2 ⟨a, S, hcl, h ha, hS⟩

variable {req : List (Fin n)}

/-! ### The candidate set -/

theorem subset_step (G : Finset (Rec n)) : G ⊆ step O req G :=
  fun x hx => by simp [step, hx]

theorem rootRecs_subset_step (G : Finset (Rec n)) : rootRecs O req ⊆ step O req G :=
  fun x hx => by simp only [step, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr hx))

theorem childRecs_subset_step (G : Finset (Rec n)) : childRecs O G ⊆ step O req G :=
  fun x hx => by simp only [step, Finset.mem_union]; exact Or.inl (Or.inr hx)

theorem augRecs_subset_step (G : Finset (Rec n)) : augRecs O G ⊆ step O req G :=
  fun x hx => by simp only [step, Finset.mem_union]; exact Or.inr hx

/-- `saturate` returns a fixpoint of `step` and keeps every invariant
that `step` keeps. -/
theorem saturate_spec (P : Finset (Rec n) → Prop) (hP : ∀ G, P G → P (step O req G)) :
    ∀ G, P G → P (saturate O req G) ∧ step O req (saturate O req G) ⊆ saturate O req G := by
  intro G
  induction h : (Finset.univ \ G).card using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    intro hG
    rw [saturate]
    split_ifs with hs
    · exact ⟨hG, hs⟩
    · refine ih _ ?_ _ rfl (hP G hG)
      rw [← h]
      obtain ⟨x, hx, hxG⟩ := Finset.not_subset.1 hs
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (subset_step G))]
      exact ⟨x, by simp [hxG], by simp [hx]⟩

theorem step_Gstar : step O req (Gstar O req) ⊆ Gstar O req :=
  (saturate_spec (fun _ => True) (fun _ _ => trivial) ∅ trivial).2

theorem Gstar_root {a : Fin n} (ha : a ∈ req) {t : Ty n} (ht : t ∈ branches O {a}) :
    (⟨{a}, ∅, t⟩ : Rec n) ∈ Gstar O req := by
  apply step_Gstar
  apply rootRecs_subset_step
  exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨t, ht, rfl⟩⟩)

theorem Gstar_child {r : Rec n} (hr : r ∈ Gstar O req) {a b : Fin n} {R : RT m}
    (hd : (a, R, b) ∈ demands O r.t) {s : Ty n}
    (hs : s ∈ branches O (insert b (fwd O r.t R))) :
    (⟨insert b (fwd O r.t R), ∅, s⟩ : Rec n) ∈ Gstar O req := by
  apply step_Gstar
  apply childRecs_subset_step
  exact Finset.mem_biUnion.2 ⟨r, hr, List.mem_toFinset.2
    (List.mem_flatMap.2 ⟨(a, R, b), hd, List.mem_map.2 ⟨s, hs, rfl⟩⟩)⟩

theorem Gstar_augment {r r' : Rec n} (hr : r ∈ Gstar O req) (hr' : r' ∈ Gstar O req)
    {a b : Fin n} {R : RT m} (hd : (a, R, b) ∈ demands O r.t)
    (hb : b ∈ r'.K) (hK : r'.K ⊆ insert b (fwd O r.t R)) {t' : Ty n}
    (ht' : t' ∈ branches O (r.K ∪ (r.A ∪ back O r'.t R))) :
    (⟨r.K, r.A ∪ back O r'.t R, t'⟩ : Rec n) ∈ Gstar O req := by
  apply step_Gstar
  apply augRecs_subset_step
  exact Finset.mem_biUnion.2 ⟨r, hr, Finset.mem_biUnion.2 ⟨(a, R, b), List.mem_toFinset.2 hd,
    Finset.mem_biUnion.2 ⟨r', Finset.mem_filter.2 ⟨hr', hb, hK⟩,
      List.mem_toFinset.2 (List.mem_map.2 ⟨t', ht', rfl⟩)⟩⟩⟩

theorem step_closed {G : Finset (Rec n)} (hG : ∀ r ∈ G, Closed O r.t) :
    ∀ r ∈ step O req G, Closed O r.t := by
  intro r hr
  simp only [step, Finset.mem_union] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · exact hG r hr
  · obtain ⟨a, -, t, ht, rfl⟩ := by
      simpa only [rootRecs, List.mem_toFinset, List.mem_flatMap, List.mem_map] using hr
    exact (branches_closed ht).1
  · obtain ⟨r0, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨d, -, hr⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 hr)
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact (branches_closed hs).1
  · obtain ⟨r0, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨d, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨r1, -, hr⟩ := Finset.mem_biUnion.1 hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hr)
    exact (branches_closed hs).1

theorem Gstar_closed {r : Rec n} (hr : r ∈ Gstar O req) : Closed O r.t :=
  (saturate_spec (fun G => ∀ r ∈ G, Closed O r.t) (fun _ hG => step_closed hG) ∅
    (by simp)).1 r hr

/-! ### Elimination -/

theorem witnessed_mono {S G : Finset (Rec n)} (h : S ⊆ G) {r : Rec n}
    (hw : witnessed O S r) : witnessed O G r := by
  intro d hd
  obtain ⟨r', hr', h1, h2, h3⟩ := hw d hd
  exact ⟨r', h hr', h1, h2, h3⟩

theorem eliminate_spec : ∀ G : Finset (Rec n),
    eliminate O G ⊆ G ∧ prune O (eliminate O G) = eliminate O G ∧
    ∀ S ⊆ G, (∀ r ∈ S, witnessed O S r) → S ⊆ eliminate O G := by
  intro G
  induction h : G.card using Nat.strong_induction_on generalizing G with
  | _ k ih =>
    rw [eliminate]
    split_ifs with hp
    · exact ⟨Finset.Subset.refl _, hp, fun S hS _ => hS⟩
    · have hlt : (prune O G).card < k := h ▸
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, hp⟩)
      obtain ⟨h1, h2, h3⟩ := ih _ hlt _ rfl
      refine ⟨h1.trans (Finset.filter_subset _ _), h2, fun S hS hw => h3 S ?_ hw⟩
      intro r hr
      exact Finset.mem_filter.2 ⟨hS hr, witnessed_mono hS (hw r hr)⟩

theorem alive_subset : alive O req ⊆ Gstar O req :=
  (eliminate_spec _).1

theorem alive_witnessed {r : Rec n} (hr : r ∈ alive O req) : witnessed O (alive O req) r := by
  have h := (eliminate_spec (O := O) (Gstar O req)).2.1
  unfold alive at hr ⊢
  rw [← h] at hr
  exact (Finset.mem_filter.1 hr).2

/-- Every set of `Gstar` records whose members are witnessed inside it
survives elimination. -/
theorem subset_alive {S : Finset (Rec n)} (hS : S ⊆ Gstar O req)
    (hw : ∀ r ∈ S, witnessed O S r) : S ⊆ alive O req :=
  (eliminate_spec _).2.2 S hS hw

/-- **P3, soundness.** Alive types are good. -/
theorem alive_good {r : Rec n} (hr : r ∈ alive O req) : Good O r.t := by
  refine ⟨(alive O req).image Rec.t, Finset.mem_image_of_mem _ hr, ?_⟩
  intro t ht
  obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 ht
  refine ⟨Gstar_closed (alive_subset hr0), ?_⟩
  intro a R b hcl ha
  obtain ⟨r', hr', hb, hf, hbk⟩ := alive_witnessed hr0 (a, R, b) (mem_demands.2 ⟨hcl, ha⟩)
  exact ⟨r'.t, Finset.mem_image_of_mem _ hr', hb, (compat_iff R r0.t r'.t).2 ⟨hf, hbk⟩⟩

end Facts

#print axioms alive_good
#print axioms subset_alive
#print axioms guided_mem_branches
#print axioms Gstar_augment

end ContextCalculus.SRI.Proc
