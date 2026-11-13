import ContextCalculus.SRI.Procedure

/-!
# Completeness of the v1.6.3 procedure (plan, section 2b, core lemma)

If a good type contains `a` and not `b`, and `a` is requested, an alive
record contains `a` and not `b`.

Proof. Fix a self-realising `G ∋ t0` and witnesses `w`. Unravel `G` from
`t0` into paths of demands (`tp`). Build, by recursion on the stage `k`
and then on the path, types `m k x ⊆ tp x`:

- `m 0 [] = guided (tp []) {a}`,
  `m 0 (d :: p) = guided (tp (d :: p)) (K 0 (d :: p))`;
- `m (k+1) x = guided (tp x) (K (k+1) x ∪ B k x)`,

with the context `K k (d :: p) = insert d.b (fwd (m k p) d.R)` (the
parent at the same stage), `K k [] = {a}`, and the back set `B k x`, the
union of `back (m k (d :: x)) d.R` over the demands `d` of `m k x`, taken
only when `x` is active at stage `k`. A path is active at stage `k` when
every step is a demand of `m k` of its parent. `m` and activity increase
with `k`; each `m · x` stops at `M x`.

1. `sim`: an active path at stage `k` has a `Gstar` record with context
   `K k x` and type `m k x` (child rule, then augment with the children's
   back sets stage by stage from the stage the path became active).
2. `selfReal`: the records whose type is some `M x` of an eventually
   active `x` are witnessed among themselves.
3. `subset_alive` puts them into `alive`; the root record has `a` and not
   `b` because `M [] ⊆ tp [] = t0`.
-/

namespace ContextCalculus.SRI.Proc

open ContextCalculus.SRI

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)}

/-- A demand: `exRight a R b`. -/
abbrev Dm (n m : Nat) := Fin n × RT m × Fin n

section Unravel

variable (O) (G : Finset (Ty n)) (hG : SelfReal O G)

/-- A witness for every demand of every member of `G` (arbitrary outside). -/
noncomputable def wit (t : Ty n) (d : Dm n m) : Ty n := by
  classical
  exact if h : t ∈ G ∧ Clause.exRight d.1 d.2.1 d.2.2 ∈ O ∧ d.1 ∈ t then
    Classical.choose ((hG t h.1).2 d.1 d.2.1 d.2.2 h.2.1 h.2.2) else t

theorem wit_spec {t : Ty n} (ht : t ∈ G) {d : Dm n m}
    (hd : Clause.exRight d.1 d.2.1 d.2.2 ∈ O) (ha : d.1 ∈ t) :
    wit O G hG t d ∈ G ∧ d.2.2 ∈ wit O G hG t d ∧ Compat O d.2.1 t (wit O G hG t d) := by
  unfold wit
  rw [dif_pos ⟨ht, hd, ha⟩]
  exact Classical.choose_spec ((hG t ht).2 d.1 d.2.1 d.2.2 hd ha)

/-- The type at a path (the head of the list is the last step). -/
noncomputable def tp (t0 : Ty n) : List (Dm n m) → Ty n
  | [] => t0
  | d :: p => wit O G hG (tp t0 p) d

theorem tp_mem {t0 : Ty n} (h0 : t0 ∈ G) (x : List (Dm n m)) : tp O G hG t0 x ∈ G := by
  induction x with
  | nil => exact h0
  | cons d p ih =>
    show wit O G hG (tp O G hG t0 p) d ∈ G
    unfold wit
    split_ifs with h
    · exact (Classical.choose_spec ((hG _ h.1).2 d.1 d.2.1 d.2.2 h.2.1 h.2.2)).1
    · exact ih

end Unravel

section Stages

variable (O) (T : List (Dm n m) → Ty n) (a : Fin n)

/-- Stage `k` types (`T` is the unravelled `tp`). Mutual recursion on the
stage and the path; the activity test and the back sets use stage `k`. -/
noncomputable def stage : Nat → List (Dm n m) → Ty n
  | 0, [] => guided O (T []) {a}
  | 0, d :: p => guided O (T (d :: p)) (insert d.2.2 (fwd O (stage 0 p) d.2.1))
  | k + 1, x =>
      guided O (T x) (ctx (k + 1) x ∪ backs k x)
where
  ctx : Nat → List (Dm n m) → Ty n
    | _, [] => {a}
    | j, d :: p => insert d.2.2 (fwd O (stage j p) d.2.1)
  active : Nat → List (Dm n m) → Prop
    | _, [] => True
    | j, d :: p => d ∈ demands O (stage j p) ∧ active j p
  backs : Nat → List (Dm n m) → Ty n
    | j, x => by
        classical
        exact if active j x then
          ((demands O (stage j x)).map fun d => back O (stage j (d :: x)) d.2.1).foldr (· ∪ ·) ∅
        else ∅

end Stages

/-! The lemmas of the proof, in order. Each is stated for `T = tp …` with
`t0 ∈ G`, `SelfReal O G`, `IsALCHI O`. -/

-- (a) `stage k x ⊆ T x`, and every seed is inside `T x` (compat of `w`).
-- (b) `stage k x ⊆ stage (k+1) x` and `active k x → active (k+1) x`.
-- (c) eventual value `M x` and `∀ k, stage k x ⊆ M x`.
-- (d) `sim`: `active k x → ∃ A, ⟨ctx k x, A, stage k x⟩ ∈ Gstar O req`
--     (with `a ∈ req`); by induction on `k`, then on `x`.
-- (e) `selfReal` of the records whose type is `M x` for an eventually
--     active `x`.
--
-- In this file: (a) `stage_le_T` (on `Valid` paths, with `UnravelOK` for
-- the unravelling, met by `tp_ok`); (b) `stage_mono_succ`, `stage_mono`,
-- `active_mono`; (c) `stage_stab`; (d) `sim`, through `aug_list` (one
-- stage of augments) and `aug_stages` (stages in increasing order);
-- (e) `limRecs_witnessed` for `limRecs`.

section Lemmas

variable {T : List (Dm n m) → Ty n} {a : Fin n}

/-! ### Helpers -/

theorem demands_iff {t : Ty n} {d : Dm n m} :
    d ∈ demands O t ↔ Clause.exRight d.1 d.2.1 d.2.2 ∈ O ∧ d.1 ∈ t := by
  obtain ⟨a, R, b⟩ := d
  exact mem_demands

theorem demands_mono {t t' : Ty n} (h : t ⊆ t') {d : Dm n m} (hd : d ∈ demands O t) :
    d ∈ demands O t' :=
  demands_iff.2 ⟨(demands_iff.1 hd).1, h (demands_iff.1 hd).2⟩

/-- An increasing chain of subsets of `Fin n` stops. -/
theorem chain_stab (f : Nat → Ty n) (hf : ∀ k, f k ⊆ f (k + 1)) :
    ∃ N, ∀ k, N ≤ k → f k = f N := by
  have hmono : Monotone f := monotone_nat_of_le_succ hf
  by_contra hne
  push Not at hne
  have hgrow : ∀ i, ∃ N, i ≤ (f N).card := by
    intro i
    induction i with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ i ih =>
      obtain ⟨N, hN⟩ := ih
      obtain ⟨k, hk, hne'⟩ := hne N
      have hsub : f N ⊂ f k := Finset.ssubset_iff_subset_ne.2 ⟨hmono hk, fun h => hne' h.symm⟩
      exact ⟨k, Nat.lt_of_le_of_lt hN (Finset.card_lt_card hsub)⟩
  obtain ⟨N, hN⟩ := hgrow (n + 1)
  have := Finset.card_le_univ (f N)
  rw [Fintype.card_fin] at this
  omega

theorem exists_lt_succ_iff {P : Nat → Prop} {i : Nat} :
    (∃ j < i + 1, P j) ↔ (∃ j < i, P j) ∨ P i := by
  constructor
  · rintro ⟨j, hj, hP⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Or.inl ⟨j, hj, hP⟩
    · exact Or.inr hP
  · rintro (⟨j, hj, hP⟩ | hP)
    · exact ⟨j, Nat.lt_succ_of_lt hj, hP⟩
    · exact ⟨i, Nat.lt_succ_self i, hP⟩

/-! ### Unfolding the stages -/

theorem stage_zero (x : List (Dm n m)) :
    stage O T a 0 x = guided O (T x) (stage.ctx O T a 0 x) := by
  cases x with
  | nil => rw [stage.eq_1, stage.ctx.eq_1]
  | cons d p => rw [stage.eq_2, stage.ctx.eq_2]

theorem stage_succ (k : Nat) (x : List (Dm n m)) :
    stage O T a (k + 1) x = guided O (T x) (stage.ctx O T a (k + 1) x ∪ stage.backs O T a k x) :=
  stage.eq_3 O T a x k

theorem mem_backs {k : Nat} {x : List (Dm n m)} {c : Fin n} :
    c ∈ stage.backs O T a k x ↔ stage.active O T a k x ∧
      ∃ d ∈ demands O (stage O T a k x), c ∈ back O (stage O T a k (d :: x)) d.2.1 := by
  rw [stage.backs.eq_1]
  split_ifs with h
  · simp only [h, true_and]
    generalize demands O (stage O T a k x) = L
    induction L with
    | nil => simp
    | cons d L ih => simp [ih]
  · simp [h]

theorem active_cons {k : Nat} {d : Dm n m} {p : List (Dm n m)} :
    stage.active O T a k (d :: p) ↔ d ∈ demands O (stage O T a k p) ∧ stage.active O T a k p := by
  rw [stage.active.eq_2]

theorem active_nil (k : Nat) : stage.active O T a k [] := by
  rw [stage.active.eq_1]; trivial

theorem ctx_sub_stage (k : Nat) (x : List (Dm n m)) :
    stage.ctx O T a k x ⊆ stage O T a k x := by
  cases k with
  | zero => rw [stage_zero]; exact subset_guided
  | succ k => rw [stage_succ]; exact Finset.subset_union_left.trans subset_guided

theorem backs_sub_stage (k : Nat) (x : List (Dm n m)) :
    stage.backs O T a k x ⊆ stage O T a (k + 1) x := by
  rw [stage_succ]; exact Finset.subset_union_right.trans subset_guided

theorem mem_ctx_cons (k : Nat) (d : Dm n m) (p : List (Dm n m)) :
    d.2.2 ∈ stage.ctx O T a k (d :: p) := by
  rw [stage.ctx.eq_2]; exact Finset.mem_insert_self _ _

theorem fwd_sub_ctx (k : Nat) (d : Dm n m) (p : List (Dm n m)) :
    fwd O (stage O T a k p) d.2.1 ⊆ stage.ctx O T a k (d :: p) := by
  rw [stage.ctx.eq_2]; exact Finset.subset_insert _ _

/-! ### (a) The stages stay inside the unravelled types -/

variable (O T a) in
/-- What the proof needs from the unravelling `T`: the root contains `a`,
every type is closed, and a step along a demand of the parent reaches a
compatible type that contains the demanded name. -/
def UnravelOK : Prop :=
  a ∈ T [] ∧ (∀ x, Closed O (T x)) ∧
    ∀ (d : Dm n m) p, Clause.exRight d.1 d.2.1 d.2.2 ∈ O → d.1 ∈ T p →
      d.2.2 ∈ T (d :: p) ∧ Compat O d.2.1 (T p) (T (d :: p))

variable (O T) in
/-- A path is valid when every step is a demand of the type it leaves. -/
def Valid : List (Dm n m) → Prop
  | [] => True
  | d :: p => Clause.exRight d.1 d.2.1 d.2.2 ∈ O ∧ d.1 ∈ T p ∧ Valid p

theorem ctx_cons_le (hT : UnravelOK O T a) {k : Nat} {d : Dm n m} {p : List (Dm n m)}
    (hv : Valid O T (d :: p)) (hp : stage O T a k p ⊆ T p) :
    stage.ctx O T a k (d :: p) ⊆ T (d :: p) := by
  rw [stage.ctx.eq_2]
  obtain ⟨hex, hd, -⟩ := hv
  obtain ⟨hb, hc⟩ := hT.2.2 d p hex hd
  exact Finset.insert_subset hb ((fwd_mono _ hp).trans ((compat_iff (O := O) _ _ _).1 hc).1)

theorem valid_cons {k : Nat} {d : Dm n m} {x : List (Dm n m)} (hv : Valid O T x)
    (hd : d ∈ demands O (stage O T a k x)) (hx : stage O T a k x ⊆ T x) :
    Valid O T (d :: x) :=
  ⟨(demands_iff.1 hd).1, hx (demands_iff.1 hd).2, hv⟩

theorem backs_le (hT : UnravelOK O T a) {k : Nat} {x : List (Dm n m)}
    (hx : stage O T a k x ⊆ T x)
    (hc : ∀ d ∈ demands O (stage O T a k x), stage O T a k (d :: x) ⊆ T (d :: x)) :
    stage.backs O T a k x ⊆ T x := by
  intro c hcm
  obtain ⟨-, d, hd, hcb⟩ := mem_backs.1 hcm
  obtain ⟨hex, hd1⟩ := demands_iff.1 hd
  obtain ⟨-, hcomp⟩ := hT.2.2 d x hex (hx hd1)
  exact ((compat_iff (O := O) _ _ _).1 hcomp).2 (back_mono _ (hc d hd) hcb)

/-- **(a)** On valid paths every stage lies inside the unravelled type. -/
theorem stage_le_T (hT : UnravelOK O T a) :
    ∀ k x, Valid O T x → stage O T a k x ⊆ T x := by
  intro k
  induction k with
  | zero =>
    intro x
    induction x with
    | nil => intro _; rw [stage.eq_1]; exact guided_le (Finset.singleton_subset_iff.2 hT.1)
    | cons d p ih =>
      intro hv
      rw [stage_zero]
      exact guided_le (ctx_cons_le hT hv (ih hv.2.2))
  | succ k ihk =>
    have hb : ∀ x, Valid O T x → stage.backs O T a k x ⊆ T x := fun x hv =>
      backs_le hT (ihk x hv) (fun d hd => ihk _ (valid_cons hv hd (ihk x hv)))
    intro x
    induction x with
    | nil =>
      intro hv
      rw [stage_succ]
      refine guided_le (Finset.union_subset ?_ (hb [] hv))
      rw [stage.ctx.eq_1]; exact Finset.singleton_subset_iff.2 hT.1
    | cons d p ih =>
      intro hv
      rw [stage_succ]
      exact guided_le (Finset.union_subset (ctx_cons_le hT hv (ih hv.2.2)) (hb _ hv))

theorem backs_le_T (hT : UnravelOK O T a) {k : Nat} {x : List (Dm n m)} (hv : Valid O T x) :
    stage.backs O T a k x ⊆ T x :=
  backs_le hT (stage_le_T hT k x hv)
    (fun _ hd => stage_le_T hT k _ (valid_cons hv hd (stage_le_T hT k x hv)))

/-- Active paths are valid. -/
theorem valid_of_active (hT : UnravelOK O T a) {k : Nat} :
    ∀ {x : List (Dm n m)}, stage.active O T a k x → Valid O T x
  | [], _ => trivial
  | _ :: _, h =>
    have hv := valid_of_active hT (active_cons.1 h).2
    valid_cons hv (active_cons.1 h).1 (stage_le_T hT k _ hv)

/-! ### (b) The stages and activity increase -/

theorem active_mono_of {k k' : Nat} (h : ∀ p, stage O T a k p ⊆ stage O T a k' p) :
    ∀ {x : List (Dm n m)}, stage.active O T a k x → stage.active O T a k' x
  | [], _ => active_nil k'
  | _ :: _, hx =>
    active_cons.2 ⟨demands_mono (h _) (active_cons.1 hx).1, active_mono_of h (active_cons.1 hx).2⟩

theorem ctx_mono_of {k k' : Nat} (h : ∀ p, stage O T a k p ⊆ stage O T a k' p)
    (x : List (Dm n m)) : stage.ctx O T a k x ⊆ stage.ctx O T a k' x := by
  cases x with
  | nil => rw [stage.ctx.eq_1, stage.ctx.eq_1]
  | cons d p =>
    rw [stage.ctx.eq_2, stage.ctx.eq_2]
    exact Finset.insert_subset_insert _ (fwd_mono _ (h p))

theorem backs_mono_of {k k' : Nat} (h : ∀ p, stage O T a k p ⊆ stage O T a k' p)
    (x : List (Dm n m)) : stage.backs O T a k x ⊆ stage.backs O T a k' x := by
  intro c hc
  obtain ⟨hact, d, hd, hcb⟩ := mem_backs.1 hc
  exact mem_backs.2 ⟨active_mono_of h hact, d, demands_mono (h x) hd, back_mono _ (h _) hcb⟩

/-- **(b)** One stage more gives a larger type, on every path. -/
theorem stage_mono_succ : ∀ (k : Nat) (x : List (Dm n m)),
    stage O T a k x ⊆ stage O T a (k + 1) x := by
  intro k
  induction k with
  | zero =>
    intro x
    induction x with
    | nil =>
      rw [stage.eq_1, stage_succ]
      refine guided_mono (Finset.Subset.trans ?_ Finset.subset_union_left)
      rw [stage.ctx.eq_1]
    | cons d p ih =>
      rw [stage_zero, stage_succ]
      refine guided_mono (Finset.Subset.trans ?_ Finset.subset_union_left)
      rw [stage.ctx.eq_2, stage.ctx.eq_2]
      exact Finset.insert_subset_insert _ (fwd_mono _ ih)
  | succ k ihk =>
    intro x
    induction x with
    | nil =>
      rw [stage_succ, stage_succ]
      exact guided_mono (Finset.union_subset_union (by rw [stage.ctx.eq_1, stage.ctx.eq_1])
        (backs_mono_of ihk _))
    | cons d p ih =>
      rw [stage_succ, stage_succ (k + 1)]
      refine guided_mono (Finset.union_subset_union ?_ (backs_mono_of ihk _))
      rw [stage.ctx.eq_2, stage.ctx.eq_2]
      exact Finset.insert_subset_insert _ (fwd_mono _ ih)

theorem stage_mono {k k' : Nat} (h : k ≤ k') (x : List (Dm n m)) :
    stage O T a k x ⊆ stage O T a k' x :=
  monotone_nat_of_le_succ (f := fun j => stage O T a j x) (fun j => stage_mono_succ j x) h

theorem active_mono {k k' : Nat} (h : k ≤ k') {x : List (Dm n m)}
    (hx : stage.active O T a k x) : stage.active O T a k' x :=
  active_mono_of (fun p => stage_mono h p) hx

/-! ### (c) Every path has an eventual stage -/

/-- **(c)** The stages of a path stop growing. -/
theorem stage_stab (x : List (Dm n m)) :
    ∃ N, ∀ k, N ≤ k → stage O T a k x = stage O T a N x :=
  chain_stab (fun k => stage O T a k x) (fun k => stage_mono_succ k x)

/-! ### (d) Every active stage type is a record of `Gstar` -/

variable {req : List (Fin n)}

/-- Augment along a list of demands of `stage j x`, using the records of
the children at stage `j`. The current type contains `stage j x`, so each
child's context passes the augment condition. -/
theorem aug_list (hT : UnravelOK O T a) {x : List (Dm n m)} {K : Ty n} {j : Nat}
    (hK : K ⊆ T x) :
    ∀ (L : List (Dm n m)) (A : Ty n),
      (⟨K, A, guided O (T x) (K ∪ A)⟩ : Rec n) ∈ Gstar O req → A ⊆ T x →
      stage O T a j x ⊆ guided O (T x) (K ∪ A) →
      (∀ d ∈ L, d ∈ demands O (stage O T a j x) ∧
        (∃ A', (⟨stage.ctx O T a j (d :: x), A', stage O T a j (d :: x)⟩ : Rec n) ∈ Gstar O req) ∧
        back O (stage O T a j (d :: x)) d.2.1 ⊆ T x) →
      ∃ B : Ty n, (∀ c, c ∈ B ↔ c ∈ A ∨ ∃ d ∈ L, c ∈ back O (stage O T a j (d :: x)) d.2.1) ∧
        (⟨K, B, guided O (T x) (K ∪ B)⟩ : Rec n) ∈ Gstar O req := by
  intro L
  induction L with
  | nil =>
    intro A hr _ _ _
    exact ⟨A, fun c => by simp, hr⟩
  | cons d L ih =>
    intro A hr hA hU hL
    obtain ⟨hd, ⟨A', hr'⟩, hbk⟩ := hL d (List.mem_cons_self ..)
    have hd' : d ∈ demands O (guided O (T x) (K ∪ A)) := demands_mono hU hd
    have hsub : K ∪ (A ∪ back O (stage O T a j (d :: x)) d.2.1) ⊆ T x :=
      Finset.union_subset hK (Finset.union_subset hA hbk)
    have hnew : (⟨K, A ∪ back O (stage O T a j (d :: x)) d.2.1,
        guided O (T x) (K ∪ (A ∪ back O (stage O T a j (d :: x)) d.2.1))⟩ : Rec n) ∈
          Gstar O req :=
      Gstar_augment (r := ⟨K, A, guided O (T x) (K ∪ A)⟩) hr hr' hd' (mem_ctx_cons j d x)
        (by
          show stage.ctx O T a j (d :: x) ⊆ insert d.2.2 (fwd O (guided O (T x) (K ∪ A)) d.2.1)
          rw [stage.ctx.eq_2]
          exact Finset.insert_subset_insert _ (fwd_mono _ hU))
        (guided_mem_branches (hT.2.1 x) hsub)
    obtain ⟨B, hB, hrB⟩ := ih _ hnew (Finset.union_subset hA hbk)
      (hU.trans (guided_mono (Finset.union_subset_union (Finset.Subset.refl _)
        Finset.subset_union_left)))
      (fun d' hd' => hL d' (List.mem_cons_of_mem _ hd'))
    refine ⟨B, fun c => ?_, hrB⟩
    rw [hB c, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨d', hd', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨d', List.mem_cons_of_mem _ hd', h⟩
    · rintro (h | ⟨d', hd', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hd' with rfl | hd'
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨d', hd', h⟩

/-- Augment with the back sets of stages `0` to `i - 1`, in increasing
order, starting from the record the child (or root) rule gives. -/
theorem aug_stages (hT : UnravelOK O T a) {k : Nat}
    (ih : ∀ j < k + 1, ∀ y, stage.active O T a j y →
      ∃ A, (⟨stage.ctx O T a j y, A, stage O T a j y⟩ : Rec n) ∈ Gstar O req)
    {x : List (Dm n m)} (hv : Valid O T x)
    (hbase : (⟨stage.ctx O T a (k + 1) x, ∅, guided O (T x) (stage.ctx O T a (k + 1) x)⟩ : Rec n) ∈
      Gstar O req) :
    ∀ i ≤ k + 1, ∃ B : Ty n, (∀ c, c ∈ B ↔ ∃ j < i, c ∈ stage.backs O T a j x) ∧
      (⟨stage.ctx O T a (k + 1) x, B, guided O (T x) (stage.ctx O T a (k + 1) x ∪ B)⟩ : Rec n) ∈
        Gstar O req := by
  have hK : stage.ctx O T a (k + 1) x ⊆ T x :=
    (ctx_sub_stage _ _).trans (stage_le_T hT _ x hv)
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅, fun c => by simp, by rw [Finset.union_empty]; exact hbase⟩
  | succ i ihi =>
    intro hi
    obtain ⟨B, hB, hr⟩ := ihi (Nat.le_of_succ_le hi)
    have hBT : B ⊆ T x := fun c hc => by
      obtain ⟨j, -, hj⟩ := (hB c).1 hc
      exact backs_le_T hT hv hj
    by_cases hact : stage.active O T a i x
    · have hU : stage O T a i x ⊆ guided O (T x) (stage.ctx O T a (k + 1) x ∪ B) := by
        cases i with
        | zero =>
          rw [stage_zero]
          exact guided_mono ((ctx_mono_of (fun p => stage_mono (Nat.zero_le _) p) x).trans
            Finset.subset_union_left)
        | succ i =>
          rw [stage_succ]
          refine guided_mono (Finset.union_subset_union
            (ctx_mono_of (fun p => stage_mono (by omega) p) x) fun c hc => ?_)
          exact (hB c).2 ⟨i, Nat.lt_succ_self i, hc⟩
      obtain ⟨B', hB', hr'⟩ := aug_list (j := i) hT hK (demands O (stage O T a i x)) B hr hBT hU
        (fun d hd => ⟨hd, ih i (by omega) (d :: x) (active_cons.2 ⟨hd, hact⟩),
          fun c hc => backs_le_T hT hv (mem_backs.2 ⟨hact, d, hd, hc⟩)⟩)
      refine ⟨B', fun c => ?_, hr'⟩
      rw [hB', hB, exists_lt_succ_iff, mem_backs]
      simp only [hact, true_and]
    · refine ⟨B, fun c => ?_, hr⟩
      rw [hB, exists_lt_succ_iff, mem_backs]
      simp [hact]

/-- **(d)** An active path at stage `k` has a `Gstar` record with context
`ctx k x` and type `stage k x`. -/
theorem sim (hT : UnravelOK O T a) (ha : a ∈ req) :
    ∀ k x, stage.active O T a k x →
      ∃ A, (⟨stage.ctx O T a k x, A, stage O T a k x⟩ : Rec n) ∈ Gstar O req := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  -- The record the root or child rule gives at stage `k`, from the
  -- parent's record at stage `k`.
  have hbase : ∀ x, stage.active O T a k x → (∀ p, x ≠ [] → x.tail = p →
      ∃ A, (⟨stage.ctx O T a k p, A, stage O T a k p⟩ : Rec n) ∈ Gstar O req) →
      (⟨stage.ctx O T a k x, ∅, guided O (T x) (stage.ctx O T a k x)⟩ : Rec n) ∈ Gstar O req := by
    intro x hx hpar
    cases x with
    | nil =>
      rw [stage.ctx.eq_1]
      exact Gstar_root ha (guided_mem_branches (hT.2.1 _) (Finset.singleton_subset_iff.2 hT.1))
    | cons d p =>
      obtain ⟨A, hr⟩ := hpar p (List.cons_ne_nil _ _) rfl
      have hv := valid_of_active hT hx
      have hK := ctx_cons_le hT hv (stage_le_T hT k p hv.2.2)
      rw [stage.ctx.eq_2] at hK ⊢
      exact Gstar_child (r := ⟨_, A, stage O T a k p⟩) hr (active_cons.1 hx).1
        (guided_mem_branches (hT.2.1 _) hK)
  intro x
  induction x with
  | nil =>
    intro hx
    have hb := hbase [] hx (fun _ h => absurd rfl h)
    cases k with
    | zero => exact ⟨∅, by rw [stage_zero]; exact hb⟩
    | succ k =>
      obtain ⟨B, hB, hr⟩ := aug_stages (x := []) hT ih trivial hb (k + 1) le_rfl
      refine ⟨B, ?_⟩
      have hBe : B = stage.backs O T a k [] := by
        ext c
        rw [hB, exists_lt_succ_iff]
        constructor
        · rintro (⟨j, hj, hc⟩ | hc)
          · exact backs_mono_of (fun p => stage_mono hj.le p) _ hc
          · exact hc
        · exact Or.inr
      rw [stage_succ, ← hBe]
      exact hr
  | cons d p ihp =>
    intro hx
    have hb := hbase (d :: p) hx (fun q _ hq => by
      subst hq; exact ihp (active_cons.1 hx).2)
    cases k with
    | zero => exact ⟨∅, by rw [stage_zero]; exact hb⟩
    | succ k =>
      obtain ⟨B, hB, hr⟩ := aug_stages hT ih (valid_of_active hT hx) hb (k + 1) le_rfl
      refine ⟨B, ?_⟩
      have hBe : B = stage.backs O T a k (d :: p) := by
        ext c
        rw [hB, exists_lt_succ_iff]
        constructor
        · rintro (⟨j, hj, hc⟩ | hc)
          · exact backs_mono_of (fun p => stage_mono hj.le p) _ hc
          · exact hc
        · exact Or.inr
      rw [stage_succ, ← hBe]
      exact hr

/-! ### (e) The eventual records are witnessed among themselves -/

variable (O T a req) in
/-- The `Gstar` records whose type is the eventual stage of an eventually
active path. -/
noncomputable def limRecs (N : List (Dm n m) → Nat) : Finset (Rec n) := by
  classical
  exact (Gstar O req).filter fun r =>
    ∃ x, (∃ k, stage.active O T a k x) ∧ r.t = stage O T a (N x) x

theorem mem_limRecs {N : List (Dm n m) → Nat} {r : Rec n} :
    r ∈ limRecs O T a req N ↔
      r ∈ Gstar O req ∧ ∃ x, (∃ k, stage.active O T a k x) ∧ r.t = stage O T a (N x) x := by
  classical
  unfold limRecs
  rw [Finset.mem_filter]

/-- **(e)** The eventual records are witnessed among themselves. -/
theorem limRecs_witnessed (hT : UnravelOK O T a) (ha : a ∈ req) {N : List (Dm n m) → Nat}
    (hN : ∀ x k, N x ≤ k → stage O T a k x = stage O T a (N x) x) :
    ∀ r ∈ limRecs O T a req N, witnessed O (limRecs O T a req N) r := by
  intro r hr d hd
  obtain ⟨-, x, ⟨k0, hk0⟩, hrt⟩ := mem_limRecs.1 hr
  rw [hrt] at hd ⊢
  let k := max (max (N x) (N (d :: x))) k0
  have hsx : stage O T a k x = stage O T a (N x) x := hN x k (by omega)
  have hsx1 : stage O T a (k + 1) x = stage O T a (N x) x := hN x (k + 1) (by omega)
  have hsd : stage O T a k (d :: x) = stage O T a (N (d :: x)) (d :: x) := hN _ k (by omega)
  have hact : stage.active O T a k x := active_mono (by omega) hk0
  have hd' : d ∈ demands O (stage O T a k x) := hsx ▸ hd
  have hactd : stage.active O T a k (d :: x) := active_cons.2 ⟨hd', hact⟩
  obtain ⟨A, hrec⟩ := sim hT ha k (d :: x) hactd
  refine ⟨⟨stage.ctx O T a k (d :: x), A, stage O T a k (d :: x)⟩,
    mem_limRecs.2 ⟨hrec, d :: x, ⟨k, hactd⟩, hsd⟩, ?_, ?_, ?_⟩
  · exact ctx_sub_stage k (d :: x) (mem_ctx_cons k d x)
  · rw [← hsx]
    exact (fwd_sub_ctx k d x).trans (ctx_sub_stage k (d :: x))
  · rw [← hsx1]
    exact fun c hc => backs_sub_stage k x (mem_backs.2 ⟨hact, d, hd', hc⟩)

end Lemmas

/-- The unravelling of a self-realising set meets `UnravelOK`. -/
theorem tp_ok {G : Finset (Ty n)} (hG : SelfReal O G) {t0 : Ty n} (h0 : t0 ∈ G) {a : Fin n}
    (hat : a ∈ t0) : UnravelOK O (tp O G hG t0) a := by
  refine ⟨hat, fun x => (hG _ (tp_mem O G hG h0 x)).1, fun d p hex hd => ?_⟩
  obtain ⟨-, hb, hc⟩ := wit_spec O G hG (tp_mem O G hG h0 p) hex hd
  exact ⟨hb, hc⟩

/-- **P4, completeness.** -/
theorem complete (hA : IsALCHI O) {req : List (Fin n)} {a b : Fin n} (ha : a ∈ req)
    {t0 : Ty n} (hgood : Good O t0) (hat : a ∈ t0) (hbt : b ∉ t0) :
    ∃ r ∈ alive O req, a ∈ r.t ∧ b ∉ r.t := by
  obtain ⟨G, ht0, hG⟩ := hgood
  have hT := tp_ok hG ht0 hat
  choose N hN using fun x => stage_stab (O := O) (T := tp O G hG t0) (a := a) x
  have hN' : ∀ x k, N x ≤ k →
      stage O (tp O G hG t0) a k x = stage O (tp O G hG t0) a (N x) x := hN
  obtain ⟨A, hr⟩ := sim hT ha (N []) [] (active_nil _)
  have hmem : (⟨stage.ctx O (tp O G hG t0) a (N []) [], A, stage O (tp O G hG t0) a (N []) []⟩ :
      Rec n) ∈ limRecs O (tp O G hG t0) a req N :=
    mem_limRecs.2 ⟨hr, [], ⟨0, active_nil 0⟩, rfl⟩
  refine ⟨_, subset_alive (fun r hr => (mem_limRecs.1 hr).1) (limRecs_witnessed hT ha hN') hmem, ?_, ?_⟩
  · apply ctx_sub_stage
    rw [stage.ctx.eq_1]
    exact Finset.mem_singleton_self a
  · exact fun hb => hbt (stage_le_T hT (N []) [] trivial hb)

/-- **Exactness of the procedure on requested names.** -/
theorem entails_iff (hA : IsALCHI O) {req : List (Fin n)} {a : Fin n} (ha : a ∈ req)
    (b : Fin n) : entails O req a b = true ↔ EntailsSub O a b := by
  rw [entailsSub_iff_good O hA, entails, decide_eq_true_iff]
  constructor
  · intro h t ht hat
    by_contra hbt
    obtain ⟨r, hr, har, hbr⟩ := complete hA ha ht hat hbt
    exact hbr (h r hr har)
  · intro h r hr har
    exact h r.t (alive_good hr) har

end ContextCalculus.SRI.Proc

#print axioms ContextCalculus.SRI.Proc.complete
#print axioms ContextCalculus.SRI.Proc.entails_iff
