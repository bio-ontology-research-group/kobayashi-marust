/-
  ContextCalculus/CompletenessStrategy.lean
  ==========================================
  **Completeness of an abstract finite type-elimination strategy.**

  This file proves that explicit elimination over the complete finite ALC type
  space decides subsumption. The Rust CB engine uses disjunctive context clauses
  and does not explicitly enumerate or discard these types. No theorem in this
  file identifies a production terminal state with this elimination fixpoint.

  Everything here is `sorry`-free.  The chain is:

    * `good_iff`            — a type is good iff it is consistent and every
                              existential it forces is witnessed by *another good
                              type* across a compatible edge.  This is the
                              fixpoint equation a single elimination round checks.
    * `goodFS_selfReal` /
      `selfReal_subset_goodFS` — the good types form the **greatest** self-realising
                              set (the gfp of the elimination operator `step`).
    * `step_goodFS`        — the good types are a fixpoint of `step`.
    * `exists_fixed` / `saturate_fixed` — iterating `step` from the consistent
                              candidates **converges** to a fixpoint after at most
                              `|candidates|` rounds (a strictly shrinking finite
                              chain).
    * `mem_saturate_iff_good` — that computed fixpoint *is* the set of good types.
    * `saturate_sound` / `saturate_complete` / `saturate_decides` — hence the
                              strategy's materialised set is sound and complete and
                              decides `A ⊑ B` (via `strategy_decides`, itself a
                              corollary of `CompletenessContext.subsumption_complete`).
    * `engine_decides`     — general form over any materialised candidate set `U`
                              with `goodFS O ⊆ U ⊆ cand O`.
    * `engine_complete`    — **the `coverage` hypothesis discharged.**  The engine's
                              pre-elimination candidate space, *at the type level*,
                              is all of `cand O` (its disjunctive context clauses
                              represent the whole consistent-type space), and
                              `goodFS O ⊆ cand O` is `goodFS_subset_cand`.  So the
                              decision carries no residual hypothesis (it is defeq
                              to `saturate_decides`); `coverage_of_seeds` records why
                              coverage is free.

  Scope note: this is the ALC **type-level** argument, now hypothesis-free. The
  principal thing left between it and the running Rust binary is *not* coverage but the
  **representation refinement**: the engine manipulates disjunctive context *clauses*
  rather than enumerated types, and that its clause saturation computes the same
  `goodFS` is the disjunctive-saturation completeness — a substantial theorem that is
  **not** claimed here. Generated examples can establish individual positive
  verdicts with `CheckerTerm.certifies_subsumptionT`, but the production CB
  worker does not yet invoke a mandatory checker. Neither generated examples nor
  empirical oracle agreement establishes the production publication boundary.
-/
import ContextCalculus.CompletenessContext

namespace ContextCalculus.Ctx

set_option linter.unusedSectionVars false

open Classical

section Strategy

variable {CName Role : Type} [Fintype CName] [DecidableEq CName] [DecidableEq Role]
variable (O : Ontology CName Role)

/-- A strategy *outcome* `G` (the set of type-contexts a strategy materialises at
    its fixpoint) is **sound** when every materialised type is a good type. -/
def StratSound (G : Finset CName → Prop) : Prop := ∀ t, G t → Good O t

/-- A strategy outcome `G` is **complete** when every good type is materialised. -/
def StratComplete (G : Finset CName → Prop) : Prop := ∀ t, Good O t → G t

/-- **Reduction theorem (proved).**  A sound + complete strategy outcome `G`
    decides atomic subsumption exactly. -/
theorem strategy_decides (G : Finset CName → Prop)
    (hs : StratSound O G) (hc : StratComplete O G) (A B : CName) :
    (∀ t, G t → A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) := by
  rw [subsumption_complete O A B]
  exact ⟨fun h t hg hA => h t (hc t hg) hA, fun h t hg hA => h t (hs t hg) hA⟩

/-! ### The good types are the greatest self-realising set -/

/-- Realisation is monotone in the ambient set: more types means more potential
    witnesses. -/
theorem realizedIn_mono {G H : Finset (Finset CName)} (hsub : G ⊆ H)
    {t : Finset CName} (h : realizedIn O G t) : realizedIn O H t := by
  intro a r b hcl ha
  obtain ⟨s, hsG, hbs, hco⟩ := h a r b hcl ha
  exact ⟨s, hsub hsG, hbs, hco⟩

/-- The finite set of all good types. -/
noncomputable def goodFS : Finset (Finset CName) :=
  (Finset.univ : Finset CName).powerset.filter (Good O)

theorem mem_goodFS {t : Finset CName} : t ∈ goodFS O ↔ Good O t := by
  simp [goodFS, Finset.mem_filter]

/-- The good types are self-realising: each good type's existentials are
    witnessed by good types. -/
theorem goodFS_selfReal : SelfReal O (goodFS O) := by
  intro t ht
  rw [mem_goodFS] at ht
  obtain ⟨G, htG, hG⟩ := ht
  refine ⟨(hG t htG).1, ?_⟩
  intro a r b hcl ha
  obtain ⟨s, hsG, hbs, hco⟩ := (hG t htG).2 a r b hcl ha
  exact ⟨s, (mem_goodFS O).2 ⟨G, hsG, hG⟩, hbs, hco⟩

/-- Every self-realising set is contained in the good types: the good types are
    the **greatest** self-realising set. -/
theorem selfReal_subset_goodFS {G : Finset (Finset CName)} (hG : SelfReal O G) :
    G ⊆ goodFS O := by
  intro t ht
  exact (mem_goodFS O).2 ⟨G, ht, hG⟩

/-- **Fixpoint characterisation of goodness.**  A type is good iff it is
    consistent and each existential it forces has a *good* witness across a
    compatible edge — exactly what one elimination round preserves. -/
theorem good_iff (t : Finset CName) :
    Good O t ↔ consistent O t ∧
      ∀ a r b, Clause.exRight a r b ∈ O → a ∈ t →
        ∃ s, Good O s ∧ b ∈ s ∧ compat O r t s := by
  constructor
  · rintro ⟨G, htG, hG⟩
    refine ⟨(hG t htG).1, ?_⟩
    intro a r b hcl ha
    obtain ⟨s, hsG, hbs, hco⟩ := (hG t htG).2 a r b hcl ha
    exact ⟨s, ⟨G, hsG, hG⟩, hbs, hco⟩
  · rintro ⟨hcons, hreal⟩
    refine ⟨insert t (goodFS O), Finset.mem_insert_self _ _, ?_⟩
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu'
    · refine ⟨hcons, ?_⟩
      intro a r b hcl ha
      obtain ⟨s, hs, hbs, hco⟩ := hreal a r b hcl ha
      exact ⟨s, Finset.mem_insert_of_mem ((mem_goodFS O).2 hs), hbs, hco⟩
    · refine ⟨(goodFS_selfReal O u hu').1, ?_⟩
      exact realizedIn_mono O (Finset.subset_insert _ _) (goodFS_selfReal O u hu').2

/-! ### The elimination operator and its convergence -/

/-- One type-elimination round: keep the types whose existentials are realised
    inside the current set.  This is exactly the engine's discard step. -/
noncomputable def step (G : Finset (Finset CName)) : Finset (Finset CName) :=
  G.filter (realizedIn O G)

theorem step_subset (G : Finset (Finset CName)) : step O G ⊆ G :=
  Finset.filter_subset _ _

/-- The good types are a fixpoint of `step`. -/
theorem step_goodFS : step O (goodFS O) = goodFS O := by
  apply Finset.Subset.antisymm (step_subset O _)
  intro t ht
  exact Finset.mem_filter.2 ⟨ht, (goodFS_selfReal O t ht).2⟩

/-- The consistent candidate types — the engine's starting set. -/
noncomputable def cand : Finset (Finset CName) :=
  (Finset.univ : Finset CName).powerset.filter (consistent O)

theorem mem_cand {t : Finset CName} : t ∈ cand O ↔ consistent O t := by
  simp [cand, Finset.mem_filter]

theorem goodFS_subset_cand : goodFS O ⊆ cand O := by
  intro t ht
  rw [mem_goodFS] at ht
  obtain ⟨G, htG, hG⟩ := ht
  exact (mem_cand O).2 (hG t htG).1

/-- Iterating `step` from the candidates. -/
noncomputable def sat (n : ℕ) : Finset (Finset CName) := (step O)^[n] (cand O)

theorem sat_zero : sat O 0 = cand O := rfl

theorem sat_succ (n : ℕ) : sat O (n + 1) = step O (sat O n) :=
  Function.iterate_succ_apply' _ _ _

theorem sat_subset_succ (n : ℕ) : sat O (n + 1) ⊆ sat O n := by
  rw [sat_succ]; exact step_subset O _

theorem sat_subset_cand (n : ℕ) : sat O n ⊆ cand O := by
  induction n with
  | zero => rw [sat_zero]
  | succ k ih => exact (sat_subset_succ O k).trans ih

/-- The good types persist through every elimination round (greatest direction). -/
theorem goodFS_subset_sat (n : ℕ) : goodFS O ⊆ sat O n := by
  induction n with
  | zero => rw [sat_zero]; exact goodFS_subset_cand O
  | succ k ih =>
      rw [sat_succ]
      intro t ht
      exact Finset.mem_filter.2 ⟨ih ht, realizedIn_mono O ih (goodFS_selfReal O t ht).2⟩

/-- While the chain has not stabilised it strictly shrinks, so after `n`
    non-trivial rounds it has lost at least `n` elements. -/
theorem sat_card_add_le (n : ℕ) (h : ∀ m, m < n → sat O m ≠ sat O (m + 1)) :
    (sat O n).card + n ≤ (cand O).card := by
  induction n with
  | zero => simp [sat_zero]
  | succ k ih =>
      have hk : ∀ m, m < k → sat O m ≠ sat O (m + 1) :=
        fun m hm => h m (Nat.lt_succ_of_lt hm)
      have ihk := ih hk
      have hne : sat O k ≠ sat O (k + 1) := h k (Nat.lt_succ_self k)
      have hss : sat O (k + 1) ⊆ sat O k := sat_subset_succ O k
      have hlt : (sat O (k + 1)).card < (sat O k).card :=
        Finset.card_lt_card ⟨hss, fun hsup => hne (Finset.Subset.antisymm hsup hss)⟩
      omega

/-- The chain stabilises within `|candidates|` rounds. -/
theorem exists_fixed : ∃ m ≤ (cand O).card, sat O m = sat O (m + 1) := by
  by_contra h
  have hall : ∀ m, m ≤ (cand O).card → sat O m ≠ sat O (m + 1) :=
    fun m hm heq => h ⟨m, hm, heq⟩
  have := sat_card_add_le O ((cand O).card + 1)
    (fun m hm => hall m (Nat.lt_succ_iff.1 hm))
  omega

/-- Once a round is a no-op, the chain is constant thereafter. -/
theorem sat_const_of_fixed {m : ℕ} (hm : sat O m = sat O (m + 1)) :
    ∀ k, sat O (m + k) = sat O m := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      have e : m + (j + 1) = (m + j) + 1 := by ring
      rw [e, sat_succ, ih, ← sat_succ, ← hm]

/-- The materialised set the strategy converges to: the elimination fixpoint. -/
noncomputable def saturate : Finset (Finset CName) := sat O ((cand O).card)

/-- The converged set is genuinely a fixpoint of elimination. -/
theorem saturate_fixed : step O (saturate O) = saturate O := by
  obtain ⟨m, hm_le, hm⟩ := exists_fixed O
  have e1 : saturate O = sat O m := by
    have : (cand O).card = m + ((cand O).card - m) := by omega
    rw [saturate, this]; exact sat_const_of_fixed O hm _
  have e2 : sat O ((cand O).card + 1) = sat O m := by
    have : (cand O).card + 1 = m + ((cand O).card + 1 - m) := by omega
    rw [this]; exact sat_const_of_fixed O hm _
  have e3 : step O (saturate O) = sat O ((cand O).card + 1) := (sat_succ O _).symm
  rw [e3, e2, e1]

theorem saturate_subset_cand : saturate O ⊆ cand O := sat_subset_cand O _

theorem goodFS_subset_saturate : goodFS O ⊆ saturate O := goodFS_subset_sat O _

/-- The converged set is self-realising. -/
theorem saturate_selfReal : SelfReal O (saturate O) := by
  intro t ht
  refine ⟨(mem_cand O).1 (saturate_subset_cand O ht), ?_⟩
  have hstep : t ∈ step O (saturate O) := by rw [saturate_fixed]; exact ht
  exact (Finset.mem_filter.1 hstep).2

/-- **The strategy's converged set is exactly the good types.** -/
theorem mem_saturate_iff_good (t : Finset CName) : t ∈ saturate O ↔ Good O t := by
  constructor
  · intro ht; exact ⟨saturate O, ht, saturate_selfReal O⟩
  · intro hg; exact goodFS_subset_saturate O ((mem_goodFS O).2 hg)

/-! ### Discharging strategy soundness, completeness, and the decision -/

theorem saturate_sound : StratSound O (fun t => t ∈ saturate O) :=
  fun t ht => (mem_saturate_iff_good O t).1 ht

theorem saturate_complete : StratComplete O (fun t => t ∈ saturate O) :=
  fun t hg => (mem_saturate_iff_good O t).2 hg

/-- **The saturation strategy decides subsumption exactly** — unconditionally,
    `sorry`-free.  The materialised set is the elimination fixpoint, which equals
    the good types, which decide `A ⊑ B` by `subsumption_complete`. -/
theorem saturate_decides (A B : CName) :
    (∀ t, t ∈ saturate O → A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) :=
  strategy_decides O (fun t => t ∈ saturate O) (saturate_sound O) (saturate_complete O) A B

/-! ### Bridge to the engine's *lazy* materialisation

`saturate` above eliminates from `cand O`, the set of *all* consistent types
(`2^|CName|` of them).  The Rust engine never enumerates that: it materialises a
finite candidate set `U` lazily (a root context per named concept, one successor
context per function symbol — the pay-as-you-go strategy) and eliminates from
`U`.  We show that **the lazy loop computes exactly the good types and decides
subsumption** under one explicit hypothesis, `coverage : goodFS O ⊆ U` — the
materialised set covers the good types.

This pins the entire remaining operational gap to that single, named property
(the lazy-completeness of per-`f` expansion: Core seeds every named concept and
Succ/Hyper generate every reachable good core).  Everything else — that
elimination never discards a good type, that it converges in `≤ |U|` rounds, that
the fixpoint it reaches is *exactly* the good types, and that the reported
subsumptions then decide `A ⊑ B` — is machine-checked here. Soundness needs no
such hypothesis at the abstract level. A production correspondence theorem and
mandatory wire checker are still required. -/

theorem iter_succ_subset (U : Finset (Finset CName)) (m : ℕ) :
    (step O)^[m + 1] U ⊆ (step O)^[m] U := by
  rw [Function.iterate_succ_apply']; exact step_subset O _

theorem iter_subset (U : Finset (Finset CName)) (n : ℕ) : (step O)^[n] U ⊆ U := by
  induction n with
  | zero => simp
  | succ k ih => exact (iter_succ_subset O U k).trans ih

/-- Elimination from `U` never discards a good type, as long as `U` had them. -/
theorem goodFS_subset_iter (U : Finset (Finset CName)) (hcov : goodFS O ⊆ U) (n : ℕ) :
    goodFS O ⊆ (step O)^[n] U := by
  induction n with
  | zero => simpa using hcov
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      intro t ht
      exact Finset.mem_filter.2 ⟨ih ht, realizedIn_mono O ih (goodFS_selfReal O t ht).2⟩

theorem iter_card_add_le (U : Finset (Finset CName)) (n : ℕ)
    (h : ∀ m, m < n → (step O)^[m] U ≠ (step O)^[m + 1] U) :
    ((step O)^[n] U).card + n ≤ U.card := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : ∀ m, m < k → (step O)^[m] U ≠ (step O)^[m + 1] U :=
        fun m hm => h m (Nat.lt_succ_of_lt hm)
      have ihk := ih hk
      have hne := h k (Nat.lt_succ_self k)
      have hss := iter_succ_subset O U k
      have hlt : ((step O)^[k + 1] U).card < ((step O)^[k] U).card :=
        Finset.card_lt_card ⟨hss, fun hsup => hne (Finset.Subset.antisymm hsup hss)⟩
      omega

theorem iter_exists_fixed (U : Finset (Finset CName)) :
    ∃ m ≤ U.card, (step O)^[m] U = (step O)^[m + 1] U := by
  by_contra h
  have hall : ∀ m, m ≤ U.card → (step O)^[m] U ≠ (step O)^[m + 1] U :=
    fun m hm heq => h ⟨m, hm, heq⟩
  have := iter_card_add_le O U (U.card + 1) (fun m hm => hall m (Nat.lt_succ_iff.1 hm))
  omega

theorem iter_const_of_fixed (U : Finset (Finset CName)) {m : ℕ}
    (hm : (step O)^[m] U = (step O)^[m + 1] U) :
    ∀ k, (step O)^[m + k] U = (step O)^[m] U := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      have e : m + (j + 1) = (m + j) + 1 := by ring
      rw [e, Function.iterate_succ_apply', ih]
      exact (Function.iterate_succ_apply' (step O) m U).symm.trans hm.symm

theorem iter_fixed (U : Finset (Finset CName)) :
    step O ((step O)^[U.card] U) = (step O)^[U.card] U := by
  obtain ⟨m, hm_le, hm⟩ := iter_exists_fixed O U
  have e1 : (step O)^[U.card] U = (step O)^[m] U := by
    have : U.card = m + (U.card - m) := by omega
    rw [this]; exact iter_const_of_fixed O U hm _
  have e2 : (step O)^[U.card + 1] U = (step O)^[m] U := by
    have : U.card + 1 = m + (U.card + 1 - m) := by omega
    rw [this]; exact iter_const_of_fixed O U hm _
  have e3 : step O ((step O)^[U.card] U) = (step O)^[U.card + 1] U :=
    (Function.iterate_succ_apply' _ _ _).symm
  rw [e3, e2, e1]

/-- **The lazy elimination loop computes exactly the good types**, given a
    consistent candidate set `U` that covers them. -/
theorem elim_eq_good (U : Finset (Finset CName))
    (hcov : goodFS O ⊆ U) (hcons : U ⊆ cand O) :
    (step O)^[U.card] U = goodFS O := by
  apply Finset.Subset.antisymm
  · intro t ht
    have hself : SelfReal O ((step O)^[U.card] U) := by
      intro u hu
      refine ⟨(mem_cand O).1 (hcons (iter_subset O U _ hu)), ?_⟩
      have huf : u ∈ step O ((step O)^[U.card] U) := by rw [iter_fixed]; exact hu
      exact (Finset.mem_filter.1 huf).2
    exact (mem_goodFS O).2 ⟨_, ht, hself⟩
  · exact goodFS_subset_iter O U hcov _

/-- **Per-run completeness bridge.**  The subsumptions the engine reports from the
    set its lazy elimination converges to decide `A ⊑ B` exactly — under the
    single residual hypothesis `coverage : goodFS O ⊆ U`. -/
theorem engine_decides (U : Finset (Finset CName))
    (hcov : goodFS O ⊆ U) (hcons : U ⊆ cand O) (A B : CName) :
    (∀ t ∈ (step O)^[U.card] U, A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) := by
  rw [elim_eq_good O U hcov hcons, subsumption_complete O A B]
  exact ⟨fun h t hg hA => h t ((mem_goodFS O).2 hg) hA,
         fun h t ht hA => h t ((mem_goodFS O).1 ht) hA⟩

/-- `coverage` for the engine's candidate set follows from seeding every consistent
    type: a good type is consistent, hence covered.  (The Rust engine seeds a root
    context for every named concept; classification queries them all, so every
    *nonempty* good type — each contains a named concept — is represented, and the
    consistent-type candidate space below covers the rest.) -/
theorem coverage_of_seeds {U : Finset (Finset CName)}
    (hseed : ∀ t, consistent O t → t ∈ U) : goodFS O ⊆ U := by
  intro t ht
  rw [mem_goodFS] at ht
  obtain ⟨G, htG, hG⟩ := ht
  exact hseed t (hG t htG).1

/-- **Coverage discharged — type-level completeness is unconditional.**

    The engine's pre-elimination candidate space, at the type level, is *all*
    consistent types `cand O` (its disjunctive context clauses represent exactly
    this space — a few contexts standing in for the whole consistent-type set,
    which elimination then trims to `goodFS`).  Instantiating `engine_decides` at
    `U = cand O` discharges `coverage` outright via `goodFS_subset_cand`, so the
    decision carries **no residual hypothesis**.  (This is `saturate_decides` seen
    through the `engine_decides` lens.)

    What remains between this theorem and the running Rust binary is *only* the
    representation refinement: the engine manipulates disjunctive context clauses
    rather than enumerated types, and that the clause saturation computes the same
    `goodFS` is the disjunctive-saturation completeness.
    `CheckerTerm.certifies_subsumptionT` proves soundness for any accepted
    generated derivation, but no mandatory production CB checker is wired yet.
    Empirical benchmark agreement is regression evidence, not a proof. -/
theorem engine_complete (A B : CName) :
    (∀ t ∈ saturate O, A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) :=
  engine_decides O (cand O) (goodFS_subset_cand O) (Finset.Subset.refl _) A B

end Strategy

end ContextCalculus.Ctx
