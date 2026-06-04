/-
  ContextCalculus/CompletenessStrategy.lean
  ==========================================
  **Completeness of the saturation strategy the engine runs.**

  `engine/src/engine.rs` classifies by *consequence-based type-elimination*: it
  seeds the candidate contexts and repeatedly discards any context whose
  existential demands (`a ⊑ ∃r.b`) are no longer realised by a surviving
  context, until a fixpoint is reached.  The *pay-as-you-go* expansion strategy
  (one successor context per function symbol) only changes how the surviving
  contexts are *represented*; the **set of contexts it converges to is exactly
  this elimination fixpoint** (the benchmark confirms verdicts are byte-identical
  to the trivial strategy).  This file proves that fixpoint decides subsumption.

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

  Scope note (unchanged from `lean/README`): this is the ALCHIQ type-level
  argument.  It establishes that *some* terminating elimination computes the good
  types; the remaining engineering obligation is the operational refinement that
  the Rust per-`f` data structures realise this abstract `step` — the verdict
  identity to the trivial strategy is checked empirically, and the per-run
  certificate checker re-establishes soundness on every run.
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

end Strategy

end ContextCalculus.Ctx
