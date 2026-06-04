/-
  ContextCalculus/CompletenessStrategy.lean
  ==========================================
  **SCAFFOLD — completeness of the *pay-as-you-go* expansion strategy.**

  The engine (`engine/src/engine.rs`) was changed from the *trivial* expansion
  strategy (one shared empty-core successor context for every anonymous
  successor) to a *pay-as-you-go* strategy: **one successor context per function
  symbol `f`** (`successor_for`).  This file scaffolds the completeness argument
  for that strategy.

  What is established here (no `sorry`):

    * `strategy_decides` — the **reduction theorem**.  For *any* expansion
      strategy whose materialised set of type-contexts `G` is **sound**
      (`G ⊆ good types`) and **complete** (`good types ⊆ G`), the engine reports
      `A ⊑ B` (every materialised type carrying `A` carries `B`) **iff**
      `O ⊨ A ⊑ B`.  This is a direct corollary of the calculus's good-type
      completeness `CompletenessContext.subsumption_complete`, which is itself
      `sorry`-free.  So strategy completeness is *entirely* reduced to the
      question "does the strategy materialise exactly the good types?".

  What remains open (the two `sorry`s, precisely isolated):

    * `perF_sound`     — every type-context the per-`f` engine materialises is a
      good type.  This is the **soundness** direction; operationally it is the
      guarantee the per-run Lean certificate checker (`CheckerTerm.lean`,
      `certifies_subsumptionT`) re-establishes on every run, so it is already
      machine-checked *per run* even though it is not yet proved schematically
      here.
    * `perF_complete`  — every good type is materialised by per-`f` expansion.
      This is the **completeness** direction, and it is the genuine
      Bachmair–Ganzinger ordered-resolution content that `lean/README` lists
      under "What is NOT claimed": resolving only on maximal literals and
      expanding successors lazily is a refutation-complete *restriction* of full
      closure.  Discharging it for `PerF` below (and refining `PerF` so it
      mirrors the engine's reachability exactly — query-root closure under the
      GCIs, and one `compat` successor per `exRight` demand) is the remaining
      formalisation effort.

  Once both obligations are discharged, `perF_decides` becomes an unconditional
  completeness theorem for the shipped strategy.
-/
import ContextCalculus.CompletenessContext

namespace ContextCalculus.Ctx

section Strategy

variable {CName Role : Type} [Fintype CName] [DecidableEq CName] [DecidableEq Role]
variable (O : Ontology CName Role)

/-- A strategy *outcome* `G` (the set of type-contexts a strategy materialises at
    its fixpoint) is **sound** when every materialised type is a good type. -/
def StratSound (G : Finset CName → Prop) : Prop := ∀ t, G t → Good O t

/-- A strategy outcome `G` is **complete** when every good type is materialised. -/
def StratComplete (G : Finset CName → Prop) : Prop := ∀ t, Good O t → G t

/-- **Reduction theorem (proved).**  A sound + complete strategy outcome `G`
    decides atomic subsumption exactly: the engine's report (`A` carried by a
    materialised type forces `B`) holds iff `O ⊨ A ⊑ B`.

    The whole proof is `subsumption_complete` (good types decide subsumption)
    plus set inclusion both ways between `G` and the good types. -/
theorem strategy_decides (G : Finset CName → Prop)
    (hs : StratSound O G) (hc : StratComplete O G) (A B : CName) :
    (∀ t, G t → A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) := by
  rw [subsumption_complete O A B]
  exact ⟨fun h t hg hA => h t (hc t hg) hA, fun h t hg hA => h t (hs t hg) hA⟩

/-- A type-level model of the **per-`f` strategy's** materialised contexts: the
    types reachable from a consistent root by following each existential demand
    `a ⊑ ∃r.b` across a `compat`ible edge — one successor context per skolem `f`
    (each `exRight` occurrence is a distinct `f`).  This is the structure the
    Rust `successor_for` builds.  (The model is intentionally coarse for the
    scaffold; refining it to the engine's exact reachability is part of the open
    work flagged in the header.) -/
inductive PerF : Finset CName → Prop
  | root (t : Finset CName) (hcons : consistent O t) : PerF t
  | succ {t s : Finset CName} {a b : CName} {r : Role}
      (ht : PerF t) (hex : Clause.exRight a r b ∈ O) (ha : a ∈ t)
      (hb : b ∈ s) (hco : compat O r t s) (hcons : consistent O s) : PerF s

/-- **OBLIGATION (soundness).**  Every type-context the per-`f` engine materialises
    is good.  Discharged operationally per run by the certificate checker
    (`certifies_subsumptionT`); not yet proved schematically. -/
theorem perF_sound : StratSound O (PerF O) := by
  sorry

/-- **OBLIGATION (completeness).**  Every good type is materialised by per-`f`
    expansion.  This is the Bachmair–Ganzinger ordered-resolution completeness
    of the lazy/maximal-literal strategy (`lean/README`, "What is NOT claimed",
    item 2); the trivial strategy has it by full closure. -/
theorem perF_complete : StratComplete O (PerF O) := by
  sorry

/-- **The pay-as-you-go strategy decides subsumption exactly** — unconditional
    once the two obligations above are discharged.  The reduction itself
    (`strategy_decides`) is proved. -/
theorem perF_decides (A B : CName) :
    (∀ t, PerF O t → A ∈ t → B ∈ t)
      ↔ (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x) :=
  strategy_decides O (PerF O) (perF_sound O) (perF_complete O) A B

end Strategy

end ContextCalculus.Ctx
