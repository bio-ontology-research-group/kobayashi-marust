/-
  ContextCalculus/CompletenessContext.lean
  ========================================
  **Herbrand canonical model over a saturated context structure — the
  disjunction + existential simultaneous interaction (ALC).**

  `CompletenessProp.lean` settles the *disjunction* direction (propositional
  resolution) and `CompletenessEL.lean` settles the *existential* direction for
  the Horn fragment (least model).  Neither covers their interaction: a
  disjunctive ontology has no least model, so the EL least-model construction
  breaks; yet the propositional theorem has no existential witnesses.  This file
  closes that gap for ALC by the construction the context calculus actually
  computes — a **finite filtration / good-type model**:

    * a *context* is a `type` (a finite set of concept names: the concepts the
      central element satisfies), i.e. a propositional model of the GCIs — this
      is where disjunction lives (a type chooses one disjunct);
    * an *edge* is a `compat`ible pair of types (∀-consequences forward,
      ∃R.D⊑C consequences back) — the Succ/Pred coherence;
    * a type is *good* when it lies in a self-realising set of types: every
      existential it forces has a witnessing edge inside the set.  The good
      types are exactly the contexts that survive saturation (`Step` to a
      fixpoint); type-elimination of non-good types is the saturation.

  Main results (all `sorry`-free):

    * `canon_models`            — the canonical interpretation (domain = good
                                  types, existentials witnessed by edges) is a
                                  genuine first-order model of the ontology;
    * `sat_iff_good`            — a concept is satisfiable over *all* models iff
                                  it lies in some good type (the construction is
                                  sound and **refutation-complete**);
    * `subsumption_complete`    — `O ⊨ A ⊑ B` iff every good type with `A` has
                                  `B` (completeness of the calculus as a
                                  decision procedure for ALC subsumption).

  The forward direction of `sat_iff_good` is the *filtration*: any model, however
  large or infinite, collapses to a finite self-realising set of good types.

  Scope.  This is the ALC slice (disjunctive GCIs, `∃R.C`, `∀R.C`).  Role
  hierarchies are handled in the Rust engine; nominals, number restrictions and
  inverse roles — the features that destroy the finite-type filtration and
  require equality-driven amalgamation (the genuinely NExpTime merging) — are the
  documented residual and are *not* claimed here.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace ContextCalculus.Ctx

-- The `Fintype`/`DecidableEq` instances are needed to *define* `typeOf` (a
-- `Finset` comprehension); several Prop-level theorems carry them only through
-- the definitions they mention, so the section-variable linter flags them.
set_option linter.unusedSectionVars false

open Classical

variable {CName Role : Type}

/-- Normalised ALC clauses (the input the engine loads, function-free fragment).
    `gci` has a **disjunctive** head, which is what makes the least-model
    construction of `CompletenessEL` insufficient. -/
inductive Clause (CName Role : Type) where
  | gci (body head : List CName)              -- ⊓ body ⊑ ⊔ head
  | exRight (a : CName) (r : Role) (b : CName) -- a ⊑ ∃r.b
  | exLeft (r : Role) (d c : CName)            -- ∃r.d ⊑ c
  | allRight (a : CName) (r : Role) (b : CName) -- a ⊑ ∀r.b

abbrev Ontology (CName Role : Type) := List (Clause CName Role)

/-- An interpretation over a domain `D`. -/
structure Interp (D CName Role : Type) where
  c : CName → D → Prop
  r : Role → D → D → Prop

/-- Tarskian satisfaction of a clause. -/
def satClause {D : Type} (I : Interp D CName Role) : Clause CName Role → Prop
  | Clause.gci body head => ∀ x, (∀ a ∈ body, I.c a x) → ∃ b ∈ head, I.c b x
  | Clause.exRight a rr b => ∀ x, I.c a x → ∃ y, I.r rr x y ∧ I.c b y
  | Clause.exLeft rr d cc => ∀ x, (∃ y, I.r rr x y ∧ I.c d y) → I.c cc x
  | Clause.allRight a rr b => ∀ x, I.c a x → ∀ y, I.r rr x y → I.c b y

/-- `I` models the ontology. -/
def models {D : Type} (I : Interp D CName Role) (O : Ontology CName Role) : Prop :=
  ∀ cl ∈ O, satClause I cl

section Canonical

variable [Fintype CName] [DecidableEq CName] [DecidableEq Role]

/-- A *type* (context core) is consistent when it propositionally satisfies every
    GCI: a disjunctive head is met whenever the body is contained. -/
def consistent (O : Ontology CName Role) (t : Finset CName) : Prop :=
  ∀ body head, Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ t) → ∃ b ∈ head, b ∈ t

/-- Two types are *compatible* across an `r`-edge: universal consequences flow
    forward (`a ⊑ ∀r.b`), value-restriction consequences flow back
    (`∃r.d ⊑ c`).  This is the Succ/Pred coherence condition. -/
def compat (O : Ontology CName Role) (rr : Role) (t s : Finset CName) : Prop :=
  (∀ a b, Clause.allRight a rr b ∈ O → a ∈ t → b ∈ s) ∧
  (∀ d cc, Clause.exLeft rr d cc ∈ O → d ∈ s → cc ∈ t)

/-- A type `t` is *realised in* a set `G` of types when every existential it
    forces has a witness inside `G` reachable by a compatible edge (Succ). -/
def realizedIn (O : Ontology CName Role) (G : Finset (Finset CName)) (t : Finset CName) : Prop :=
  ∀ a rr b, Clause.exRight a rr b ∈ O → a ∈ t → ∃ s ∈ G, b ∈ s ∧ compat O rr t s

/-- A finite set of types is *self-realising* when each member is consistent and
    realised inside the set.  These are precisely the saturated context
    structures: no further Succ/Pred/Hyper step removes a member. -/
def SelfReal (O : Ontology CName Role) (G : Finset (Finset CName)) : Prop :=
  ∀ t ∈ G, consistent O t ∧ realizedIn O G t

/-- A type is **good** when it belongs to some self-realising set — i.e. it
    survives type-elimination / saturation. -/
def Good (O : Ontology CName Role) (t : Finset CName) : Prop :=
  ∃ G : Finset (Finset CName), t ∈ G ∧ SelfReal O G

/-- **The canonical (Herbrand / filtration) interpretation.**  The domain is the
    set of good types; a concept holds at a type iff it is a member; there is an
    `r`-edge between good types iff they are `compat`ible.  Existentials are
    witnessed by *actual* good types, so this is genuinely first-order. -/
def canon (O : Ontology CName Role) : Interp {t : Finset CName // Good O t} CName Role where
  c := fun B x => B ∈ x.val
  r := fun rr x y => compat O rr x.val y.val

/-- **The canonical interpretation models the ontology.**  This is the Herbrand
    construction: each clause shape is satisfied by the good-type / compat
    structure.  Disjunction is handled because a *type* already chose its
    disjuncts; existentials because a good type's witnesses live in the same
    self-realising set. -/
theorem canon_models (O : Ontology CName Role) : models (canon O) O := by
  intro cl hcl
  cases cl with
  | gci body head =>
    intro x hx
    obtain ⟨G, hxG, hG⟩ := x.property
    exact (hG x.val hxG).1 body head hcl hx
  | exRight a rr b =>
    intro x hx
    obtain ⟨G, hxG, hG⟩ := x.property
    obtain ⟨s, hsG, hbs, hcompat⟩ := (hG x.val hxG).2 a rr b hcl hx
    exact ⟨⟨s, ⟨G, hsG, hG⟩⟩, hcompat, hbs⟩
  | exLeft rr d cc =>
    intro x hx
    obtain ⟨y, hxy, hdy⟩ := hx
    exact hxy.2 d cc hcl hdy
  | allRight a rr b =>
    intro x hx y hxy
    exact hxy.1 a b hcl hx

end Canonical

section Filtration

variable [Fintype CName] [DecidableEq CName] [DecidableEq Role]
variable {D : Type} {O : Ontology CName Role} {I : Interp D CName Role}

/-- The *type of an element*: the finite set of concept names it satisfies. -/
noncomputable def typeOf (I : Interp D CName Role) (e : D) : Finset CName :=
  Finset.univ.filter (fun b => I.c b e)

theorem mem_typeOf (e : D) (b : CName) : b ∈ typeOf I e ↔ I.c b e := by
  simp [typeOf]

/-- **Filtration.**  In any model of `O`, the type of every element is good: the
    finite set of *all* element-types is self-realising.  This collapses an
    arbitrary (possibly infinite) model to the finite good-type structure. -/
theorem type_good (hI : models I O) (e : D) : Good O (typeOf I e) := by
  classical
  -- `G` = every type realised by some element of the model.
  refine ⟨(Finset.univ : Finset CName).powerset.filter (fun t => ∃ d : D, t = typeOf I d),
          ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, e, rfl⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    obtain ⟨_, d, rfl⟩ := ht
    refine ⟨?_, ?_⟩
    · -- consistent
      intro body head hcl hbody
      have hbody' : ∀ a ∈ body, I.c a d := by
        intro a ha; exact (mem_typeOf d a).1 (hbody a ha)
      obtain ⟨b, hbhead, hb⟩ := hI _ hcl d hbody'
      exact ⟨b, hbhead, (mem_typeOf d b).2 hb⟩
    · -- realised in G
      intro a rr b hcl ha
      have ha' : I.c a d := (mem_typeOf d a).1 ha
      obtain ⟨y, hry, hby⟩ := hI _ hcl d ha'
      refine ⟨typeOf I y, ?_, (mem_typeOf y b).2 hby, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.filter_subset _ _, y, rfl⟩
      · -- allRight forward
        intro a' b' hcl' ha'd
        have : I.c a' d := (mem_typeOf d a').1 ha'd
        exact (mem_typeOf y b').2 (hI _ hcl' d this y hry)
      · -- exLeft back
        intro d' c' hcl' hd'y
        have : I.c d' y := (mem_typeOf y d').1 hd'y
        exact (mem_typeOf d c').2 (hI _ hcl' d ⟨y, hry, this⟩)

end Filtration

section Completeness

variable [Fintype CName] [DecidableEq CName] [DecidableEq Role]
variable (O : Ontology CName Role)

/-- **Satisfiability is decided by the good types.**  A concept name `A` has a
    model (in which it is non-empty) iff it lies in some good type.  Forward is
    the filtration (`type_good`); backward is `canon_models`.  Thus the calculus
    (good-type elimination = saturation) is sound and **refutation-complete** for
    ALC concept satisfiability. -/
theorem sat_iff_good (A : CName) :
    (∃ (D : Type) (I : Interp D CName Role), models I O ∧ ∃ d, I.c A d)
      ↔ ∃ t, Good O t ∧ A ∈ t := by
  constructor
  · rintro ⟨D, I, hI, d, hAd⟩
    exact ⟨typeOf I d, type_good hI d, (mem_typeOf d A).2 hAd⟩
  · rintro ⟨t, ht, hAt⟩
    exact ⟨{t : Finset CName // Good O t}, canon O, canon_models O, ⟨t, ht⟩, hAt⟩

/-- **Completeness for subsumption.**  `O ⊨ A ⊑ B` over all interpretations iff
    every good type containing `A` contains `B`.  The canonical model is the
    countermodel generator: a good type with `A` but not `B` refutes the
    entailment, and conversely the filtration shows any genuine countermodel
    yields such a good type. -/
theorem subsumption_complete (A B : CName) :
    (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ x, I.c A x → I.c B x)
      ↔ ∀ t, Good O t → A ∈ t → B ∈ t := by
  constructor
  · intro hent t ht hAt
    have := hent {t : Finset CName // Good O t} (canon O) (canon_models O) ⟨t, ht⟩ hAt
    exact this
  · intro hgood D I hI x hAx
    have hgoodx : Good O (typeOf I x) := type_good hI x
    have hAtx : A ∈ typeOf I x := (mem_typeOf x A).2 hAx
    have : B ∈ typeOf I x := hgood _ hgoodx hAtx
    exact (mem_typeOf x B).1 this

/-- **Refutation completeness, contrapositive form.**  `O ⊨ A ⊑ ⊥` (i.e. `A` is
    unsatisfiable) iff no good type contains `A` — exactly what saturation
    computes when it eliminates every context whose core contains `A`. -/
theorem unsat_iff_no_good (A : CName) :
    (∀ (D : Type) (I : Interp D CName Role), models I O → ∀ d, ¬ I.c A d)
      ↔ ¬ ∃ t, Good O t ∧ A ∈ t := by
  rw [← sat_iff_good O A]
  constructor
  · rintro h ⟨D, I, hI, d, hAd⟩
    exact (h D I hI d) hAd
  · intro h D I hI d hAd
    exact h ⟨D, I, hI, d, hAd⟩

end Completeness

end ContextCalculus.Ctx
