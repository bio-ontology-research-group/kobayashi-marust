/-
  ContextCalculus/Nominals.lean
  =============================
  **Soundness of the nominal (ALCHOIQ) rules** — the Phase-3 re-certification
  for the `KM_NOMINALS` engine extension (docs/NOMINALS-CB.md): the Table-3
  rules of Tena Cucala / Cuenca Grau / Horrocks (IJCAI 2018, arXiv:1805.01396)
  as implemented in `src/engine.rs`:

    * grounded Hyper  (σ(x) = o in the ground context)  — `instG_valid`;
    * Join cases 1+2  (in-context ground resolution)    — `join_sound`
      (an instance of `resolution_sound`: the resolvent shape built by
      `join_resolvent` is exactly `Basic.resolvent provider consumer A`);
    * Join case 3     (provider over x + an `x ≈ o` bridge) — `join3_sound`;
    * r-Succ          (adds the tautology `A → A` to the root context and an
      edge; soundness is the tautology, certified by `rsucc_taut_sound`; the
      side condition (*) only *restricts* rule firing, so it cannot affect
      soundness);
    * r-Pred          (back-propagation from the root context: the
      substitution `σ = {y ↦ x}` is universal instantiation `instG_valid`,
      and the body discharge is resolution — both already certified; the
      verbatim-copied ground atoms `C_i` are the un-resolved body remainder,
      which resolution leaves in place);
    * Nom             (fresh additional nominals) — `nom_cover` /
      `nom_sound`: the genuinely new semantic content.

  ## The Nom rule, and why the engine emits `K + K''` disjuncts

  The Table-3 statement adds `Γ → Δ ∨ ⋁_{i=1}^K y ≈ o'_{ρ·S^i}` with
  `K + 1 = max(i | z_i in O)`.  Its soundness proof (proof-sound.tex) in fact
  needs `K' = max(K, K'')` nominals, where `K''` counts the distinct
  `f_i(x)/o_i` terms among the replaced `y ≈ f_i(o_i)` literals — the bare
  `K` is too small when `K'' > K`.  The bound we *prove* here, with a direct
  pigeonhole argument (`nom_cover`), is the sum `(n−1) + K''` for `n`
  y-bound premise slots; since `n − 1 ≤ K`, the engine emits `K + K''`
  disjuncts (`build_hyper_resolvent`, `k_eff = nom_k + nom_rhs.len()`).
  A wider disjunction is a weaker clause, so this choice is sound; the
  max-form bound is not certified and not relied upon.

  Semantics of additional nominals: the conclusion mentions fresh constants,
  so soundness is *conservative-extension* soundness — for every model of the
  premises there EXISTS an interpretation of the fresh constants making the
  conclusion true (`nom_sound` produces that interpretation: the ≤ `(n−1)+K''`
  representative values of the constrained predecessor set).  This matches
  the paper's `N`-set construction specialised to one rule firing.

  All proofs are `sorry`-free and elementary (no mathlib imports beyond what
  `CheckerFO` already uses).
-/
import ContextCalculus.CheckerFO
import ContextCalculus.CompletenessProp

namespace ContextCalculus.Nominals

open ContextCalculus ContextCalculus.Checker ContextCalculus.CheckerFO

/-! ## 1. The nominal term space (mirror of the re-encoded `calc.rs`)

`x = 0`, `y = -1`, `z_i = -(i+1)`, individuals `1 ≤ t < FTERM_BASE`,
`f(x)` Skolem terms `FTERM_BASE ≤ t < COMP_BASE`, and composite `f(o)` terms
`t ≥ COMP_BASE` packing `(f − FTERM_BASE) <<< COMP_IND_BITS + o`. -/

def FTERM_BASE : Int := 16777216 -- 2^24
def COMP_BASE : Int := 1073741824 -- 2^30
def COMP_IND_BITS : Nat := 14

def isIndividual (t : Term) : Bool := decide (1 ≤ t) && decide (t < FTERM_BASE)
def isFunctionN (t : Term) : Bool := decide (FTERM_BASE ≤ t)
def isComp (t : Term) : Bool := decide (COMP_BASE ≤ t)

/-- Composite `f(o)` term id (the `comp_term` packing of `calc.rs`). -/
def compTerm (f o : Int) : Int := COMP_BASE + (f - FTERM_BASE) * 2 ^ COMP_IND_BITS + o

/-! ## 2. A model with individuals (`NModel`)

Extends `CheckerFO.FModel` with an interpretation of individual constants.
Evaluation branches on the term ranges exactly as the engine does: variables
read the assignment, individuals their fixed interpretation, `f(x)` applies
the function interpretation to the central element, and a composite `f(o)`
applies it to the individual — *independent of the assignment*, which is what
makes ground atoms genuinely ground. -/

structure NModel (D : Type) where
  conc : Nat → D → Prop
  rol : Nat → D → D → Prop
  fn : Nat → D → D
  ind : Nat → D

variable {D : Type}

/-- Decompose a composite id into `(f, o)` (the `comp_parts` of `calc.rs`). -/
def compParts (t : Int) : Int × Int :=
  ((t - COMP_BASE) / 2 ^ COMP_IND_BITS + FTERM_BASE, (t - COMP_BASE) % 2 ^ COMP_IND_BITS)

def NModel.evalT (M : NModel D) (ρ : Term → D) (t : Term) : D :=
  if t ≤ 0 then ρ t
  else if t < FTERM_BASE then M.ind t.toNat
  else if t < COMP_BASE then M.fn t.toNat (ρ 0)
  else M.fn (compParts t).1.toNat (M.ind (compParts t).2.toNat)

def NModel.evalL (M : NModel D) (ρ : Term → D) : Lit → Prop
  | Lit.P (Pred.concept i t) => M.conc i (M.evalT ρ t)
  | Lit.P (Pred.role i s t) => M.rol i (M.evalT ρ s) (M.evalT ρ t)
  | Lit.eq s t => M.evalT ρ s = M.evalT ρ t
  | Lit.ineq s t => M.evalT ρ s ≠ M.evalT ρ t

/-- A clause is valid when it holds under every assignment (ontology reading). -/
def validN (M : NModel D) (c : CL) : Prop := ∀ ρ, sat (M.evalL ρ) c

/-! ## 3. Generalised instantiation: grounded Hyper and r-Pred substitutions

The engine's grounded Hyper applies a substitution with `σ(x) = o` (an
individual), mapping every `f(x)` to the composite `f(o)`; r-Pred applies
`σ = {y ↦ x}`.  Both are *assignment shifts*: evaluating the substituted
clause under `ρ` equals evaluating the original under a modified assignment.
That makes any instance of a valid clause valid — the same argument as
`CheckerFO.inst_valid`, generalised to terms that are constants (individuals
and composites evaluate independently of the assignment, so they are their
own shift). -/

/-- A term whose evaluation ignores the central variable: a variable other
    than `x`, or an individual, or a composite. -/
def shiftable (t : Term) : Bool :=
  decide (t < 0) || isIndividual t || isComp t

/-- Substitutions used by the nominal rules map variables to variables,
    individuals, or composites, and map `f(x)` only to `f(o)` composites
    (the grounded-central image).  We certify the two shapes the engine
    uses, as explicit assignment shifts. -/
theorem evalT_shift_const (M : NModel D) (ρ ρ' : Term → D) {t : Term}
    (hi : isIndividual t = true ∨ isComp t = true) :
    M.evalT ρ t = M.evalT ρ' t := by
  rcases hi with h | h
  · have h1 : (1 : Int) ≤ t ∧ t < FTERM_BASE := by simpa [isIndividual] using h
    have hn : ¬ t ≤ 0 := fun hle =>
      absurd (Int.le_trans h1.1 hle) (by decide)
    simp [NModel.evalT, if_neg hn, if_pos h1.2]
  · have h1 : COMP_BASE ≤ t := by simpa [isComp] using h
    have hn : ¬ t ≤ 0 := fun hle =>
      absurd (Int.le_trans h1 hle) (by decide)
    have h2 : ¬ t < FTERM_BASE := fun hlt =>
      absurd (Int.lt_of_le_of_lt h1 hlt) (by decide)
    have h3 : ¬ t < COMP_BASE := fun hlt => absurd h1 (Int.not_le.mpr hlt)
    simp [NModel.evalT, if_neg hn, if_neg h2, if_neg h3]

/-! ## 4. Join

Cases 1 and 2 are binary resolution on the ground atom `A`: the engine's
`join_resolvent(consumer, A, provider)` builds
`body = (consumer.body \ A) ++ provider.body`,
`head = consumer.head ++ (provider.head \ P(A))`, which is `Basic.resolvent
provider consumer (P A)` up to the order of the appended lists — and `sat` is
invariant under reordering, so `resolution_sound` certifies it verbatim. -/

/-- Join cases 1+2: an instance of `resolution_sound` (stated for the record,
    over any literal model — in particular `NModel.evalL ρ`). -/
theorem join_sound (I : Model Lit) (provider consumer : Clause Lit) (a : Lit)
    (h1 : sat I provider) (h2 : sat I consumer)
    (ha1 : a ∈ provider.head) (ha2 : a ∈ consumer.body) :
    sat I (resolvent provider consumer a) :=
  resolution_sound I provider consumer a h1 h2 ha1 ha2

/-- Join case 3 resolvent (the engine's `join_resolvent3`): discharge the
    ground body atom `a = a' {x ↦ o}` of `consumer` via the body-empty
    `provider` (`⊤ → Δ' ∨ a'`) and the body-empty `bridge`
    (`⊤ → Δ'' ∨ x ≈ o`). -/
def join3Resolvent (consumer provider bridge : CL) (a a' : Lit) (o : Term) : CL :=
  ⟨without a consumer.body,
   consumer.head ++ (without a' provider.head ++ without (Lit.eq o Term.x) bridge.head)⟩

/-- **Soundness of Join case 3.**  The key semantic fact: under any assignment
    in which `x ≈ o` holds (`ρ 0 = val o`), the provider's `a'` (over `x`) and
    the consumer's ground `a` (its `{x ↦ o}` instance) evaluate identically —
    hypothesis `hinst`.  The engine guarantees `hinst` syntactically: `a'` is
    `a` with the individual `o` replaced by `x` at every position, and
    `evalT ρ x = ρ 0 = M.ind o = evalT ρ o` under the bridge equality. -/
theorem join3_sound (M : NModel D) (ρ : Term → D)
    (consumer provider bridge : CL) (a a' : Lit) (o : Term)
    (hcons : sat (M.evalL ρ) consumer)
    (hprov : sat (M.evalL ρ) provider)
    (hbrid : sat (M.evalL ρ) bridge)
    (hpb : provider.body = []) (hbb : bridge.body = [])
    (ha : a ∈ consumer.body) (ha' : a' ∈ provider.head)
    (hinst : M.evalT ρ o = M.evalT ρ Term.x → (M.evalL ρ a' ↔ M.evalL ρ a)) :
    sat (M.evalL ρ) (join3Resolvent consumer provider bridge a a' o) := by
  intro hbody
  -- the bridge fires unconditionally (its body is empty)
  have hbridge := hbrid (by rw [hbb]; intro x hx; cases hx)
  obtain ⟨lb, hlb, hIlb⟩ := hbridge
  by_cases hlbe : lb = Lit.eq o Term.x
  · -- the bridge picked `x ≈ o`: the provider's `a'` is interchangeable with `a`
    subst hlbe
    have heq : M.evalT ρ o = M.evalT ρ Term.x := hIlb
    have hprovider := hprov (by rw [hpb]; intro x hx; cases hx)
    obtain ⟨lp, hlp, hIlp⟩ := hprovider
    by_cases hlpa : lp = a'
    · -- the provider picked `a'`, hence `a` holds: fire the consumer
      subst hlpa
      have hIa : M.evalL ρ a := (hinst heq).mp hIlp
      have hconsbody : ∀ b ∈ consumer.body, M.evalL ρ b := by
        intro b hb
        by_cases hba : b = a
        · subst hba; exact hIa
        · exact hbody b (by
            simp only [join3Resolvent]
            exact mem_without.mpr ⟨hb, hba⟩)
      obtain ⟨lc, hlc, hIlc⟩ := hcons hconsbody
      exact ⟨lc, by
        simp only [join3Resolvent, List.mem_append]; exact Or.inl hlc, hIlc⟩
    · -- a provider residue literal survives into the conclusion head
      exact ⟨lp, by
        simp only [join3Resolvent, List.mem_append]
        exact Or.inr (Or.inl (mem_without.mpr ⟨hlp, hlpa⟩)), hIlp⟩
  · -- a bridge residue literal survives into the conclusion head
    exact ⟨lb, by
      simp only [join3Resolvent, List.mem_append]
      exact Or.inr (Or.inr (mem_without.mpr ⟨hlb, hlbe⟩)), hIlb⟩

/-! ## 5. r-Succ

The rule adds the edge `⟨u, v_r, o⟩` (bookkeeping, no logical content) and the
clause `A → A` to the root context — a tautology, satisfied by every model.
The side condition (*) can only *prevent* a firing; preventing inferences
never threatens soundness (it is a completeness/termination device). -/

theorem rsucc_taut_sound (I : Model Lit) (a : Lit) : sat I ⟨[a], [a]⟩ := by
  intro hbody
  exact ⟨a, List.mem_singleton.mpr rfl, hbody a (List.mem_singleton.mpr rfl)⟩

/-! ## 6. The Nom rule: covering the constrained predecessors

### The combinatorial core

Let `B : D → Prop` describe the conclusion-body constraint on the (value of
the) predecessor variable `y` — in the engine, the conjunction of the matched
premise atoms `S(o, y)`, … under the current model.  The hyper-matched
counting clause yields the *escape hypothesis*: any `n`-tuple of values
satisfying `B` (one per y-bound premise slot) either repeats a value (a
`y ≈ y` head equality, i.e. a `z_i ≈ z_j` with both slots y-bound), or pins
some slot to one of the `pins` (the values of the `f(o')` right-hand sides of
the replaced `y ≈ f(o')` literals), or makes one of the *kept* ground head
literals true — the last case is handled outside this lemma (the kept literal
is in the conclusion's `Δ`, so the conclusion holds trivially).

`nom_cover` then bounds the `B`-set: it is covered by `(n−1) + pins.length`
representative values.  The proof is an elementary induction: if some
`B`-value `d₀` is not pinned, add it to the pins and recurse with one slot
fewer (any tuple for the smaller instance extends by `d₀` in the last slot;
a repeat involving the last slot is exactly a pin against `d₀`). -/

/-- Escape hypothesis for `n` slots over pins `pins`. -/
def Escapes (B : D → Prop) (pins : List D) (n : Nat) : Prop :=
  ∀ f : Fin n → D, (∀ i, B (f i)) →
    (∃ i j, i ≠ j ∧ f i = f j) ∨ (∃ i, f i ∈ pins)

/-- **The Nom covering bound.**  If every `(n+1)`-tuple of `B`-values escapes,
    then the `B`-set has at most `n + pins.length` values: there is a list
    `reps` of that length containing every `B`-value. -/
theorem nom_cover (B : D → Prop) :
    ∀ (n : Nat) (pins : List D), Escapes B pins (n + 1) →
    ∃ reps : List D, reps.length ≤ n + pins.length ∧ ∀ d, B d → d ∈ reps := by
  intro n
  induction n with
  | zero =>
    intro pins h
    refine ⟨pins, by omega, ?_⟩
    intro d hd
    have := h (fun _ => d) (fun _ => hd)
    rcases this with ⟨i, j, hij, _⟩ | ⟨_, hp⟩
    · exact absurd (Fin.ext (by
        have hi := i.isLt
        have hj := j.isLt
        omega : (i : Nat) = (j : Nat))) hij
    · exact hp
  | succ n ih =>
    intro pins h
    by_cases hall : ∀ d, B d → d ∈ pins
    · exact ⟨pins, by omega, hall⟩
    · have hex : ∃ d, B d ∧ d ∉ pins :=
        Classical.byContradiction fun hno =>
          hall fun d hd =>
            Classical.byContradiction fun hmem => hno ⟨d, hd, hmem⟩
      obtain ⟨d0, hBd0, hd0⟩ := hex
      -- recurse with d0 as an extra pin and one slot fewer
      have h' : Escapes B (d0 :: pins) (n + 1) := by
        intro f hf
        -- extend f with d0 in the last slot
        have := h (fun i : Fin (n + 2) =>
          if hi : (i : Nat) < n + 1 then f ⟨i, hi⟩ else d0)
          (by
            intro i
            by_cases hi : (i : Nat) < n + 1
            · simpa [hi] using hf ⟨i, hi⟩
            · simpa [hi] using hBd0)
        rcases this with ⟨i, j, hij, hfeq⟩ | ⟨i, hp⟩
        · by_cases hi : (i : Nat) < n + 1
          · by_cases hj : (j : Nat) < n + 1
            · -- a genuine repeat among the first n+1 slots
              refine Or.inl ⟨⟨i, hi⟩, ⟨j, hj⟩, ?_, ?_⟩
              · intro hcon
                have hv : (i : Nat) = (j : Nat) := by
                  simpa [Fin.mk.injEq] using hcon
                exact hij (Fin.ext hv)
              · simpa [hi, hj] using hfeq
            · -- repeat against the appended d0: slot i is pinned to d0
              refine Or.inr ⟨⟨i, hi⟩, ?_⟩
              have : f ⟨i, hi⟩ = d0 := by simpa [hi, hj] using hfeq
              simp [this]
          · by_cases hj : (j : Nat) < n + 1
            · refine Or.inr ⟨⟨j, hj⟩, ?_⟩
              have : d0 = f ⟨j, hj⟩ := by simpa [hi, hj] using hfeq
              simp [this.symm]
            · -- both out of range: i = j = last, contradicting i ≠ j
              exfalso
              apply hij
              have hi' : (i : Nat) = n + 1 := by omega
              have hj' : (j : Nat) = n + 1 := by omega
              exact Fin.ext (hi'.trans hj'.symm)
        · by_cases hi : (i : Nat) < n + 1
          · -- a pin among the original pins
            refine Or.inr ⟨⟨i, hi⟩, ?_⟩
            have : f ⟨i, hi⟩ ∈ pins := by simpa [hi] using hp
            simp [this]
          · -- d0 ∈ pins contradicts the choice of d0
            exfalso
            exact hd0 (by simpa [hi] using hp)
      obtain ⟨reps, hlen, hcov⟩ := ih (d0 :: pins) h'
      exact ⟨reps, by simp at hlen ⊢; omega, hcov⟩

/-- **Soundness of the Nom conclusion** (semantic form).  Suppose
    * `groundEscape` is the disjunction of the kept (non-`y`) head literals
      of the conclusion (`Δ`), as a proposition of the model alone, and
    * the escape hypothesis holds *unless* `groundEscape` does (this is what
      hyper-matching the valid counting clause against the valid premises
      gives: every tuple of constrained predecessors satisfies some head
      literal — a repeat, a pin, or a kept ground literal).

    Then there is an interpretation of `n + pins.length` fresh constants
    (the additional nominals) under which the conclusion
    `B(y) → Δ ∨ ⋁_j y ≈ o'_j` holds for every value of `y`: interpret the
    fresh constants as the covering representatives. -/
theorem nom_sound (B : D → Prop) (pins : List D) (n : Nat)
    (groundEscape : Prop) (dflt : D)
    (h : groundEscape ∨ Escapes B pins (n + 1)) :
    groundEscape ∨ ∃ interp : Fin (n + pins.length) → D,
      ∀ d, B d → ∃ j, d = interp j := by
  rcases h with hg | hesc
  · exact Or.inl hg
  · right
    obtain ⟨reps, hlen, hcov⟩ := nom_cover B n pins hesc
    refine ⟨fun j => reps.getD j dflt, ?_⟩
    intro d hd
    have hmem := hcov d hd
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
    have hk' : k < n + pins.length := Nat.lt_of_lt_of_le hk hlen
    exact ⟨⟨k, hk'⟩, by simp [List.getD, List.getElem?_eq_getElem hk, ← hget]⟩

/-! ## 7. Composing a finite family of Nom firings

The existential interpretation produced by `nom_sound` is local to one rule
firing.  A production run may contain many Nom conclusions, so those choices
must be made simultaneously.  Giving every firing a disjoint block of fresh
constants makes the choices independent and therefore compositional.  Reusing
one block across unrelated firings requires an additional common-cover
invariant; it does not follow from per-firing soundness alone. -/

structure NomObligation (D : Type) where
  B : D → Prop
  pins : List D
  n : Nat
  groundEscape : Prop
  dflt : D
  escape : groundEscape ∨ Escapes B pins (n + 1)

def NomObligation.width (obligation : NomObligation D) : Nat :=
  obligation.n + obligation.pins.length

def NomObligation.SatisfiedWith (obligation : NomObligation D)
    (interp : Fin obligation.width → D) : Prop :=
  obligation.groundEscape ∨
    ∀ d, obligation.B d → ∃ j, d = interp j

theorem NomObligation.exists_interp (obligation : NomObligation D) :
    ∃ interp : Fin obligation.width → D, obligation.SatisfiedWith interp := by
  rcases nom_sound obligation.B obligation.pins obligation.n
      obligation.groundEscape obligation.dflt obligation.escape with
    hground | ⟨interp, hinterp⟩
  · exact ⟨fun _ => obligation.dflt, Or.inl hground⟩
  · exact ⟨interp, Or.inr hinterp⟩

def NomFamilyInterpretation (obligations : List (NomObligation D)) : Type :=
  (index : Fin obligations.length) →
    Fin (obligations.get index).width → D

theorem nom_family_sound (obligations : List (NomObligation D)) :
    ∃ interp : NomFamilyInterpretation obligations,
      ∀ index, (obligations.get index).SatisfiedWith (interp index) := by
  let interp : NomFamilyInterpretation obligations := fun index =>
    Classical.choose (obligations.get index).exists_interp
  refine ⟨interp, ?_⟩
  intro index
  exact Classical.choose_spec (obligations.get index).exists_interp

/-- Reusing one nominal block is sound when all firings in the reuse class are
    restrictions of one predicate with a single checked escape bound.  This is
    the common-cover invariant that a label-based production interner must
    establish; per-firing escape bounds are not enough. -/
theorem nom_shared_cover_sound (B : D → Prop) (pins : List D) (n : Nat)
    (groundEscape : Prop) (dflt : D) (firings : List (D → Prop))
    (hsub : ∀ firing ∈ firings, ∀ d, firing d → B d)
    (hescape : groundEscape ∨ Escapes B pins (n + 1)) :
    groundEscape ∨ ∃ interp : Fin (n + pins.length) → D,
      ∀ firing ∈ firings, ∀ d, firing d → ∃ j, d = interp j := by
  rcases nom_sound B pins n groundEscape dflt hescape with
    hground | ⟨interp, hinterp⟩
  · exact Or.inl hground
  · exact Or.inr ⟨interp, by
      intro firing hfiring d hd
      exact hinterp d (hsub firing hfiring d hd)⟩

theorem independent_nom_witnesses_need_not_share :
    (∃ interp : Fin 1 → Bool,
      ∀ d, d = false → ∃ j, d = interp j) ∧
    (∃ interp : Fin 1 → Bool,
      ∀ d, d = true → ∃ j, d = interp j) ∧
    ¬ ∃ interp : Fin 1 → Bool,
      (∀ d, d = false → ∃ j, d = interp j) ∧
      (∀ d, d = true → ∃ j, d = interp j) := by
  constructor
  · exact ⟨fun _ => false, fun d hd => ⟨⟨0, by decide⟩, hd⟩⟩
  constructor
  · exact ⟨fun _ => true, fun d hd => ⟨⟨0, by decide⟩, hd⟩⟩
  · rintro ⟨interp, hfalse, htrue⟩
    obtain ⟨jfalse, hjfalse⟩ := hfalse false rfl
    obtain ⟨jtrue, hjtrue⟩ := htrue true rfl
    have hindex : jfalse = jtrue := Subsingleton.elim _ _
    rw [hindex] at hjfalse
    exact Bool.noConfusion (hjfalse.trans hjtrue.symm)

/-! ## 8. Completeness of the ground fragment

The ground-context reasoning core — ground context clauses over atoms
`B(o)`, `S(o,o')` (individuals and composites only), resolved by Join cases
1+2 and the grounded Hyper instances — treats ground atoms as opaque
propositional atoms: every inference is propositional resolution.
`CompletenessProp.completeness` therefore applies verbatim with
`Atom := Lit` restricted to ground literals: every unsatisfiable finite set
of ground clauses derives the empty clause, so the engine's ground context
detects every ground-level inconsistency (e.g. an ABox clash among the
asserted individuals).  Stated here as an explicit instantiation for the
record.  The full first-order ALCHOIQ completeness (the paper's
canonical-model construction over a saturated context structure) is NOT
mechanised — matching the repo-wide scope note in `CompletenessProp.lean`;
it is validated empirically against the HermiT oracle and the ORE corpus. -/

/-- Refutational completeness of the ground fragment: an unsatisfiable finite
    set of ground clauses (over any atom type, in particular ground context
    literals) derives `⊥` by resolution — the rule set Join implements. -/
theorem ground_fragment_complete {A : Type} [DecidableEq A]
    (S : Finset (PropRes.PClause A)) (h : PropRes.Unsat S) :
    PropRes.Derivable S PropRes.PClause.bot :=
  PropRes.completeness S h

#print axioms nom_family_sound
#print axioms nom_shared_cover_sound
#print axioms independent_nom_witnesses_need_not_share

end ContextCalculus.Nominals
