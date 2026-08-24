/-
  ContextCalculus/Equivalence.lean
  ================================
  **Optimized saturation ≡ ground resolution.**

  The engine does not run naive ground resolution; it saturates a *context
  structure* under an ordering, with blocking.  This file proves those
  optimizations agree with ground resolution on the only thing that matters —
  derivation of the empty clause — and hence decide ground (un)satisfiability.

  We model the engine's output abstractly but faithfully as a `Saturation`: the
  finite set `N` of clauses it has produced is

    * a superset of the input `S`              (`incl`),
    * closed under the resolution it performs  (`closed`), and
    * sound — every produced clause is resolution-derivable from `S` (`sound`,
      because every context rule is a resolution / paramodulation step, the
      content mechanized in `Basic.lean`).

  The contexts, the literal ordering, and blocking determine *how* `N` is built
  and that the build terminates (`Termination.lean`); they do not appear in this
  spec, which is the point: any sound, resolution-closed saturation behaves like
  ground resolution.

  Results (`sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`):

    * `derivable_bot_iff_unsat`        — ground resolution decides satisfiability:
                                         `Derivable S ⊥ ↔ Unsat S`;
    * `saturation_refutes_iff_derivable` — `⊥ ∈ N ↔ Derivable S ⊥`, i.e. the
                                         optimized saturation refutes exactly when
                                         ground resolution does;
    * `saturation_refutes_iff_unsat`   — and exactly when `S` is unsatisfiable;
    * `engine_agrees_ground`           — on the concrete grounding: the engine's
                                         saturation refutes iff ground resolution
                                         does, and when it does not, the
                                         congruence quotient is a genuine model
                                         of the ontology.
-/
import ContextCalculus.CompletenessProp
import ContextCalculus.CompletenessEq

namespace ContextCalculus.Equiv

open ContextCalculus.PropRes ContextCalculus.Eqv

variable {Atom : Type} [DecidableEq Atom]

/-- **Ground resolution decides satisfiability.**  `⊥` is derivable iff the
    clause set is unsatisfiable (soundness via `derivable_sound`, completeness via
    `PropRes.completeness`). -/
theorem derivable_bot_iff_unsat (S : Finset (PClause Atom)) :
    Derivable S PClause.bot ↔ Unsat S := by
  constructor
  · intro h
    rintro ⟨I, hI⟩
    exact PClause.not_sat_bot I (derivable_sound I S hI h)
  · exact PropRes.completeness S

/-- A sound, resolution-closed saturation of `S` — the faithful spec of what the
    optimized engine produces. -/
structure Saturation (S N : Finset (PClause Atom)) : Prop where
  incl : S ⊆ N
  closed : ∀ c1 c2 a, c1 ∈ N → c2 ∈ N → a ∈ c1.pos → a ∈ c2.neg → resolvent c1 c2 a ∈ N
  sound : ∀ c ∈ N, Derivable S c

/-- A valuation is a model of every clause in a finite clause set. -/
def Models (S : Finset (PClause Atom)) (I : Atom → Prop) : Prop :=
  ∀ c ∈ S, c.sat I

/-- A sound saturation that retains its input preserves the complete model
    class, not only refutability.  Inclusion gives the right-to-left direction;
    derivability soundness gives the left-to-right direction for every produced
    clause.  Closure is not needed for preservation itself, but is what later
    turns the retained, sound set into a complete saturation. -/
theorem saturation_models_iff {S N : Finset (PClause Atom)}
    (hsat : Saturation S N) (I : Atom → Prop) :
    Models N I ↔ Models S I := by
  constructor
  · intro hN c hc
    exact hN c (hsat.incl hc)
  · intro hS c hc
    exact derivable_sound I S hS (hsat.sound c hc)

/-- Consequently a checked saturation preserves every semantic consequence,
    including each positive and negative cell of a published taxonomy. -/
theorem saturation_entails_iff {S N : Finset (PClause Atom)}
    (hsat : Saturation S N) (target : PClause Atom) :
    (∀ I, Models S I → target.sat I) ↔
      (∀ I, Models N I → target.sat I) := by
  constructor
  · intro h I hN
    exact h I ((saturation_models_iff hsat I).mp hN)
  · intro h I hS
    exact h I ((saturation_models_iff hsat I).mpr hS)

#print axioms saturation_models_iff
#print axioms saturation_entails_iff

/-- Everything resolution-derivable from `S` is already in a saturation of `S`. -/
theorem mem_of_derivable {S N : Finset (PClause Atom)} (hsat : Saturation S N)
    {c : PClause Atom} (h : Derivable S c) : c ∈ N := by
  induction h with
  | premise hc => exact hsat.incl hc
  | resolve _ _ ha1 ha2 ih1 ih2 => exact hsat.closed _ _ _ ih1 ih2 ha1 ha2

/-- **Optimized saturation ≡ ground resolution (on ⊥).**  The saturation contains
    the empty clause iff plain resolution derives it. -/
theorem saturation_refutes_iff_derivable {S N : Finset (PClause Atom)}
    (hsat : Saturation S N) : PClause.bot ∈ N ↔ Derivable S PClause.bot := by
  constructor
  · intro h; exact hsat.sound _ h
  · intro h; exact mem_of_derivable hsat h

/-- And both agree with unsatisfiability of `S`. -/
theorem saturation_refutes_iff_unsat {S N : Finset (PClause Atom)}
    (hsat : Saturation S N) : PClause.bot ∈ N ↔ Unsat S :=
  (saturation_refutes_iff_derivable hsat).trans (derivable_bot_iff_unsat S)

section Ground

variable {CN RN T : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq T]
  [Fintype T] [Fintype CN] [Fintype RN]
variable (wit : CN → RN → CN → T → T) (O : Ontology CN RN T)
variable (minWit : (a : CN) → (n : Nat) → RN → CN → T → Fin n → T)

/-- Ground resolution decides the grounding of the ontology. -/
theorem ground_resolution_decides :
    Derivable (ground wit minWit O) PClause.bot ↔ Unsat (ground wit minWit O) :=
  derivable_bot_iff_unsat _

/-- **The engine agrees with ground resolution on the grounding.**  Its
    saturation refutes iff ground resolution refutes the grounding; and when it
    does *not* refute, the congruence quotient is a genuine first-order model of
    the ontology (so the non-refutation is justified, not a missed proof). -/
theorem engine_agrees_ground {N : Finset (PClause (GAtom CN RN T))}
    (hsat : Saturation (ground wit minWit O) N) :
    (PClause.bot ∈ N ↔ Derivable (ground wit minWit O) PClause.bot) ∧
    (PClause.bot ∉ N → ∃ (D : Type) (I : Interp D CN RN T), models I O) := by
  refine ⟨saturation_refutes_iff_derivable hsat, ?_⟩
  intro hnb
  have hnd : ¬ Derivable (ground wit minWit O) PClause.bot :=
    fun h => hnb ((saturation_refutes_iff_derivable hsat).mpr h)
  exact herbrand_complete (grounds_ground wit minWit O) hnd

end Ground

end ContextCalculus.Equiv
