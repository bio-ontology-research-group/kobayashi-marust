/-
  ContextCalculus/CompletenessInverse.lean
  ========================================
  **Inverse roles: faithfulness of the bridge encoding (Lean certificate).**

  The Rust frontend (`engine/src/frontend/normalise.rs`, `link_inverse`) does NOT
  add inverse roles to the calculus as a primitive.  It translates an inverse
  role `R⁻` to a *fresh* ordinary role symbol `S` together with two ordinary
  DL-clauses — the **bridges**

      R(x,y) → S(y,x)        and        S(x,y) → R(y,x).

  `CompletenessContext.lean` proves completeness for the ALC clause fragment but
  explicitly leaves inverse roles as a documented residual.  This file closes
  that residual at the level it actually lives: it certifies that the bridge
  encoding is **conservative** — it neither loses nor adds any consequence over
  named concepts.  Concretely:

    * `bridges_iff_converse` — in *any* interpretation the two bridges hold iff
      `S` is interpreted as the converse of `R`.  So the bridges are not an
      approximation: they *exactly axiomatise* the inverse relationship.
    * `models_inv_iff_enc` — an interpretation is a model of the ontology read
      with `S = R⁻` iff it is a model of the encoded ontology (ALC part + the two
      bridges).  The two model classes are equal.
    * `inverse_conservative` — therefore `O ⊨ A ⊑ B` under the inverse reading
      iff `enc(O) ⊨ A ⊑ B`.  No subsumption over named concepts is gained or
      lost by the translation.

  Everything here is `sorry`-free.

  Scope.  This certifies the *encoding* the frontend performs (soundness AND
  completeness of the `R⁻ ↦ fresh role + bridges` translation).  The bridges are
  role-to-role clauses outside the `Clause` fragment of `CompletenessContext`, so
  this does not by itself extend the finite-type canonical-model construction to
  ALCI; that the engine's ordered clause saturation derives every consequence of
  the encoded set is the same disjunctive-saturation completeness that is
  empirical for the whole engine (and was confirmed for the inverse-role
  benchmark 9724 as a monotone budget-bound, not a calculus gap).  What is new
  here, and was previously *not claimed*, is that the translation itself is
  faithful: reasoning on the encoded ontology is reasoning on the original.
-/
import ContextCalculus.CompletenessContext

namespace ContextCalculus.Inverse

open ContextCalculus.Ctx

variable {CName Role : Type}

/-- The two inverse **bridges** for the pair `(R, S)` hold in `I`:
    `R(x,y) → S(y,x)` and `S(x,y) → R(y,x)`. -/
def bridges {D : Type} (I : Interp D CName Role) (R S : Role) : Prop :=
  (∀ x y, I.r R x y → I.r S y x) ∧ (∀ x y, I.r S x y → I.r R y x)

/-- `S` is interpreted as the converse of `R`: `S(x,y) ↔ R(y,x)`.  This is the
    Tarskian semantics of the inverse role `R⁻`. -/
def isConverse {D : Type} (I : Interp D CName Role) (R S : Role) : Prop :=
  ∀ x y, I.r S x y ↔ I.r R y x

/-- **The bridges exactly axiomatise the converse.**  In any interpretation, the
    two bridge clauses hold iff `S` is the converse of `R`.  The forward
    direction is the crux: each bridge gives one inclusion, and together they
    pin `S` to be *exactly* `R⁻` (not merely a super- or sub-relation). -/
theorem bridges_iff_converse {D : Type} (I : Interp D CName Role) (R S : Role) :
    bridges I R S ↔ isConverse I R S := by
  constructor
  · rintro ⟨h1, h2⟩ x y
    constructor
    · intro hSxy; exact h2 x y hSxy
    · intro hRyx; exact h1 y x hRyx
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hRxy; exact (h y x).2 hRxy
    · intro x y hSxy; exact (h x y).1 hSxy

/-- **Model classes coincide.**  An interpretation models the ALC ontology `O`
    with `S` read as the converse of `R` iff it models `O` together with the two
    bridge clauses.  (`models I O` is the ALC part; the inverse axiom is the only
    difference between the two readings, and `bridges_iff_converse` shows the two
    formulations of that axiom are equivalent.) -/
theorem models_inv_iff_enc {D : Type} (I : Interp D CName Role)
    (O : Ontology CName Role) (R S : Role) :
    (models I O ∧ isConverse I R S) ↔ (models I O ∧ bridges I R S) := by
  rw [bridges_iff_converse]

/-- **Conservativity of the inverse-role bridge encoding.**  A concept
    subsumption `A ⊑ B` holds in every model of the ontology under the inverse
    reading (`S = R⁻`) iff it holds in every model of the encoded ontology (ALC
    clauses + the two bridges).  Hence the frontend's translation loses no
    entailment (soundness of the encoding) and invents none (completeness of the
    encoding): reasoning on the encoded ontology *is* reasoning on the original
    ALCI ontology. -/
theorem inverse_conservative (O : Ontology CName Role) (R S : Role) (A B : CName) :
    (∀ (D : Type) (I : Interp D CName Role),
        models I O → isConverse I R S → ∀ x, I.c A x → I.c B x)
      ↔ (∀ (D : Type) (I : Interp D CName Role),
        models I O → bridges I R S → ∀ x, I.c A x → I.c B x) := by
  constructor
  · intro h D I hM hB x hA
    exact h D I hM ((bridges_iff_converse I R S).1 hB) x hA
  · intro h D I hM hC x hA
    exact h D I hM ((bridges_iff_converse I R S).2 hC) x hA

/-- **Symmetry of the bridge pair.**  The two bridges for `(R, S)` are also the
    two bridges for `(S, R)` — the encoding is direction-agnostic, matching the
    frontend emitting both `R(x,y)→S(y,x)` and `S(x,y)→R(y,x)`.  So declaring
    `R⁻ = S` and declaring `S⁻ = R` produce the same model class. -/
theorem bridges_symm {D : Type} (I : Interp D CName Role) (R S : Role) :
    bridges I R S ↔ bridges I S R := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- **Involution.**  Under the bridges, the converse of the converse is the
    original: `isConverse I R S` already gives `R(x,y) ↔ S(y,x)`, i.e. `R` is the
    converse of `S`.  (The inverse of an inverse role is the role itself.) -/
theorem isConverse_symm {D : Type} (I : Interp D CName Role) (R S : Role) :
    isConverse I R S ↔ isConverse I S R := by
  constructor
  · intro h x y; exact (h y x).symm
  · intro h x y; exact (h y x).symm

end ContextCalculus.Inverse
