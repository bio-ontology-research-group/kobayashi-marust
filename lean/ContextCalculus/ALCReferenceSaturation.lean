import ContextCalculus.CompletenessStrategy
import ContextCalculus.CBALCEncoding

/-!
# Computable reference saturation for the ALC type-elimination procedure

This module is the computable twin of `CompletenessStrategy` for finite concept
and role signatures (`Fin conceptCount`, `Fin roleCount`), used as the phase 2
ALC reference procedure of the v1.6.0 completeness proof
(`docs/V1.6.0-COMPLETENESS-PLAN.md`).

`CompletenessContext` and `CompletenessStrategy` open `Classical`, which makes
`step`, `cand`, `sat`, and `saturate` noncomputable through `Finset.filter`.
Here we give explicit `Decidable` instances for `consistent`, `compat`, and
`realizedIn` by bounding their quantifiers over the ontology clause list `O`
and the candidate type set `G`, define `stepC`, `candC`, `satC`, and
`saturateC` without `Classical`, and prove `saturateC O = saturate O` by
subsingleton elimination on the `Decidable` instances.  The readout `alcBit`
then inherits exactness directly from `saturate_decides`.
-/

deriving instance DecidableEq, Repr for ContextCalculus.Ctx.Clause

namespace ContextCalculus.ALCReference

open ContextCalculus.Ctx

variable {CName Role : Type}

/-- Clause-local consistency condition for a candidate type `t`. -/
def consistentClause (t : Finset CName) : Ctx.Clause CName Role → Prop
  | .gci body head => (∀ a ∈ body, a ∈ t) → ∃ b ∈ head, b ∈ t
  | _ => True

instance instDecidableConsistentClause [DecidableEq CName]
    (t : Finset CName) (cl : Ctx.Clause CName Role) :
    Decidable (consistentClause t cl) := by
  cases cl <;> unfold consistentClause <;> infer_instance

theorem consistent_iff_forall_clause (O : Ontology CName Role)
    (t : Finset CName) :
    consistent O t ↔ ∀ cl ∈ O, consistentClause t cl := by
  constructor
  · intro h cl hcl
    cases cl with
    | gci body head => exact h body head hcl
    | _ => trivial
  · intro h body head hcl
    exact h (.gci body head) hcl

/-- Computable decidability of `consistent O t` by scanning the clause list. -/
instance instDecidableConsistent [DecidableEq CName]
    (O : Ontology CName Role) (t : Finset CName) :
    Decidable (consistent O t) :=
  decidable_of_iff (∀ cl ∈ O, consistentClause t cl)
    (consistent_iff_forall_clause O t).symm

/-- Clause-local compatibility condition across a role edge `rr`. -/
def compatClause (rr : Role) (t s : Finset CName) : Ctx.Clause CName Role → Prop
  | .allRight a rr' b => rr' = rr → a ∈ t → b ∈ s
  | .exLeft rr' d cc => rr' = rr → d ∈ s → cc ∈ t
  | _ => True

instance instDecidableCompatClause [DecidableEq CName] [DecidableEq Role]
    (rr : Role) (t s : Finset CName) (cl : Ctx.Clause CName Role) :
    Decidable (compatClause rr t s cl) := by
  cases cl <;> unfold compatClause <;> infer_instance

theorem compat_iff_forall_clause (O : Ontology CName Role) (rr : Role)
    (t s : Finset CName) :
    compat O rr t s ↔ ∀ cl ∈ O, compatClause rr t s cl := by
  constructor
  · rintro ⟨hall, hex⟩ cl hcl
    cases cl with
    | allRight a rr' b =>
        rintro rfl ha
        exact hall a b hcl ha
    | exLeft rr' d cc =>
        rintro rfl hd
        exact hex d cc hcl hd
    | _ => trivial
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hcl ha
      exact h (.allRight a rr b) hcl rfl ha
    · intro d cc hcl hd
      exact h (.exLeft rr d cc) hcl rfl hd

/-- Computable decidability of `compat O rr t s` by scanning the clause list. -/
instance instDecidableCompat [DecidableEq CName] [DecidableEq Role]
    (O : Ontology CName Role) (rr : Role) (t s : Finset CName) :
    Decidable (compat O rr t s) :=
  decidable_of_iff (∀ cl ∈ O, compatClause rr t s cl)
    (compat_iff_forall_clause O rr t s).symm

/-- Clause-local existential realisation condition inside `G`. -/
def realizedClause (O : Ontology CName Role) (G : Finset (Finset CName))
    (t : Finset CName) : Ctx.Clause CName Role → Prop
  | .exRight a rr b => a ∈ t → ∃ s ∈ G, b ∈ s ∧ compat O rr t s
  | _ => True

instance instDecidableRealizedClause [DecidableEq CName] [DecidableEq Role]
    (O : Ontology CName Role) (G : Finset (Finset CName))
    (t : Finset CName) (cl : Ctx.Clause CName Role) :
    Decidable (realizedClause O G t cl) := by
  cases cl <;> unfold realizedClause <;> infer_instance

theorem realizedIn_iff_forall_clause (O : Ontology CName Role)
    (G : Finset (Finset CName)) (t : Finset CName) :
    realizedIn O G t ↔ ∀ cl ∈ O, realizedClause O G t cl := by
  constructor
  · intro h cl hcl
    cases cl with
    | exRight a rr b => exact h a rr b hcl
    | _ => trivial
  · intro h a rr b hcl
    exact h (.exRight a rr b) hcl

/-- Computable decidability of `realizedIn O G t` by scanning the clause list
and the finite type set `G`. -/
instance instDecidableRealizedIn [DecidableEq CName] [DecidableEq Role]
    (O : Ontology CName Role) (G : Finset (Finset CName)) (t : Finset CName) :
    Decidable (realizedIn O G t) :=
  decidable_of_iff (∀ cl ∈ O, realizedClause O G t cl)
    (realizedIn_iff_forall_clause O G t).symm

variable {conceptCount roleCount : Nat}

/-- Computable one-round type-elimination operator. -/
def stepC (O : Ontology (Fin conceptCount) (Fin roleCount))
    (G : Finset (Finset (Fin conceptCount))) :
    Finset (Finset (Fin conceptCount)) :=
  G.filter (realizedIn O G)

/-- Computable initial candidate set of propositionally consistent types. -/
def candC (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    Finset (Finset (Fin conceptCount)) :=
  (Finset.univ : Finset (Fin conceptCount)).powerset.filter (consistent O)

/-- Computable `n`-step iteration of `stepC` from `candC`. -/
def satC (O : Ontology (Fin conceptCount) (Fin roleCount)) (n : Nat) :
    Finset (Finset (Fin conceptCount)) :=
  (stepC O)^[n] (candC O)

/-- Iterate `stepC` with early exit as soon as a round removes no types. -/
def saturateLoop (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    Nat → Finset (Finset (Fin conceptCount)) →
      Finset (Finset (Fin conceptCount))
  | 0, G => G
  | fuel + 1, G =>
      let next := stepC O G
      if next.card = G.card then G else saturateLoop O fuel next

/-- Computable converged set of good types. -/
def saturateC (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    Finset (Finset (Fin conceptCount)) :=
  let init := candC O
  saturateLoop O init.card init

theorem stepC_eq (O : Ontology (Fin conceptCount) (Fin roleCount))
    (G : Finset (Finset (Fin conceptCount))) :
    stepC O G = Ctx.step O G := by
  unfold stepC Ctx.step
  congr

theorem candC_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    candC O = Ctx.cand O := by
  unfold candC Ctx.cand
  congr

theorem satC_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) (n : Nat) :
    satC O n = Ctx.sat O n := by
  unfold satC Ctx.sat
  rw [funext (stepC_eq O), candC_eq]

theorem saturateLoop_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    ∀ (n : Nat) (G : Finset (Finset (Fin conceptCount))),
      saturateLoop O n G = (Ctx.step O)^[n] G
  | 0, G => rfl
  | n + 1, G => by
      dsimp only [saturateLoop]
      split
      · next hcard =>
          have hsub : stepC O G ⊆ G := Finset.filter_subset _ _
          have hfix : stepC O G = G :=
            Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcard.symm)
          have hfix' : Ctx.step O G = G := by
            rw [← stepC_eq, hfix]
          exact (Function.iterate_fixed hfix' (n + 1)).symm
      · next _ =>
          rw [saturateLoop_eq O n (stepC O G), stepC_eq, Function.iterate_succ_apply]

/-- The computable saturation produces the exact same finset of good types as
the classical specification. -/
theorem saturateC_eq (O : Ontology (Fin conceptCount) (Fin roleCount)) :
    saturateC O = Ctx.saturate O := by
  unfold saturateC Ctx.saturate Ctx.sat
  rw [saturateLoop_eq, candC_eq]

/-- Executable ALC subsumption decision bit on a precomputed good-type set `G`:
`A ⊑ B` holds iff every type in `G` containing `A` also contains `B`. -/
def alcBitOf (G : Finset (Finset (Fin conceptCount)))
    (A B : Fin conceptCount) : Bool :=
  @decide (∀ t ∈ G, A ∈ t → B ∈ t) Finset.decidableDforallFinset

/-- Executable ALC subsumption decision bit: `A ⊑ B` holds iff every type in
`saturateC O` containing `A` also contains `B`. -/
def alcBit (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) : Bool :=
  alcBitOf (saturateC O) A B

theorem alcBit_eq (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = alcBitOf (saturateC O) A B := rfl

/-- `alcBit` decides atomic subsumption over all interpretations of `O`. -/
theorem alcBit_exact (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔
      (∀ (D : Type) (I : Interp D (Fin conceptCount) (Fin roleCount)),
        models I O → ∀ x, I.c A x → I.c B x) := by
  simp only [alcBit, alcBitOf, decide_eq_true_eq, saturateC_eq, saturate_decides]

/-- `alcBit` agrees with `CBALCEncoding.EntailsSub`. -/
theorem alcBit_iff_entailsSub (O : Ontology (Fin conceptCount) (Fin roleCount))
    (A B : Fin conceptCount) :
    alcBit O A B = true ↔ CBALCEncoding.EntailsSub O A B := by
  rw [alcBit_exact, ← CBALCEncoding.entailsSub_iff_ctx]

#print axioms saturateC_eq
#print axioms alcBit_exact
#print axioms alcBit_iff_entailsSub

end ContextCalculus.ALCReference

namespace ContextCalculus.ALCReferenceSaturation
export ContextCalculus.ALCReference
  (consistentClause compatClause realizedClause
   instDecidableConsistent instDecidableCompat instDecidableRealizedIn
   stepC candC satC saturateLoop saturateC
   stepC_eq candC_eq satC_eq saturateLoop_eq saturateC_eq
   alcBitOf alcBit alcBit_eq alcBit_exact alcBit_iff_entailsSub)
end ContextCalculus.ALCReferenceSaturation
