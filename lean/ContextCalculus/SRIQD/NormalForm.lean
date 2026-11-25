import ContextCalculus.SRIQ.NormalForm
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Data properties and datatypes: the normal form `SRIQD` (stage C4, step 1)

`docs/V1.7.0-C4-DATATYPES-DESIGN.md`, sections 2 and 3. The clauses of
`SRIQ` (wrapped by `Clause.obj`) plus five data clauses over data
property names `DProp` and data atoms `DAtom`:

* `dEx a u pos neg`: `a ⊑ ∃u.(⋀pos ⊓ ⋀¬neg)`;
* `dAll a u head`: `a ⊑ ∀u.(⋁ head)`, a literal `(p, true)` is `p` and
  `(p, false)` is `¬p`;
* `dAtLeast a n u pos neg` and `dAtMost a n u pos neg`: qualified number
  restrictions on a data range in the clausal form of `dEx`;
* `dSub u v`: `u ⊑ v`.

A functional data property is `⊤ ⊑ ≤1 u.⊤`, written with a top name `T`
(`⊤ ⊑ T`) as `dAtMost T 1 u [] []`.

An interpretation (`DInterp`) adds to an `SRI.Interp` a relation
`d : DProp → D → V → Prop` into a value type `V`. The atoms are read by
`atom : DAtom → V → Prop`, which comes with `V` from a *data theory*
`Θ : DataTheory DAtom`, a class of admissible pairs `(V, atom)`.
Entailment quantifies over the admissible pairs.

## The oracle

The *value type* `vt atom v` of a value is the set of atoms it satisfies.
A function `card : Finset DAtom → Option Nat` (`none`: unbounded) is an
oracle for `Θ` (`OracleSpec`) when

* (upper) in every admissible pair, for every `τ` with `card τ = some k`,
  at most `k` values have value type exactly `τ`;
* (lower) for every demand `need` with `need τ ≤ k` whenever
  `card τ = some k`, one admissible pair has, for every `τ` at once,
  `need τ` distinct values of value type `τ`.

The design (section 3) asked for an exact count in every admissible
pair; that fails for free datatypes outside the datatype map. The two
directions above are what the characterisation (`SRIQD/Stars.lean`)
uses: (upper) bounds the data neighbours read off a model, (lower)
supplies values for the stars of a countermodel. Both are needed
(`SRIQD/OracleExamples.lean` proves the two failures below): with
a theory whose admissible pairs have three booleans but `card` says two,
`A ⊑ ≥3 u.boolean` has a model while the stars say `A` is unsatisfiable;
with a theory where one pair has two values of `τ₁` and none of `τ₂` and
another the reverse, `card` with `2` for both satisfies a lower bound
taken one type at a time, but `A ⊑ ∃u.τ₁ ⊓ ∃u.τ₂` (in the clausal form)
has no model while the stars accept it.

## Embedding

`entailsSub_ofSRIQ`: an `SRIQ` ontology has the same subsumptions as its
embedding, for every data theory with at least one admissible pair
(`OracleSpec.nonempty` gives one). The hypothesis is needed: with no
admissible pair every subsumption holds vacuously
(`entailsSub_of_empty`).
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)

/-- `SRIQ` clauses plus data clauses. -/
inductive Clause (CName Role DProp DAtom : Type) where
  /-- An `SRIQ` clause. -/
  | obj (cl : SRIQ.Clause CName Role)
  /-- `a ⊑ ∃u.(⋀pos ⊓ ⋀¬neg)`. -/
  | dEx (a : CName) (u : DProp) (pos neg : List DAtom)
  /-- `a ⊑ ∀u.(⋁ head)`; `(p, b)` is `p` for `b = true` and `¬p` otherwise. -/
  | dAll (a : CName) (u : DProp) (head : List (DAtom × Bool))
  /-- `a ⊑ ≥n u.(⋀pos ⊓ ⋀¬neg)`. -/
  | dAtLeast (a : CName) (n : Nat) (u : DProp) (pos neg : List DAtom)
  /-- `a ⊑ ≤n u.(⋀pos ⊓ ⋀¬neg)`. -/
  | dAtMost (a : CName) (n : Nat) (u : DProp) (pos neg : List DAtom)
  /-- `u ⊑ v`. -/
  | dSub (u v : DProp)
deriving DecidableEq, Repr

abbrev Ontology (CName Role DProp DAtom : Type) := List (Clause CName Role DProp DAtom)

/-- An interpretation: an `SRI` interpretation and data properties into
the values `V`. -/
structure DInterp (D V CName Role DProp : Type) extends Interp D CName Role where
  d : DProp → D → V → Prop

/-- A data theory: the admissible value types with their atom readings. -/
abbrev DataTheory (DAtom : Type) := (V : Type) → (DAtom → V → Prop) → Prop

variable {D V CName Role DProp DAtom : Type}

/-- `v` lies in `⋀pos ⊓ ⋀¬neg`. -/
def rngSem (atom : DAtom → V → Prop) (pos neg : List DAtom) (v : V) : Prop :=
  (∀ p ∈ pos, atom p v) ∧ ∀ q ∈ neg, ¬ atom q v

/-- The literal `l` holds at `v`. -/
def litSem (atom : DAtom → V → Prop) (l : DAtom × Bool) (v : V) : Prop :=
  atom l.1 v ↔ l.2 = true

/-- A data clause at one element, given the names `c` that hold there and
its data relation `d`. Object clauses hold trivially here. -/
def dLocal (atom : DAtom → V → Prop) (c : CName → Prop) (d : DProp → V → Prop) :
    Clause CName Role DProp DAtom → Prop
  | .obj _ => True
  | .dEx a u pos neg => c a → ∃ v, d u v ∧ rngSem atom pos neg v
  | .dAll a u head => c a → ∀ v, d u v → ∃ l ∈ head, litSem atom l v
  | .dAtLeast a n u pos neg => c a →
      ∃ l : List V, l.Nodup ∧ l.length = n ∧ ∀ v ∈ l, d u v ∧ rngSem atom pos neg v
  | .dAtMost a n u pos neg => c a →
      ∀ l : List V, l.Nodup → (∀ v ∈ l, d u v ∧ rngSem atom pos neg v) → l.length ≤ n
  | .dSub u w => ∀ v, d u v → d w v

/-- Satisfaction of a clause. -/
def satClause (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp) :
    Clause CName Role DProp DAtom → Prop
  | .obj cl => SRIQ.satClause I.toInterp cl
  | cl => ∀ x, dLocal atom (fun a => I.c a x) (fun u => I.d u x) cl

/-- `I` models the ontology. -/
def models (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp)
    (O : Ontology CName Role DProp DAtom) : Prop :=
  ∀ cl ∈ O, satClause atom I cl

/-- Subsumption between concept names over the admissible data
interpretations of `Θ`, over nonempty domains. -/
def EntailsSub (Θ : DataTheory DAtom) (O : Ontology CName Role DProp DAtom) (a b : CName) :
    Prop :=
  ∀ (D V : Type) [Nonempty D] (atom : DAtom → V → Prop), Θ V atom →
    ∀ I : DInterp D V CName Role DProp, models atom I O → ∀ x, I.c a x → I.c b x

/-- The concept name `a` is empty in every model. -/
def Unsat (Θ : DataTheory DAtom) (O : Ontology CName Role DProp DAtom) (a : CName) : Prop :=
  ∀ (D V : Type) [Nonempty D] (atom : DAtom → V → Prop), Θ V atom →
    ∀ I : DInterp D V CName Role DProp, models atom I O → ∀ x, ¬ I.c a x

/-! ## Value types and the oracle -/

/-- The value type of `v`: the atoms it satisfies. -/
noncomputable def vt [Fintype DAtom] (atom : DAtom → V → Prop) (v : V) : Finset DAtom :=
  by classical exact Finset.univ.filter fun p => atom p v

theorem mem_vt [Fintype DAtom] {atom : DAtom → V → Prop} {v : V} {p : DAtom} :
    p ∈ vt atom v ↔ atom p v := by
  classical
  simp [vt]

/-- The oracle specification (see the module docstring). -/
structure OracleSpec [Fintype DAtom] (Θ : DataTheory DAtom) (card : Finset DAtom → Option Nat) :
    Prop where
  upper : ∀ (V : Type) (atom : DAtom → V → Prop), Θ V atom → ∀ τ k, card τ = some k →
    ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k
  lower : ∀ need : Finset DAtom → Nat, (∀ τ k, card τ = some k → need τ ≤ k) →
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
      ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ

/-- An oracle's theory has an admissible pair (the empty demand). -/
theorem OracleSpec.nonempty [Fintype DAtom] {Θ : DataTheory DAtom}
    {card : Finset DAtom → Option Nat} (h : OracleSpec Θ card) :
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom := by
  obtain ⟨V, atom, hΘ, -⟩ := h.lower (fun _ => 0) (fun _ _ _ => Nat.zero_le _)
  exact ⟨V, atom, hΘ⟩

/-! ## The object part -/

/-- The `SRIQ` clause of a clause, if it is one. -/
def toObj : Clause CName Role DProp DAtom → Option (SRIQ.Clause CName Role)
  | .obj cl => some cl
  | _ => none

/-- The `SRIQ` clauses of an ontology. -/
def objPart (O : Ontology CName Role DProp DAtom) : SRIQ.Ontology CName Role :=
  O.filterMap toObj

theorem mem_objPart {O : Ontology CName Role DProp DAtom} {cl : SRIQ.Clause CName Role} :
    cl ∈ objPart O ↔ Clause.obj cl ∈ O := by
  simp only [objPart, List.mem_filterMap]
  constructor
  · rintro ⟨cl', h, he⟩
    cases cl' <;> simp only [toObj, Option.some.injEq, reduceCtorEq] at he
    subst he
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

/-- The object part has role chains of length one only. -/
def IsALCHIQ (O : Ontology CName Role DProp DAtom) : Prop :=
  SRIQ.IsALCHIQ (objPart O)

/-- A model is a model of the object part whose elements satisfy the
data clauses locally. -/
theorem models_iff {atom : DAtom → V → Prop} {I : DInterp D V CName Role DProp}
    {O : Ontology CName Role DProp DAtom} :
    models atom I O ↔ SRIQ.models I.toInterp (objPart O) ∧
      ∀ cl ∈ O, ∀ x, dLocal atom (fun a => I.c a x) (fun u => I.d u x) cl := by
  constructor
  · intro h
    refine ⟨fun cl hcl => h _ (mem_objPart.1 hcl), fun cl hcl x => ?_⟩
    have := h cl hcl
    cases cl <;> first | trivial | exact this x
  · rintro ⟨h1, h2⟩ cl hcl
    cases cl with
    | obj cl => exact h1 cl (mem_objPart.2 hcl)
    | _ => exact fun x => h2 _ hcl x

/-! ## The embedding of `SRIQ` -/

/-- An `SRIQ` clause as an `SRIQD` clause. -/
abbrev ofSRIQ : SRIQ.Clause CName Role → Clause CName Role DProp DAtom := Clause.obj

theorem objPart_ofSRIQ (O : SRIQ.Ontology CName Role) :
    objPart (O.map (ofSRIQ (DProp := DProp) (DAtom := DAtom))) = O := by
  simp [objPart, List.filterMap_map, toObj]

theorem models_ofSRIQ (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp)
    (O : SRIQ.Ontology CName Role) :
    models atom I (O.map (ofSRIQ (DProp := DProp) (DAtom := DAtom))) ↔
      SRIQ.models I.toInterp O := by
  simp only [models, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satClause, SRIQ.models]

/-- **Embedding.** For a data theory with an admissible pair, an `SRIQ`
ontology and its embedding have the same subsumptions. -/
theorem entailsSub_ofSRIQ {Θ : DataTheory DAtom} (hΘ : ∃ (V : Type) (atom : DAtom → V → Prop),
    Θ V atom) (O : SRIQ.Ontology CName Role) (a b : CName) :
    EntailsSub Θ (O.map (ofSRIQ (DProp := DProp))) a b ↔ SRIQ.EntailsSub O a b := by
  constructor
  · intro h D _ I hI x hx
    obtain ⟨V, atom, hV⟩ := hΘ
    exact h D V atom hV { toInterp := I, d := fun _ _ _ => False }
      ((models_ofSRIQ atom _ O).2 hI) x hx
  · intro h D V _ atom _ I hI x hx
    exact h D I.toInterp ((models_ofSRIQ atom I O).1 hI) x hx

/-- Without an admissible pair every subsumption holds. -/
theorem entailsSub_of_empty (O : Ontology CName Role DProp DAtom) (a b : CName) :
    EntailsSub (fun _ _ => False) O a b :=
  fun _ _ _ _ h => h.elim

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.models_iff
#print axioms ContextCalculus.SRIQD.entailsSub_ofSRIQ
#print axioms ContextCalculus.SRIQD.OracleSpec.nonempty
