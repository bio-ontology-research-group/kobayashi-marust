import ContextCalculus.IncrementalDataModuleReuse
import ContextCalculus.IncrementalUnionConsistency

/-!
# Full locality with fixed datatype semantics

This extends the same fixed value domain, datatype ranges and literal values
used by `IncrementalDataModuleReuse`; these maps are never masked or changed
between models. Only class/object-role predicates and data-property edges are
masked. Individuals remain unchanged. Consequently an assertion's individual
and literal IDs do not belong to the masked semantic signature. This does not
permit dropping their source occurrence or typed public-domain provenance.

The executable source boundary remains the exact allowed object/data family:
no data class constructors, datatype definitions, keys, rules, universal object
properties, either built-in data property (topDataProperty or
bottomDataProperty), or unknown forms. Data-property IDs in this model denote
ordinary relations; no fixed universal/empty data-role semantics is assumed.
The full-index compiler must establish
signature coverage and the closed module condition. A successful OLD model and
a UNION module extracted from an empty seed and contained in OLD establish
UNION and NEW consistency. Its closed signature S0 may be nonempty, and that
core need not be contained in NEW. For query publication every data
TBox axiom and nominal axiom must be excluded from the affected object module.
An affected module containing nominals requires complete NEW classification.

The closed signature S0 is the logical fixpoint before the executable module
API restores original individual occurrences for declaration emission. That
postprocessing does not run locality again; its expanded returned declaration
signature need not be the signature used in this IsModule certificate.
-/

namespace ContextCalculus.IncrementalDataConsistency

open IncrementalModuleReuse
open IncrementalDataModuleReuse

variable {U D : Type}

/-- Fixed ranges/literal maps live outside this interpretation and are not masked. -/
def maskAug (S : Nat → Bool) (i : DataInterp U D) : DataInterp U D where
  obj := mask S i.obj
  dp p x d := S p = true ∧ i.dp p x d

def DataInSig (S : Nat → Bool) : DataAx → Prop
  | .domain p c => S p = true ∧ InSig S c
  | .sub p q | .disjoint p q => S p = true ∧ S q = true
  | .range p _ | .functional p | .asserted p _ _ | .negative p _ _ => S p = true

/-- Datatype/literal maps and individual denotations are fixed by masking. -/
def OccursData (n : Nat) : DataAx → Prop
  | .domain p c => n = p ∨ OccursC n c
  | .sub p q | .disjoint p q => n = p ∨ n = q
  | .range p _ | .functional p | .asserted p _ _ | .negative p _ _ => n = p

theorem data_insig_of_occurs (S : Nat → Bool) (a : DataAx)
    (h : ∀ n, OccursData n a → S n = true) : DataInSig S a := by
  cases a with
  | domain p c =>
      exact ⟨h p (Or.inl rfl), insig_of_occurs S c (fun n hn => h n (Or.inr hn))⟩
  | sub p q | disjoint p q => exact ⟨h p (Or.inl rfl), h q (Or.inr rfl)⟩
  | range p _ | functional p | asserted p _ _ | negative p _ _ => exact h p rfl

theorem satData_mask_agree (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) :
    ∀ a, DataInSig S a →
      (satData ranges literal (maskAug S i) a ↔ satData ranges literal i a)
  | .domain p c, h => by
      simp only [satData]
      exact forall_congr' fun x => forall_congr' fun d => by
        simp only [maskAug, h.1, true_and]
        rw [eval_mask_agree S i.obj c h.2 x]
  | .range p t, h => by
      change S p = true at h
      simp only [satData, maskAug, h, true_and]
  | .sub p q, h => by simp only [satData, maskAug, h.1, h.2, true_and]
  | .functional p, h => by
      change S p = true at h
      simp only [satData, maskAug, h, true_and]
  | .disjoint p q, h => by simp only [satData, maskAug, h.1, h.2, true_and]
  | .asserted p n l, h => by
      change S p = true at h
      simp only [satData, maskAug, mask, h, true_and]
  | .negative p n l, h => by
      change S p = true at h
      simp only [satData, maskAug, mask, h, true_and]

/-- `false` is sufficient for data-axiom locality; property names are ordinary
masked names, never the universal data property. -/
def nonLocalData (S : Nat → Bool) : DataAx → Bool
  | .domain p c => S p && notTop S c
  | .disjoint p q => S p && S q
  | .range p _ | .sub p _ | .functional p | .negative p _ _ => S p
  | .asserted _ _ _ => true

theorem data_locality_sound (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) :
    ∀ a, nonLocalData S a = false → satData ranges literal (maskAug S i) a
  | .domain p c, h => by
      intro x d hp
      rcases Bool.and_eq_false_iff.mp h with h | h
      · simp [maskAug, h] at hp
      · exact (locality_sound S i.obj c x).2 h
  | .range p t, h => by
      intro x d hp
      simp [nonLocalData] at h
      simp [maskAug, h] at hp
  | .sub p q, h => by
      intro x d hp
      simp [nonLocalData] at h
      simp [maskAug, h] at hp
  | .functional p, h => by
      intro x d e hp _
      simp [nonLocalData] at h
      simp [maskAug, h] at hp
  | .disjoint p q, h => by
      intro x d hp hq
      rcases Bool.and_eq_false_iff.mp h with h | h
      · simp [maskAug, h] at hp
      · simp [maskAug, h] at hq
  | .asserted _ _ _, h => by simp [nonLocalData] at h
  | .negative p n l, h => by
      intro hp
      simp [nonLocalData] at h
      simp [maskAug, h] at hp

def OccursAug (n : Nat) : AugAx → Prop
  | .object a => OccursA n a
  | .data a => OccursData n a

def nonLocalAug (S : Nat → Bool) : AugAx → Bool
  | .object a => nonLocal S a
  | .data a => nonLocalData S a

theorem satAug_mask_agree (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) (a : AugAx)
    (h : ∀ n, OccursAug n a → S n = true) :
    satAug ranges literal (maskAug S i) a ↔ satAug ranges literal i a := by
  cases a with
  | object a => exact sat_mask_agree S i.obj a (axinsig_of_occurs S a h)
  | data a => exact satData_mask_agree ranges literal S i a (data_insig_of_occurs S a h)

theorem augmented_locality_sound (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) (a : AugAx)
    (h : nonLocalAug S a = false) : satAug ranges literal (maskAug S i) a := by
  cases a with
  | object a => exact axiom_local_sound S i.obj a h
  | data a => exact data_locality_sound ranges literal S i a h

def DataModel (D : Type) := Σ U : Type, DataInterp U D

/-- Every interpretation has the same fixed D/ranges/literal semantics. -/
noncomputable def augmented (ranges : Nat → D → Prop) (literal : Nat → D) :
    MaskedSemantics AugAx (Concept × Concept) (DataModel D) Nat where
  sat m a := satAug ranges literal m.2 a
  holds m q := holds m.2.obj q
  mask S m := ⟨m.1, maskAug (bsig S) m.2⟩
  sigAx a n := OccursAug n a
  sigQ q n := OccursC n q.1 ∨ OccursC n q.2
  agree_ax := by
    intro S m a h
    exact satAug_mask_agree ranges literal (bsig S) m.2 a
      (fun n hn => bsig_true (h n hn))
  agree_q := by
    intro S m q h
    exact sroiq.agree_q S ⟨m.1, m.2.obj⟩ q h

theorem augmented_isModule_of_closed {ranges : Nat → D → Prop} {literal : Nat → D}
    {O M : AugAx → Prop} {S : Nat → Prop}
    (hsub : ∀ a, M a → O a)
    (hcov : ∀ a, M a → ∀ n, OccursAug n a → S n)
    (hclosed : ∀ a, O a → ¬ M a → nonLocalAug (bsig S) a = false) :
    IsModule (augmented ranges literal) O M S := by
  refine ⟨hsub, hcov, ?_⟩
  intro a ha hm m
  exact augmented_locality_sound ranges literal (bsig S) m.2 a (hclosed a ha hm)

/-- Full augmented module consistency transfers through OLD alone, using
the closed extraction signature S0 rather than the initial empty seed. -/
theorem augmented_union_consistent {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD V M0 : AugAx → Prop} {S0 : Nat → Prop}
    (hm : IsModule (augmented ranges literal) V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a)
    (hold : IncrementalDataModuleReuse.Consistent ranges literal OLD) :
    IncrementalDataModuleReuse.Consistent ranges literal V := by
  obtain ⟨W, i, hi⟩ := hold
  have oldModel : ∃ m, IncrementalModuleReuse.Models (augmented ranges literal) OLD m :=
    ⟨⟨W, i⟩, hi⟩
  obtain ⟨m, hm⟩ := IncrementalUnionConsistency.union_model_of_old_model
    (augmented ranges literal) hm hkeep oldModel
  exact ⟨m.1, m.2, hm⟩

theorem augmented_new_consistent {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD NEW V M0 : AugAx → Prop} {S0 : Nat → Prop}
    (hm : IsModule (augmented ranges literal) V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : IncrementalDataModuleReuse.Consistent ranges literal OLD) :
    IncrementalDataModuleReuse.Consistent ranges literal NEW := by
  obtain ⟨W, i, hi⟩ := augmented_union_consistent hm hkeep hold
  exact ⟨W, i, fun a ha => hi a (hnew a ha)⟩

/-- Data/nominal axioms stay outside the plain object NEW module; consistency
comes from full augmented locality, with the very same fixed data semantics. -/
theorem augmented_affected_module_from_union
    {ranges : Nat → D → Prop} {literal : Nat → D} {OLD NEW V M0 : AugAx → Prop}
    {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (augmented ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : IncrementalDataModuleReuse.Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.object a)) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.object a) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.data a) → allowedData a) :
    Module ranges literal NEW M S :=
  module_from_envelope (fun _ h => h) hkeep hplain hcov hrest hdata
    (augmented_new_consistent hm0 hkeep0 hnew hold)

theorem augmented_affected_named_query
    {ranges : Nat → D → Prop} {literal : Nat → D} {OLD NEW V M0 : AugAx → Prop}
    {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (augmented ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : IncrementalDataModuleReuse.Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.object a)) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.object a) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.data a) → allowedData a)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    IncrementalDataModuleReuse.Entails ranges literal NEW (c, .atom b) ↔
      EntailsC M (c, .atom b) :=
  module_named_query
    (augmented_affected_module_from_union hm0 hkeep0 hnew hold hkeep hplain hcov hrest hdata)
    hc hs b

theorem augmented_affected_unsat_query
    {ranges : Nat → D → Prop} {literal : Nat → D} {OLD NEW V M0 : AugAx → Prop}
    {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (augmented ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : IncrementalDataModuleReuse.Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.object a)) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.object a) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.data a) → allowedData a)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) :
    IncrementalDataModuleReuse.Entails ranges literal NEW (c, .bot) ↔ EntailsC M (c, .bot) :=
  module_entails_iff
    (augmented_affected_module_from_union hm0 hkeep0 hnew hold hkeep hplain hcov hrest hdata)
    (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)

#print axioms data_insig_of_occurs
#print axioms satData_mask_agree
#print axioms data_locality_sound
#print axioms satAug_mask_agree
#print axioms augmented_locality_sound
#print axioms augmented_isModule_of_closed
#print axioms augmented_union_consistent
#print axioms augmented_new_consistent
#print axioms augmented_affected_module_from_union
#print axioms augmented_affected_named_query
#print axioms augmented_affected_unsat_query

end ContextCalculus.IncrementalDataConsistency
