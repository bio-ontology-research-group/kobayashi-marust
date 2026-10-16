import ContextCalculus.IncrementalDataConsistency

/-!
# Fixed-domain data cardinality in retained object modules

This boundary adds only top-level inclusions from an ordinary named class to
an unqualified minimum-one or exact-one restriction on an ordinary data
property. The executable guard must reject nested or qualified restrictions,
other cardinalities and built-in class/property aliases outside this model.
The value domain, datatype ranges and literal map remain fixed across models.
Existing object/data axiom types and their proof APIs are unchanged.

Full masking agrees on retained class/property names. The exact non-locality
trigger of either new inclusion is its class owner. A closed logical module
which omits a marked cardinal axiom therefore excludes that owner. Every
cardinal owner must be marked even when its source statement is unchanged.

Object query reuse requires this owner-absence premise explicitly: empty data
relations on the fresh side cannot satisfy an inhabited positive-cardinality
owner. No data witnesses are manufactured. The optional affected object-module
path has the same premise for every NEW cardinal axiom and must decline when
it fails. Full consistency follows only from a closed full-union module kept
in an actually consistent OLD source; the closed signature may be nonempty.

All signature premises refer to the logical fixpoint, before declaration
emission restores original occurrences. Exact source admission, constructor and
alias resolution, compiler formulas, marked owners and complete publication
remain executable obligations. These theorems do not certify parsing or resume
an incremental backend.
-/
namespace ContextCalculus.IncrementalDataCardinality

open IncrementalModuleReuse
open IncrementalDataModuleReuse
open IncrementalDataConsistency

inductive CardAx where
  | minOne : Nat → Nat → CardAx
  | exactOne : Nat → Nat → CardAx

def owner : CardAx → Nat
  | .minOne c _ | .exactOne c _ => c

def property : CardAx → Nat
  | .minOne _ p | .exactOne _ p => p

inductive ExtAx where
  | base : AugAx → ExtAx
  | card : CardAx → ExtAx

variable {U V D : Type}

def satCard (i : DataInterp U D) : CardAx → Prop
  | .minOne c p => ∀ x, i.obj.cls c x → ∃ d, i.dp p x d
  | .exactOne c p => ∀ x, i.obj.cls c x → ∃! d, i.dp p x d

def satExt (ranges : Nat → D → Prop) (literal : Nat → D)
    (i : DataInterp U D) : ExtAx → Prop
  | .base a => satAug ranges literal i a
  | .card a => satCard i a

def Models (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : ExtAx → Prop) (i : DataInterp U D) : Prop :=
  ∀ a, O a → satExt ranges literal i a

def Consistent (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : ExtAx → Prop) : Prop :=
  ∃ (W : Type) (i : DataInterp W D), Models ranges literal O i

def Entails (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : ExtAx → Prop) (q : Concept × Concept) : Prop :=
  ∀ (W : Type) (i : DataInterp W D), Models ranges literal O i →
    ∀ x, eval i.obj q.1 x → eval i.obj q.2 x

def OccursCard (n : Nat) (a : CardAx) : Prop :=
  n = owner a ∨ n = property a

def CardInSig (S : Nat → Bool) (a : CardAx) : Prop :=
  S (owner a) = true ∧ S (property a) = true

theorem card_insig_of_occurs (S : Nat → Bool) (a : CardAx)
    (h : ∀ n, OccursCard n a → S n = true) : CardInSig S a :=
  ⟨h _ (Or.inl rfl), h _ (Or.inr rfl)⟩

theorem satCard_mask_agree (S : Nat → Bool) (i : DataInterp U D)
    (a : CardAx) (h : CardInSig S a) :
    satCard (maskAug S i) a ↔ satCard i a := by
  cases a <;> rcases h with ⟨hc, hp⟩ <;>
    simp only [owner, property] at hc hp <;>
    simp [satCard, maskAug, mask, hc, hp]

/-- For positive unqualified cardinality, the exact Rust trigger is SigC. -/
def nonLocalCard (S : Nat → Bool) (a : CardAx) : Bool := S (owner a)

theorem card_locality_sound (S : Nat → Bool) (i : DataInterp U D)
    (a : CardAx) (h : nonLocalCard S a = false) : satCard (maskAug S i) a := by
  cases a <;> simp [nonLocalCard, owner] at h <;>
    simp [satCard, maskAug, mask, h]

def OccursExt (n : Nat) : ExtAx → Prop
  | .base a => OccursAug n a
  | .card a => OccursCard n a

def nonLocalExt (S : Nat → Bool) : ExtAx → Bool
  | .base a => nonLocalAug S a
  | .card a => nonLocalCard S a

theorem satExt_mask_agree (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) (a : ExtAx)
    (h : ∀ n, OccursExt n a → S n = true) :
    satExt ranges literal (maskAug S i) a ↔ satExt ranges literal i a := by
  cases a with
  | base a => exact satAug_mask_agree ranges literal S i a h
  | card a => exact satCard_mask_agree S i a (card_insig_of_occurs S a h)

theorem extended_locality_sound (ranges : Nat → D → Prop) (literal : Nat → D)
    (S : Nat → Bool) (i : DataInterp U D) (a : ExtAx)
    (h : nonLocalExt S a = false) : satExt ranges literal (maskAug S i) a := by
  cases a with
  | base a => exact augmented_locality_sound ranges literal S i a h
  | card a => exact card_locality_sound S i a h

noncomputable def extended (ranges : Nat → D → Prop) (literal : Nat → D) :
    MaskedSemantics ExtAx (Concept × Concept) (DataModel D) Nat where
  sat m a := satExt ranges literal m.2 a
  holds m q := holds m.2.obj q
  mask S m := ⟨m.1, maskAug (bsig S) m.2⟩
  sigAx a n := OccursExt n a
  sigQ q n := OccursC n q.1 ∨ OccursC n q.2
  agree_ax := by
    intro S m a h
    exact satExt_mask_agree ranges literal (bsig S) m.2 a
      (fun n hn => bsig_true (h n hn))
  agree_q := by
    intro S m q h
    exact sroiq.agree_q S ⟨m.1, m.2.obj⟩ q h

theorem extended_isModule_of_closed {ranges : Nat → D → Prop} {literal : Nat → D}
    {O M : ExtAx → Prop} {S : Nat → Prop}
    (hsub : ∀ a, M a → O a)
    (hcov : ∀ a, M a → ∀ n, OccursExt n a → S n)
    (hclosed : ∀ a, O a → ¬ M a → nonLocalExt (bsig S) a = false) :
    IsModule (extended ranges literal) O M S := by
  refine ⟨hsub, hcov, ?_⟩
  intro a ha hm m
  exact extended_locality_sound ranges literal (bsig S) m.2 a (hclosed a ha hm)

theorem extended_union_consistent {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD V M0 : ExtAx → Prop} {S0 : Nat → Prop}
    (hm : IsModule (extended ranges literal) V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a) (hold : Consistent ranges literal OLD) :
    Consistent ranges literal V := by
  obtain ⟨W, i, hi⟩ := hold
  have oldModel : ∃ m, IncrementalModuleReuse.Models (extended ranges literal) OLD m :=
    ⟨⟨W, i⟩, hi⟩
  obtain ⟨m, hm⟩ := IncrementalUnionConsistency.union_model_of_old_model
    (extended ranges literal) hm hkeep oldModel
  exact ⟨m.1, m.2, hm⟩

theorem extended_new_consistent {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD NEW V M0 : ExtAx → Prop} {S0 : Nat → Prop}
    (hm : IsModule (extended ranges literal) V M0 S0)
    (hkeep : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : Consistent ranges literal OLD) : Consistent ranges literal NEW := by
  obtain ⟨W, i, hi⟩ := extended_union_consistent hm hkeep hold
  exact ⟨W, i, fun a ha => hi a (hnew a ha)⟩

/-- Omitted marked cardinal owner plus closed locality implies owner absence. -/
theorem owner_absent_of_omitted {V M : ExtAx → Prop} {S : Nat → Prop}
    (closed : ∀ a, V a → ¬ M a → nonLocalExt (bsig S) a = false)
    (a : CardAx) (hv : V (.card a)) (hm : ¬ M (.card a)) : ¬ S (owner a) := by
  have h := closed (.card a) hv hm
  change bsig S (owner a) = false at h
  intro hs
  rw [bsig_true hs] at h
  contradiction

/-- No data witnesses are manufactured on the fresh side: owner absence is
essential. Existing base joinData_sat and allowedData remain unchanged. -/
theorem joinData_mask_sat (S : Nat → Prop) (i : Interp U) (j : DataInterp V D)
    (a : CardAx) (h : ¬ S (owner a)) (hj : satCard j a) :
    satCard (joinData (mask (bsig S) i) j) a := by
  cases a with
  | minOne c p =>
      have hc : bsig S c = false := by classical simpa [bsig, owner] using h
      intro x hx
      cases x with
      | inl x => simp [joinData, union, mask, hc] at hx
      | inr y => exact hj y hx
  | exactOne c p =>
      have hc : bsig S c = false := by classical simpa [bsig, owner] using h
      intro x hx
      cases x with
      | inl x => simp [joinData, union, mask, hc] at hx
      | inr y => exact hj y hx

structure Module (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : ExtAx → Prop) (M : Axiom → Prop) (S : Nat → Prop) : Prop where
  baseModule : IncrementalDataModuleReuse.Module ranges literal (fun a => O (.base a)) M S
  cardAbsent : ∀ a, O (.card a) → ¬ S (owner a)
  consistent : Consistent ranges literal O

theorem module_from_envelope {ranges : Nat → D → Prop} {literal : Nat → D}
    {V : Axiom → Prop} {O : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hsub : ∀ a, O (.base (.object a)) → V a)
    (hkeep : ∀ a, M a → O (.base (.object a))) (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, V a → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, O (.base (.data a)) → allowedData a)
    (hcard : ∀ a, O (.card a) → ¬ S (owner a))
    (hconsistent : Consistent ranges literal O) : Module ranges literal O M S := by
  obtain ⟨W, j, hj⟩ := hconsistent
  refine ⟨?_, hcard, ⟨W, j, hj⟩⟩
  exact IncrementalDataModuleReuse.module_from_envelope hsub hkeep hplain hcov hrest
    hdata ⟨W, j, fun a ha => hj (.base a) ha⟩

theorem module_join_models {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (i : Interp U) (hi : ∀ a, M a → sat i a)
    (j : DataInterp V D) (hj : Models ranges literal O j) :
    Models ranges literal O (joinData (mask (bsig S) i) j) := by
  intro a ha
  cases a with
  | base a =>
      exact IncrementalDataModuleReuse.module_join_models hm.baseModule i hi j
        (fun b hb => hj (.base b) hb) a ha
  | card a => exact joinData_mask_sat S i j a (hm.cardAbsent a ha) (hj (.card a) ha)

theorem module_entails_iff {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) {q : Concept × Concept}
    (hc : Plain q.1) (hd : Plain q.2)
    (hs : ∀ n, OccursC n q.1 → S n) (ht : ∀ n, OccursC n q.2 → S n) :
    Entails ranges literal O q ↔ EntailsC M q := by
  constructor
  · intro e W i hi x hx
    obtain ⟨V, j, hj⟩ := hm.consistent
    have joined := module_join_models hm i hi j hj
    have a1 := eval_mask_agree (bsig S) i q.1
      (insig_of_occurs _ q.1 fun n hn => bsig_true (hs n hn)) x
    have a2 := eval_mask_agree (bsig S) i q.2
      (insig_of_occurs _ q.2 fun n hn => bsig_true (ht n hn)) x
    have result := e (W ⊕ V) _ joined (.inl x)
      ((eval_union_inl _ j.obj q.1 hc x).mpr (a1.mpr hx))
    exact a2.mp ((eval_union_inl _ j.obj q.2 hd x).mp result)
  · intro e W i hi
    exact e W i.obj (fun a ha => hi (.base (.object a)) (hm.baseModule.objectModule.sub a ha))

theorem module_outside {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) {c : Concept} (hc : Plain c)
    (hs : ∀ n, OccursC n c → S n) {b : Nat} (hb : ¬ S b)
    (e : Entails ranges literal O (c, .atom b)) : EntailsC M (c, .bot) := by
  intro W i hi x hx
  obtain ⟨V, j, hj⟩ := hm.consistent
  have joined := module_join_models hm i hi j hj
  have a1 := eval_mask_agree (bsig S) i c
    (insig_of_occurs _ c fun n hn => bsig_true (hs n hn)) x
  have result := e (W ⊕ V) _ joined (.inl x)
    ((eval_union_inl _ j.obj c hc x).mpr (a1.mpr hx))
  have absent : bsig S b = false := by classical simp [bsig, hb]
  simpa [eval, joinData, union, mask, absent] using result

theorem module_named_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) {c : Concept} (hc : Plain c)
    (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    Entails ranges literal O (c, .atom b) ↔ EntailsC M (c, .atom b) := by
  constructor
  · intro e
    by_cases hb : S b
    · exact (module_entails_iff hm (q := (c, .atom b)) hc trivial hs
        (fun n hn => by change n = b at hn; exact hn.symm ▸ hb)).mp e
    · have hbot := module_outside hm hc hs hb e
      intro W i hi x hx
      exact False.elim (hbot W i hi x hx)
  · intro e W i hi
    exact e W i.obj (fun a ha => hi (.base (.object a)) (hm.baseModule.objectModule.sub a ha))

theorem common_named_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O O' : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (hm' : Module ranges literal O' M S)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    Entails ranges literal O (c, .atom b) ↔ Entails ranges literal O' (c, .atom b) :=
  (module_named_query hm hc hs b).trans (module_named_query hm' hc hs b).symm

theorem common_unsat_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O O' : ExtAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (hm' : Module ranges literal O' M S)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) :
    Entails ranges literal O (c, .bot) ↔ Entails ranges literal O' (c, .bot) :=
  (module_entails_iff hm (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)).trans
    (module_entails_iff hm' (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)).symm

theorem mixed_named_publication_exact {Subj : Type} (subject : Subj → Concept)
    {ranges : Nat → D → Prop} {literal : Nat → D} {O O' : ExtAx → Prop}
    (affected : Subj → Prop) [DecidablePred affected]
    (common : ∀ s, ¬ affected s → ∃ M S, Module ranges literal O M S ∧
      Module ranges literal O' M S ∧ Plain (subject s) ∧
      ∀ n, OccursC n (subject s) → S n) (s : Subj) (b : Nat) :
    (if affected s then Entails ranges literal O' (subject s, .atom b)
      else Entails ranges literal O (subject s, .atom b)) ↔
      Entails ranges literal O' (subject s, .atom b) := by
  by_cases h : affected s
  · rw [if_pos h]
  · rw [if_neg h]
    obtain ⟨M, S, hm, hm', hc, hs⟩ := common s h
    exact common_named_query hm hm' hc hs b

theorem mixed_unsat_publication_exact {Subj : Type} (subject : Subj → Concept)
    {ranges : Nat → D → Prop} {literal : Nat → D} {O O' : ExtAx → Prop}
    (affected : Subj → Prop) [DecidablePred affected]
    (common : ∀ s, ¬ affected s → ∃ M S, Module ranges literal O M S ∧
      Module ranges literal O' M S ∧ Plain (subject s) ∧
      ∀ n, OccursC n (subject s) → S n) (s : Subj) :
    (if affected s then Entails ranges literal O' (subject s, .bot)
      else Entails ranges literal O (subject s, .bot)) ↔
      Entails ranges literal O' (subject s, .bot) := by
  by_cases h : affected s
  · rw [if_pos h]
  · rw [if_neg h]
    obtain ⟨M, S, hm, hm', hc, hs⟩ := common s h
    exact common_unsat_query hm hm' hc hs

#print axioms satCard_mask_agree
#print axioms card_locality_sound
#print axioms extended_isModule_of_closed
#print axioms extended_union_consistent
#print axioms extended_new_consistent
#print axioms owner_absent_of_omitted
#print axioms joinData_mask_sat
#print axioms module_from_envelope
#print axioms module_join_models
#print axioms module_entails_iff
#print axioms module_outside
#print axioms common_named_query
#print axioms common_unsat_query
#print axioms mixed_named_publication_exact
#print axioms mixed_unsat_publication_exact

theorem extended_affected_module_from_union
    {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD NEW V M0 : ExtAx → Prop} {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (extended ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.base (.object a)))
    (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.base (.object a)) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.base (.data a)) → allowedData a)
    (hcard : ∀ a, NEW (.card a) → ¬ S (owner a)) :
    Module ranges literal NEW M S :=
  module_from_envelope (fun _ h => h) hkeep hplain hcov hrest hdata hcard
    (extended_new_consistent hm0 hkeep0 hnew hold)

theorem extended_affected_named_query
    {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD NEW V M0 : ExtAx → Prop} {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (extended ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.base (.object a)))
    (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.base (.object a)) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.base (.data a)) → allowedData a)
    (hcard : ∀ a, NEW (.card a) → ¬ S (owner a))
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    Entails ranges literal NEW (c, .atom b) ↔ EntailsC M (c, .atom b) :=
  module_named_query
    (extended_affected_module_from_union hm0 hkeep0 hnew hold
      hkeep hplain hcov hrest hdata hcard) hc hs b

theorem extended_affected_unsat_query
    {ranges : Nat → D → Prop} {literal : Nat → D}
    {OLD NEW V M0 : ExtAx → Prop} {M : Axiom → Prop} {S0 S : Nat → Prop}
    (hm0 : IsModule (extended ranges literal) V M0 S0)
    (hkeep0 : ∀ a, M0 a → OLD a) (hnew : ∀ a, NEW a → V a)
    (hold : Consistent ranges literal OLD)
    (hkeep : ∀ a, M a → NEW (.base (.object a)))
    (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, NEW (.base (.object a)) → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, NEW (.base (.data a)) → allowedData a)
    (hcard : ∀ a, NEW (.card a) → ¬ S (owner a))
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) :
    Entails ranges literal NEW (c, .bot) ↔ EntailsC M (c, .bot) :=
  module_entails_iff
    (extended_affected_module_from_union hm0 hkeep0 hnew hold
      hkeep hplain hcov hrest hdata hcard)
    (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)

#print axioms extended_affected_module_from_union
#print axioms extended_affected_named_query
#print axioms extended_affected_unsat_query

end ContextCalculus.IncrementalDataCardinality
