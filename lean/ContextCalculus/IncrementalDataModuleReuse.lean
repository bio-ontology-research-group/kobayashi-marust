import ContextCalculus.IncrementalModuleReuse

/-!
# Object-module reuse with a separate data-property envelope

Datatype ranges and literal values are fixed parameters of the theory. A
countermodel of a pure object module gains no data-property edges on its fresh
left component. The right component is an actual model of the complete source,
with the same value domain, ranges and literal map. Domain axioms require
universal-object-role-free concepts so their right-side meaning is preserved.

The executable boundary must reject data class constructors, datatype
definitions, keys, rules, universal object/data properties and unknown forms.
It must mark every data TBox axiom as well as changed and nominal axioms, so a
retained module is object-only and nominal-free. OLD and NEW consistency are
independent premises; no model of their union is assumed. Source admission,
exact identities, class domains and complete selected-subject classification
remain executable obligations. This module neither skips NEW consistency nor
certifies parsing or arbitrary datatype reasoning.
-/

namespace ContextCalculus.IncrementalDataModuleReuse

open IncrementalModuleReuse

structure DataInterp (U D : Type) where
  obj : Interp U
  dp : Nat → U → D → Prop

inductive DataAx where
  | domain : Nat → Concept → DataAx
  | range : Nat → Nat → DataAx
  | sub : Nat → Nat → DataAx
  | functional : Nat → DataAx
  | disjoint : Nat → Nat → DataAx
  | asserted : Nat → Nat → Nat → DataAx
  | negative : Nat → Nat → Nat → DataAx

inductive AugAx where
  | object : Axiom → AugAx
  | data : DataAx → AugAx

variable {U V D : Type}

def satData (ranges : Nat → D → Prop) (literal : Nat → D)
    (i : DataInterp U D) : DataAx → Prop
  | .domain p c => ∀ x d, i.dp p x d → eval i.obj c x
  | .range p t => ∀ x d, i.dp p x d → ranges t d
  | .sub p q => ∀ x d, i.dp p x d → i.dp q x d
  | .functional p => ∀ x d e, i.dp p x d → i.dp p x e → d = e
  | .disjoint p q => ∀ x d, i.dp p x d → i.dp q x d → False
  | .asserted p n l => i.dp p (i.obj.ind n) (literal l)
  | .negative p n l => ¬ i.dp p (i.obj.ind n) (literal l)

def allowedData : DataAx → Prop
  | .domain _ c => TopFree c
  | _ => True

def satAug (ranges : Nat → D → Prop) (literal : Nat → D)
    (i : DataInterp U D) : AugAx → Prop
  | .object a => sat i.obj a
  | .data a => satData ranges literal i a

def Models (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : AugAx → Prop) (i : DataInterp U D) : Prop :=
  ∀ a, O a → satAug ranges literal i a

def Consistent (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : AugAx → Prop) : Prop :=
  ∃ (W : Type) (i : DataInterp W D), Models ranges literal O i

/-- The fixed value/range interpretation is shared by every queried model. -/
def Entails (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : AugAx → Prop) (q : Concept × Concept) : Prop :=
  ∀ (W : Type) (i : DataInterp W D), Models ranges literal O i →
    ∀ x, eval i.obj q.1 x → eval i.obj q.2 x

def joinData (i : Interp U) (j : DataInterp V D) : DataInterp (U ⊕ V) D where
  obj := union i j.obj
  dp p x d := match x with
    | .inl _ => False
    | .inr y => j.dp p y d

/-- Empty data roles on the fresh side preserve every allowed data axiom. -/
theorem joinData_sat (ranges : Nat → D → Prop) (literal : Nat → D)
    (i : Interp U) (j : DataInterp V D) :
    ∀ a, allowedData a → satData ranges literal j a →
      satData ranges literal (joinData i j) a
  | .domain p c, hc, h => by
      intro x d hp
      cases x with
      | inl x => exact hp.elim
      | inr y => exact (eval_union_inr i j.obj c hc y).mpr (h y d hp)
  | .range p t, _, h => by
      intro x d hp
      cases x with
      | inl x => exact hp.elim
      | inr y => exact h y d hp
  | .sub p q, _, h => by
      intro x d hp
      cases x with
      | inl x => exact hp.elim
      | inr y => exact h y d hp
  | .functional p, _, h => by
      intro x d e hp hq
      cases x with
      | inl x => exact hp.elim
      | inr y => exact h y d e hp hq
  | .disjoint p q, _, h => by
      intro x d hp hq
      cases x with
      | inl x => exact hp.elim
      | inr y => exact h y d hp hq
  | .asserted p n l, _, h => h
  | .negative p n l, _, h => h

structure Module (ranges : Nat → D → Prop) (literal : Nat → D)
    (O : AugAx → Prop) (M : Axiom → Prop) (S : Nat → Prop) : Prop where
  objectModule : NominalModule (fun a => O (.object a)) M S
  dataAllowed : ∀ a, O (.data a) → allowedData a
  consistent : Consistent ranges literal O

/-- Envelope analysis supplies locality; actual source consistency supplies the
right model. The envelope itself need not be consistent. -/
theorem module_from_envelope {ranges : Nat → D → Prop} {literal : Nat → D}
    {V : Axiom → Prop} {O : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hsub : ∀ a, O (.object a) → V a) (hkeep : ∀ a, M a → O (.object a))
    (hplain : ∀ a, M a → PlainAx a)
    (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hrest : ∀ a, V a → ¬ M a →
      AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false))
    (hdata : ∀ a, O (.data a) → allowedData a)
    (hconsistent : Consistent ranges literal O) : Module ranges literal O M S := by
  obtain ⟨W, j, hj⟩ := hconsistent
  refine ⟨nominal_module_from_envelope hsub hkeep hplain hcov hrest ?_, hdata,
    ⟨W, j, hj⟩⟩
  exact ⟨W, j.obj, fun a ha => hj (.object a) ha⟩

/-- Extend any pure object-module model using a complete source model's data. -/
theorem module_join_models {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (i : Interp U) (hi : ∀ a, M a → sat i a)
    (j : DataInterp V D) (hj : Models ranges literal O j) :
    Models ranges literal O (joinData (mask (bsig S) i) j) := by
  intro a ha
  cases a with
  | object a =>
      exact nominal_union_models hm.objectModule i hi j.obj
        (fun b hb => hj (.object b) hb) a ha
  | data a =>
      exact joinData_sat ranges literal _ j a (hm.dataAllowed a ha)
        (hj (.data a) ha)

theorem module_entails_iff {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
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
    exact e W i.obj (fun a ha => hi (.object a) (hm.objectModule.sub a ha))

/-- Outside targets require an unsatisfiable subject; no target-signature
assumption is hidden in whole-row reuse. -/
theorem module_outside {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
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
  have absent : bsig S b = false := by
    classical
    simp [bsig, hb]
  simpa [eval, joinData, union, mask, absent] using result

theorem module_named_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
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
    exact e W i.obj (fun a ha => hi (.object a) (hm.objectModule.sub a ha))

theorem common_named_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O O' : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (hm' : Module ranges literal O' M S)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) (b : Nat) :
    Entails ranges literal O (c, .atom b) ↔ Entails ranges literal O' (c, .atom b) :=
  (module_named_query hm hc hs b).trans (module_named_query hm' hc hs b).symm

theorem common_unsat_query {ranges : Nat → D → Prop} {literal : Nat → D}
    {O O' : AugAx → Prop} {M : Axiom → Prop} {S : Nat → Prop}
    (hm : Module ranges literal O M S) (hm' : Module ranges literal O' M S)
    {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n) :
    Entails ranges literal O (c, .bot) ↔ Entails ranges literal O' (c, .bot) :=
  (module_entails_iff hm (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)).trans
    (module_entails_iff hm' (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)).symm

/-- Production merge: fresh complete NEW rows for affected subjects, old rows
only where structural common modules and both actual consistency models exist. -/
theorem mixed_named_publication_exact {Subj : Type} (subject : Subj → Concept)
    {ranges : Nat → D → Prop} {literal : Nat → D} {O O' : AugAx → Prop}
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
    {ranges : Nat → D → Prop} {literal : Nat → D} {O O' : AugAx → Prop}
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

#print axioms joinData_sat
#print axioms module_from_envelope
#print axioms module_join_models
#print axioms module_entails_iff
#print axioms module_outside
#print axioms module_named_query
#print axioms common_named_query
#print axioms common_unsat_query
#print axioms mixed_named_publication_exact
#print axioms mixed_unsat_publication_exact

end ContextCalculus.IncrementalDataModuleReuse
