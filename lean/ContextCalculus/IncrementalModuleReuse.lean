import Mathlib.Data.List.Nodup

/-!
# Module reuse for retained source revisions

The retained `km incremental-source` session publishes, for a revision `O'`
obtained from a stored, completely classified and consistent revision `O` by
deleting axioms:

* the stored answer of every subject whose ⊥-module in `O` contains no
  deleted axiom (`unaffected_query`);
* the answer of the unchanged classification pipeline on a source `U` with
  `M ⊆ U ⊆ O'` for a module `M` of `O'`, for every other subject
  (`sandwich_query`);
* no answer change for a subject that had no superclass and was satisfiable in
  `O` (`deletion_no_new_consequence`).

The abstract part states these for any semantics with a signature-indexed
masking operation. The concrete part instantiates it for SROIQ concepts with
inverse, universal and empty roles, qualified number restrictions, nominals
and self restrictions, role chains and role characteristics, and assertions:
syntactic ⊥-locality (the Rust formulas `notBot`/`notTop`) is sound
(`axiom_local_sound`) and masking preserves everything inside the signature
(`eval_mask_agree`, `sat_mask_agree`). Finally the TBox-only index used when
no compiled axiom mentions an individual or the universal role is justified
by a disjoint-union model (`tbox_entails_iff`): for a consistent ontology the
assertions cannot change a subsumption between such concepts.

Datatypes, keys and DL-safe rules are outside this model; the Rust compiler
treats datatype definitions, rules, reflexivity, positive property assertions
and every unknown statement as non-local, and data properties like object
properties without inverses. The Rust/Lean binding (parser, formula compiler,
DNF weakening, fixpoint propagation) is an executable obligation checked by
tests, not by this file.
-/

namespace ContextCalculus.IncrementalModuleReuse

universe u v

/-! ## Abstract module transfer -/

section Abstract

/-- A semantics with an operation that empties every symbol outside a
signature `S`, preserving the meaning of everything inside `S`. -/
structure MaskedSemantics (Ax : Type u) (Q : Type u) (I : Type v) (Sym : Type u) where
  sat : I → Ax → Prop
  holds : I → Q → Prop
  mask : (Sym → Prop) → I → I
  sigAx : Ax → Sym → Prop
  sigQ : Q → Sym → Prop
  agree_ax : ∀ (S : Sym → Prop) (i : I) (a : Ax),
    (∀ s, sigAx a s → S s) → (sat (mask S i) a ↔ sat i a)
  agree_q : ∀ (S : Sym → Prop) (i : I) (q : Q),
    (∀ s, sigQ q s → S s) → (holds (mask S i) q ↔ holds i q)

variable {Ax Q Sym : Type u} {I : Type v} (sem : MaskedSemantics Ax Q I Sym)

def Models (O : Ax → Prop) (i : I) : Prop := ∀ a, O a → sem.sat i a

def Entails (O : Ax → Prop) (q : Q) : Prop := ∀ i, Models sem O i → sem.holds i q

/-- ⊥-locality: every masked interpretation satisfies the axiom. -/
def Local (S : Sym → Prop) (a : Ax) : Prop := ∀ i, sem.sat (sem.mask S i) a

/-- `M ⊆ O`, `sig(M) ⊆ S`, and every other axiom of `O` is local for `S`. -/
structure IsModule (O M : Ax → Prop) (S : Sym → Prop) : Prop where
  sub : ∀ a, M a → O a
  covers : ∀ a, M a → ∀ s, sem.sigAx a s → S s
  rest_local : ∀ a, O a → ¬ M a → Local sem S a

theorem entails_mono {O O' : Ax → Prop} (h : ∀ a, O' a → O a) {q : Q} :
    Entails sem O' q → Entails sem O q :=
  fun e i m => e i (fun a ha => m a (h a ha))

theorem module_entails {O M : Ax → Prop} {S : Sym → Prop} (hm : IsModule sem O M S)
    {q : Q} (hq : ∀ s, sem.sigQ q s → S s) : Entails sem O q ↔ Entails sem M q := by
  constructor
  · intro e i mi
    have mo : Models sem O (sem.mask S i) := by
      intro a ha
      by_cases hM : M a
      · exact (sem.agree_ax S i a (hm.covers a hM)).mpr (mi a hM)
      · exact hm.rest_local a ha hM i
    exact (sem.agree_q S i q hq).mp (e _ mo)
  · exact entails_mono sem hm.sub

/-- A module of `O` contained in a smaller source `O'` is a module of `O'`. -/
theorem module_restrict {O O' M : Ax → Prop} {S : Sym → Prop} (hm : IsModule sem O M S)
    (hsub : ∀ a, O' a → O a) (hM : ∀ a, M a → O' a) : IsModule sem O' M S :=
  ⟨hM, hm.covers, fun a ha hna => hm.rest_local a (hsub a ha) hna⟩

/-- Unaffected subject: its module in the stored revision avoids every
deleted axiom, so its answers are unchanged. -/
theorem unaffected_query {O O' M : Ax → Prop} {S : Sym → Prop} (hm : IsModule sem O M S)
    (hsub : ∀ a, O' a → O a) (hM : ∀ a, M a → O' a) {q : Q}
    (hq : ∀ s, sem.sigQ q s → S s) : Entails sem O q ↔ Entails sem O' q := by
  rw [module_entails sem hm hq, module_entails sem (module_restrict sem hm hsub hM) hq]

/-- Recomputed subject: any source between a module and the new revision
decides the query exactly. -/
theorem sandwich_query {O' M U : Ax → Prop} {S : Sym → Prop} (hm : IsModule sem O' M S)
    (hMU : ∀ a, M a → U a) (hU : ∀ a, U a → O' a) {q : Q}
    (hq : ∀ s, sem.sigQ q s → S s) : Entails sem O' q ↔ Entails sem U q := by
  constructor
  · intro e
    exact entails_mono sem hMU ((module_entails sem hm hq).mp e)
  · exact entails_mono sem hU

/-- Deletion never adds a consequence. -/
theorem deletion_no_new_consequence {O O' : Ax → Prop} (hsub : ∀ a, O' a → O a) {q : Q}
    (hnot : ¬ Entails sem O q) : ¬ Entails sem O' q :=
  fun e => hnot (entails_mono sem hsub e)

/-- A revision containing a subset with no model has no model. -/
theorem inconsistent_superset {J O' : Ax → Prop} (hJ : ∀ i, ¬ Models sem J i)
    (hsub : ∀ a, J a → O' a) : ∀ i, ¬ Models sem O' i :=
  fun i m => hJ i (fun a ha => m a (hsub a ha))

/-- The module of any signature of an inconsistent source is inconsistent;
so is every revision that keeps that module. -/
theorem module_inconsistent {O M O' : Ax → Prop} {S : Sym → Prop} (hm : IsModule sem O M S)
    (hO : ∀ i, ¬ Models sem O i) (hM : ∀ a, M a → O' a) : ∀ i, ¬ Models sem O' i := by
  have hMi : ∀ i, ¬ Models sem M i := by
    intro i mi
    apply hO (sem.mask S i)
    intro a ha
    by_cases h : M a
    · exact (sem.agree_ax S i a (hm.covers a h)).mpr (mi a h)
    · exact hm.rest_local a ha h i
  exact inconsistent_superset sem hMi hM

/-- The merged publication: stored rows outside the recomputed subjects and
rows of the module classification inside them equal the new revision's
answers. `affected` subjects come with a module of `O'` inside `U`;
every other subject with a module of `O` that avoids the deleted axioms. -/
theorem merged_publication_exact {Subj : Type u} (query : Subj → Q)
    {O O' U : Ax → Prop} (affected : Subj → Prop) [DecidablePred affected]
    (hU : ∀ a, U a → O' a)
    (oldModule : ∀ s, ¬ affected s → ∃ M S, IsModule sem O M S ∧ (∀ a, M a → O' a) ∧
      ∀ x, sem.sigQ (query s) x → S x)
    (hsub : ∀ a, O' a → O a)
    (newModule : ∀ s, affected s → ∃ M S, IsModule sem O' M S ∧ (∀ a, M a → U a) ∧
      ∀ x, sem.sigQ (query s) x → S x) (s : Subj) :
    (if affected s then Entails sem U (query s) else Entails sem O (query s)) ↔
      Entails sem O' (query s) := by
  by_cases h : affected s
  · rw [if_pos h]
    obtain ⟨M, S, hm, hMU, hq⟩ := newModule s h
    exact (sandwich_query sem hm hMU hU hq).symm
  · rw [if_neg h]
    obtain ⟨M, S, hm, hM, hq⟩ := oldModule s h
    exact unaffected_query sem hm hsub hM hq

end Abstract

/-! ## SROIQ concepts and syntactic ⊥-locality -/

inductive Role where
  | name : Nat → Role
  | inv : Nat → Role
  | top : Role
  | bot : Role

inductive Concept where
  | atom : Nat → Concept
  | top : Concept
  | bot : Concept
  | not : Concept → Concept
  | and : Concept → Concept → Concept
  | or : Concept → Concept → Concept
  | some : Role → Concept → Concept
  | all : Role → Concept → Concept
  | atLeast : Nat → Role → Concept → Concept
  | atMost : Nat → Role → Concept → Concept
  | nominal : Nat → Concept
  | self : Role → Concept

structure Interp (U : Type u) where
  cls : Nat → U → Prop
  rl : Nat → U → U → Prop
  ind : Nat → U

variable {U : Type u}

def Interp.role (i : Interp U) : Role → U → U → Prop
  | .name n => i.rl n
  | .inv n => fun x y => i.rl n y x
  | .top => fun _ _ => True
  | .bot => fun _ _ => False

/-- At least `k` distinct elements satisfy `P`. -/
def AtLeast (k : Nat) (P : U → Prop) : Prop :=
  ∃ l : List U, l.Nodup ∧ l.length = k ∧ ∀ y ∈ l, P y

def eval (i : Interp U) : Concept → U → Prop
  | .atom n, x => i.cls n x
  | .top, _ => True
  | .bot, _ => False
  | .not c, x => ¬ eval i c x
  | .and c d, x => eval i c x ∧ eval i d x
  | .or c d, x => eval i c x ∨ eval i d x
  | .some r c, x => ∃ y, i.role r x y ∧ eval i c y
  | .all r c, x => ∀ y, i.role r x y → eval i c y
  | .atLeast k r c, x => AtLeast k (fun y => i.role r x y ∧ eval i c y)
  | .atMost k r c, x => ¬ AtLeast (k + 1) (fun y => i.role r x y ∧ eval i c y)
  | .nominal n, x => x = i.ind n
  | .self r, x => i.role r x x

/-- Empty every class and role name outside `S`; individuals are kept. -/
def mask (S : Nat → Bool) (i : Interp U) : Interp U where
  cls n x := S n = true ∧ i.cls n x
  rl n x y := S n = true ∧ i.rl n x y
  ind := i.ind

def roleIn (S : Nat → Bool) : Role → Bool
  | .name n => S n
  | .inv n => S n
  | .top => true
  | .bot => false

mutual
/-- `false` proves the concept empty in every masked interpretation. -/
def notBot (S : Nat → Bool) : Concept → Bool
  | .atom n => S n
  | .top => true
  | .bot => false
  | .not c => notTop S c
  | .and c d => notBot S c && notBot S d
  | .or c d => notBot S c || notBot S d
  | .some r c => roleIn S r && notBot S c
  | .all _ _ => true
  | .atLeast 0 _ _ => true
  | .atLeast (_ + 1) r c => roleIn S r && notBot S c
  | .atMost _ _ _ => true
  | .nominal _ => true
  | .self r => roleIn S r

/-- `false` proves the concept universal in every masked interpretation. -/
def notTop (S : Nat → Bool) : Concept → Bool
  | .atom _ => true
  | .top => false
  | .bot => true
  | .not c => notBot S c
  | .and c d => notTop S c || notTop S d
  | .or c d => notTop S c && notTop S d
  | .some _ _ => true
  | .all r c => roleIn S r && notTop S c
  | .atLeast 0 _ _ => false
  | .atLeast (_ + 1) _ _ => true
  | .atMost _ r c => roleIn S r && notBot S c
  | .nominal _ => true
  | .self _ => true
end

theorem role_mask_empty {S : Nat → Bool} {r : Role} (h : roleIn S r = false)
    (i : Interp U) (x y : U) : ¬ (mask S i).role r x y := by
  cases r with
  | name n => simp [roleIn] at h; simp [Interp.role, mask, h]
  | inv n => simp [roleIn] at h; simp [Interp.role, mask, h]
  | top => simp [roleIn] at h
  | bot => simp [Interp.role]

theorem atLeast_succ_empty {k : Nat} {P : U → Prop} (h : ∀ y, ¬ P y) :
    ¬ AtLeast (k + 1) P := by
  rintro ⟨l, _, hl, hp⟩
  cases l with
  | nil => simp at hl
  | cons y _ => exact h y (hp y (by simp))

theorem atLeast_zero (P : U → Prop) : AtLeast 0 P := ⟨[], by simp, rfl, by simp⟩

/-- Soundness of the syntactic rules of ⊥-locality. -/
theorem locality_sound (S : Nat → Bool) (i : Interp U) :
    ∀ (c : Concept) (x : U), (notBot S c = false → ¬ eval (mask S i) c x) ∧
      (notTop S c = false → eval (mask S i) c x)
  | .atom n, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBot] at h; simp [eval, mask, h]
      · simp [notTop] at h
  | .top, x => by simp [notBot, notTop, eval]
  | .bot, x => by simp [notBot, notTop, eval]
  | .not c, x => by
      have ih := locality_sound S i c x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot] at h; simp only [eval, not_not]; exact ih.2 h
      · simp only [notTop] at h; simp only [eval]; exact ih.1 h
  | .and c d, x => by
      have ic := locality_sound S i c x
      have id := locality_sound S i d x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot, Bool.and_eq_false_iff] at h
        simp only [eval, not_and_or]
        rcases h with h | h
        · exact Or.inl (ic.1 h)
        · exact Or.inr (id.1 h)
      · simp only [notTop, Bool.or_eq_false_iff] at h
        exact ⟨ic.2 h.1, id.2 h.2⟩
  | .or c d, x => by
      have ic := locality_sound S i c x
      have id := locality_sound S i d x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot, Bool.or_eq_false_iff] at h
        simp only [eval, not_or]
        exact ⟨ic.1 h.1, id.1 h.2⟩
      · simp only [notTop, Bool.and_eq_false_iff] at h
        rcases h with h | h
        · exact Or.inl (ic.2 h)
        · exact Or.inr (id.2 h)
  | .some r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot, Bool.and_eq_false_iff] at h
        rintro ⟨y, hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (locality_sound S i c y).1 h hc
      · simp [notTop] at h
  | .all r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBot] at h
      · simp only [notTop, Bool.and_eq_false_iff] at h
        intro y hr
        rcases h with h | h
        · exact absurd hr (role_mask_empty h i x y)
        · exact (locality_sound S i c y).2 h
  | .atLeast 0 r c, x => by
      refine ⟨fun h => ?_, fun _ => atLeast_zero _⟩
      simp [notBot] at h
  | .atLeast (k + 1) r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot, Bool.and_eq_false_iff] at h
        apply atLeast_succ_empty
        rintro y ⟨hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (locality_sound S i c y).1 h hc
      · simp [notTop] at h
  | .atMost k r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBot] at h
      · simp only [notTop, Bool.and_eq_false_iff] at h
        apply atLeast_succ_empty
        rintro y ⟨hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (locality_sound S i c y).1 h hc
  | .nominal n, x => by simp [notBot, notTop]
  | .self r, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBot] at h
        exact role_mask_empty h i x x
      · simp [notTop] at h

/-! ### Signatures and agreement inside the signature -/

def RoleIn (S : Nat → Bool) : Role → Prop
  | .name n => S n = true
  | .inv n => S n = true
  | .top => True
  | .bot => True

def InSig (S : Nat → Bool) : Concept → Prop
  | .atom n => S n = true
  | .top => True
  | .bot => True
  | .not c => InSig S c
  | .and c d => InSig S c ∧ InSig S d
  | .or c d => InSig S c ∧ InSig S d
  | .some r c => RoleIn S r ∧ InSig S c
  | .all r c => RoleIn S r ∧ InSig S c
  | .atLeast _ r c => RoleIn S r ∧ InSig S c
  | .atMost _ r c => RoleIn S r ∧ InSig S c
  | .nominal _ => True
  | .self r => RoleIn S r

theorem role_mask_agree {S : Nat → Bool} {r : Role} (h : RoleIn S r) (i : Interp U) (x y : U) :
    (mask S i).role r x y ↔ i.role r x y := by
  cases r with
  | name n => simp [RoleIn] at h; simp [Interp.role, mask, h]
  | inv n => simp [RoleIn] at h; simp [Interp.role, mask, h]
  | top => simp [Interp.role]
  | bot => simp [Interp.role]

theorem eval_mask_agree (S : Nat → Bool) (i : Interp U) :
    ∀ (c : Concept), InSig S c → ∀ x, (eval (mask S i) c x ↔ eval i c x)
  | .atom n, h, x => by simp [InSig] at h; simp [eval, mask, h]
  | .top, _, x => Iff.rfl
  | .bot, _, x => Iff.rfl
  | .not c, h, x => by
      simp only [eval]; rw [eval_mask_agree S i c h x]
  | .and c d, h, x => by
      simp only [eval]; rw [eval_mask_agree S i c h.1 x, eval_mask_agree S i d h.2 x]
  | .or c d, h, x => by
      simp only [eval]; rw [eval_mask_agree S i c h.1 x, eval_mask_agree S i d h.2 x]
  | .some r c, h, x => by
      simp only [eval]
      exact exists_congr fun y => by
        rw [role_mask_agree h.1 i x y, eval_mask_agree S i c h.2 y]
  | .all r c, h, x => by
      simp only [eval]
      exact forall_congr' fun y => by
        rw [role_mask_agree h.1 i x y, eval_mask_agree S i c h.2 y]
  | .atLeast k r c, h, x => by
      simp only [eval, AtLeast]
      exact exists_congr fun l => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => forall_congr' fun _ => by
          rw [role_mask_agree h.1 i x y, eval_mask_agree S i c h.2 y]))
  | .atMost k r c, h, x => by
      simp only [eval, AtLeast]
      exact not_congr (exists_congr fun l => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => forall_congr' fun _ => by
          rw [role_mask_agree h.1 i x y, eval_mask_agree S i c h.2 y])))
  | .nominal n, _, x => by simp [eval, mask]
  | .self r, h, x => by
      simp only [eval]; exact role_mask_agree h i x x

/-! ### Axioms -/

/-- Composition of a role chain. -/
def chain (i : Interp U) : List Role → U → U → Prop
  | [] => fun x y => x = y
  | r :: rs => fun x z => ∃ y, i.role r x y ∧ chain i rs y z

inductive Axiom where
  | sub : Concept → Concept → Axiom
  /-- A non-empty role chain included in a role. -/
  | roleSub : Role → List Role → Role → Axiom
  | trans : Role → Axiom
  | func : Role → Axiom
  | symm : Role → Axiom
  | asymm : Role → Axiom
  | irrefl : Role → Axiom
  | refl : Role → Axiom
  | disjointRoles : Role → Role → Axiom
  | classAssert : Concept → Nat → Axiom
  | roleAssert : Role → Nat → Nat → Axiom
  | negRoleAssert : Role → Nat → Nat → Axiom
  | same : Nat → Nat → Axiom
  | diff : Nat → Nat → Axiom

def sat (i : Interp U) : Axiom → Prop
  | .sub c d => ∀ x, eval i c x → eval i d x
  | .roleSub r rs s => ∀ x y, chain i (r :: rs) x y → i.role s x y
  | .trans r => ∀ x y z, i.role r x y → i.role r y z → i.role r x z
  | .func r => ∀ x y z, i.role r x y → i.role r x z → y = z
  | .symm r => ∀ x y, i.role r x y → i.role r y x
  | .asymm r => ∀ x y, i.role r x y → ¬ i.role r y x
  | .irrefl r => ∀ x, ¬ i.role r x x
  | .refl r => ∀ x, i.role r x x
  | .disjointRoles r s => ∀ x y, i.role r x y → ¬ i.role s x y
  | .classAssert c a => eval i c (i.ind a)
  | .roleAssert r a b => i.role r (i.ind a) (i.ind b)
  | .negRoleAssert r a b => ¬ i.role r (i.ind a) (i.ind b)
  | .same a b => i.ind a = i.ind b
  | .diff a b => i.ind a ≠ i.ind b

/-- The Rust compiler's non-locality condition (up to weakening). -/
def nonLocal (S : Nat → Bool) : Axiom → Bool
  | .sub c d => notBot S c && notTop S d
  | .roleSub r rs s => (roleIn S r && rs.all (roleIn S)) &&
      (match s with | .top => false | _ => true)
  | .trans r => roleIn S r
  | .func r => roleIn S r
  | .symm r => roleIn S r
  | .asymm r => roleIn S r
  | .irrefl r => roleIn S r
  | .refl _ => true
  | .disjointRoles r s => roleIn S r && roleIn S s
  | .classAssert c _ => notTop S c
  | .roleAssert _ _ _ => true
  | .negRoleAssert r _ _ => roleIn S r
  | .same _ _ => true
  | .diff _ _ => true

theorem chain_mask_empty {S : Nat → Bool} (i : Interp U) :
    ∀ (rs : List Role), rs.all (roleIn S) = false → ∀ x y, ¬ chain (mask S i) rs x y
  | [], h, _, _ => by simp at h
  | r :: rs, h, x, z => by
      rintro ⟨y, hr, hc⟩
      simp only [List.all_cons, Bool.and_eq_false_iff] at h
      rcases h with h | h
      · exact role_mask_empty h i x y hr
      · exact chain_mask_empty i rs h y z hc

/-- Every axiom whose non-locality condition fails is ⊥-local. -/
theorem axiom_local_sound (S : Nat → Bool) (i : Interp U) :
    ∀ a : Axiom, nonLocal S a = false → sat (mask S i) a
  | .sub c d, h => by
      simp only [nonLocal, Bool.and_eq_false_iff] at h
      intro x hc
      rcases h with h | h
      · exact absurd hc ((locality_sound S i c x).1 h)
      · exact (locality_sound S i d x).2 h
  | .roleSub r rs s, h => by
      intro x y hc
      simp only [nonLocal, Bool.and_eq_false_iff] at h
      rcases h with (h | h) | h
      · exact absurd hc (chain_mask_empty i (r :: rs) (by simp [h]) x y)
      · exact absurd hc (chain_mask_empty i (r :: rs) (by simp [h]) x y)
      · cases s with
        | top => simp [Interp.role]
        | name _ => simp at h
        | inv _ => simp at h
        | bot => simp at h
  | .trans r, h => fun x y _ hr _ => absurd hr (role_mask_empty h i x y)
  | .func r, h => fun x y _ hr _ => absurd hr (role_mask_empty h i x y)
  | .symm r, h => fun x y hr => absurd hr (role_mask_empty h i x y)
  | .asymm r, h => fun x y hr _ => role_mask_empty h i x y hr
  | .irrefl r, h => fun x => role_mask_empty h i x x
  | .refl r, h => by simp [nonLocal] at h
  | .disjointRoles r s, h => by
      simp only [nonLocal, Bool.and_eq_false_iff] at h
      intro x y hr hs
      rcases h with h | h
      · exact role_mask_empty h i x y hr
      · exact role_mask_empty h i x y hs
  | .classAssert c a, h => (locality_sound S i c _).2 h
  | .roleAssert _ _ _, h => by simp [nonLocal] at h
  | .negRoleAssert r a b, h => role_mask_empty h i _ _
  | .same _ _, h => by simp [nonLocal] at h
  | .diff _ _, h => by simp [nonLocal] at h

def AxInSig (S : Nat → Bool) : Axiom → Prop
  | .sub c d => InSig S c ∧ InSig S d
  | .roleSub r rs s => RoleIn S r ∧ (∀ t ∈ rs, RoleIn S t) ∧ RoleIn S s
  | .trans r | .func r | .symm r | .asymm r | .irrefl r | .refl r => RoleIn S r
  | .disjointRoles r s => RoleIn S r ∧ RoleIn S s
  | .classAssert c _ => InSig S c
  | .roleAssert r _ _ | .negRoleAssert r _ _ => RoleIn S r
  | .same _ _ | .diff _ _ => True

theorem chain_mask_agree {S : Nat → Bool} (i : Interp U) :
    ∀ (rs : List Role), (∀ t ∈ rs, RoleIn S t) → ∀ x y,
      (chain (mask S i) rs x y ↔ chain i rs x y)
  | [], _, x, y => Iff.rfl
  | r :: rs, h, x, z => by
      simp only [chain]
      exact exists_congr fun y => by
        rw [role_mask_agree (h r (by simp)) i x y,
          chain_mask_agree i rs (fun t ht => h t (by simp [ht])) y z]

theorem sat_mask_agree (S : Nat → Bool) (i : Interp U) :
    ∀ a : Axiom, AxInSig S a → (sat (mask S i) a ↔ sat i a)
  | .sub c d, h => by
      simp only [sat]
      exact forall_congr' fun x => by
        rw [eval_mask_agree S i c h.1 x, eval_mask_agree S i d h.2 x]
  | .roleSub r rs s, h => by
      have hc := chain_mask_agree (S := S) i (r :: rs) (by
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact h.1
        · exact h.2.1 t ht)
      simp only [sat]
      exact forall_congr' fun x => forall_congr' fun y => by
        rw [hc x y, role_mask_agree h.2.2 i x y]
  | .trans r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .func r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .symm r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .asymm r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .irrefl r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .refl r, h => by
      simp only [sat]
      simp only [role_mask_agree h i]
  | .disjointRoles r s, h => by
      simp only [sat]
      simp only [role_mask_agree h.1 i, role_mask_agree h.2 i]
  | .classAssert c a, h => by
      simp only [sat]
      exact eval_mask_agree S i c h _
  | .roleAssert r a b, h => by
      simp only [sat]
      exact role_mask_agree h i _ _
  | .negRoleAssert r a b, h => by
      simp only [sat]
      exact not_congr (role_mask_agree h i _ _)
  | .same a b, _ => Iff.rfl
  | .diff a b, _ => Iff.rfl

/-- Subsumption queries `C ⊑ D`; unsatisfiability is `A ⊑ ⊥`. -/
def holds (i : Interp U) (q : Concept × Concept) : Prop :=
  ∀ x, eval i q.1 x → eval i q.2 x

/-! ### Occurrences and the concrete masked semantics -/

def OccursR (n : Nat) : Role → Prop
  | .name m => n = m
  | .inv m => n = m
  | .top => False
  | .bot => False

def OccursC (n : Nat) : Concept → Prop
  | .atom m => n = m
  | .top => False
  | .bot => False
  | .not c => OccursC n c
  | .and c d => OccursC n c ∨ OccursC n d
  | .or c d => OccursC n c ∨ OccursC n d
  | .some r c => OccursR n r ∨ OccursC n c
  | .all r c => OccursR n r ∨ OccursC n c
  | .atLeast _ r c => OccursR n r ∨ OccursC n c
  | .atMost _ r c => OccursR n r ∨ OccursC n c
  | .nominal _ => False
  | .self r => OccursR n r

def OccursA (n : Nat) : Axiom → Prop
  | .sub c d => OccursC n c ∨ OccursC n d
  | .roleSub r rs s => OccursR n r ∨ (∃ t ∈ rs, OccursR n t) ∨ OccursR n s
  | .trans r | .func r | .symm r | .asymm r | .irrefl r | .refl r => OccursR n r
  | .disjointRoles r s => OccursR n r ∨ OccursR n s
  | .classAssert c _ => OccursC n c
  | .roleAssert r _ _ | .negRoleAssert r _ _ => OccursR n r
  | .same _ _ | .diff _ _ => False

theorem rolein_of_occurs (B : Nat → Bool) (r : Role) (h : ∀ n, OccursR n r → B n = true) :
    RoleIn B r := by
  cases r with
  | name m => exact h m rfl
  | inv m => exact h m rfl
  | top => trivial
  | bot => trivial

theorem insig_of_occurs (B : Nat → Bool) :
    ∀ c : Concept, (∀ n, OccursC n c → B n = true) → InSig B c
  | .atom m, h => h m rfl
  | .top, _ => trivial
  | .bot, _ => trivial
  | .not c, h => insig_of_occurs B c h
  | .and c d, h => ⟨insig_of_occurs B c fun n hn => h n (Or.inl hn),
      insig_of_occurs B d fun n hn => h n (Or.inr hn)⟩
  | .or c d, h => ⟨insig_of_occurs B c fun n hn => h n (Or.inl hn),
      insig_of_occurs B d fun n hn => h n (Or.inr hn)⟩
  | .some r c, h => ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
      insig_of_occurs B c fun n hn => h n (Or.inr hn)⟩
  | .all r c, h => ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
      insig_of_occurs B c fun n hn => h n (Or.inr hn)⟩
  | .atLeast _ r c, h => ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
      insig_of_occurs B c fun n hn => h n (Or.inr hn)⟩
  | .atMost _ r c, h => ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
      insig_of_occurs B c fun n hn => h n (Or.inr hn)⟩
  | .nominal _, _ => trivial
  | .self r, h => rolein_of_occurs B r h

theorem axinsig_of_occurs (B : Nat → Bool) (a : Axiom) (h : ∀ n, OccursA n a → B n = true) :
    AxInSig B a := by
  cases a with
  | sub c d => exact ⟨insig_of_occurs B c fun n hn => h n (Or.inl hn),
      insig_of_occurs B d fun n hn => h n (Or.inr hn)⟩
  | roleSub r rs s =>
      exact ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
        fun t ht => rolein_of_occurs B t fun n hn => h n (Or.inr (Or.inl ⟨t, ht, hn⟩)),
        rolein_of_occurs B s fun n hn => h n (Or.inr (Or.inr hn))⟩
  | trans r => exact rolein_of_occurs B r h
  | func r => exact rolein_of_occurs B r h
  | symm r => exact rolein_of_occurs B r h
  | asymm r => exact rolein_of_occurs B r h
  | irrefl r => exact rolein_of_occurs B r h
  | refl r => exact rolein_of_occurs B r h
  | disjointRoles r s => exact ⟨rolein_of_occurs B r fun n hn => h n (Or.inl hn),
      rolein_of_occurs B s fun n hn => h n (Or.inr hn)⟩
  | classAssert c _ => exact insig_of_occurs B c h
  | roleAssert r _ _ => exact rolein_of_occurs B r h
  | negRoleAssert r _ _ => exact rolein_of_occurs B r h
  | same _ _ => trivial
  | diff _ _ => trivial

/-- Interpretations over any domain. -/
def Model := Σ U : Type, Interp U

open Classical in
/-- The Boolean signature of a propositional one. -/
noncomputable def bsig (S : Nat → Prop) : Nat → Bool := fun n => decide (S n)

theorem bsig_true {S : Nat → Prop} {n : Nat} (h : S n) : bsig S n = true := by
  classical
  simp [bsig, h]

/-- The concrete masked semantics of SROIQ subsumption queries. -/
noncomputable def sroiq : MaskedSemantics Axiom (Concept × Concept) Model Nat where
  sat m a := sat m.2 a
  holds m q := holds m.2 q
  mask S m := ⟨m.1, mask (bsig S) m.2⟩
  sigAx a n := OccursA n a
  sigQ q n := OccursC n q.1 ∨ OccursC n q.2
  agree_ax := by
    intro S m a h
    exact sat_mask_agree (bsig S) m.2 a
      (axinsig_of_occurs _ a fun n hn => bsig_true (h n hn))
  agree_q := by
    intro S m q h
    have h1 := eval_mask_agree (bsig S) m.2 q.1
      (insig_of_occurs _ q.1 fun n hn => bsig_true (h n (Or.inl hn)))
    have h2 := eval_mask_agree (bsig S) m.2 q.2
      (insig_of_occurs _ q.2 fun n hn => bsig_true (h n (Or.inr hn)))
    show (∀ x, _ → _) ↔ (∀ x, _ → _)
    exact forall_congr' fun x => by rw [h1 x, h2 x]

/-- The compiled formula decides locality for the concrete semantics. -/
theorem local_of_nonLocal {S : Nat → Prop} {a : Axiom} (h : nonLocal (bsig S) a = false) :
    Local sroiq S a :=
  fun m => axiom_local_sound (bsig S) m.2 a h

/-- A source subset closed under the compiled rules is a module. -/
theorem isModule_of_closed {O M : Axiom → Prop} {S : Nat → Prop}
    (hsub : ∀ a, M a → O a) (hcov : ∀ a, M a → ∀ n, OccursA n a → S n)
    (hclosed : ∀ a, O a → ¬ M a → nonLocal (bsig S) a = false) : IsModule sroiq O M S :=
  ⟨hsub, hcov, fun a ha hna => local_of_nonLocal (hclosed a ha hna)⟩

/-! ## Assertions cannot change TBox subsumptions of a consistent ontology -/

def RoleNoTop : Role → Prop
  | .top => False
  | _ => True

/-- No nominal and no universal role. -/
def Plain : Concept → Prop
  | .atom _ | .top | .bot => True
  | .not c => Plain c
  | .and c d | .or c d => Plain c ∧ Plain d
  | .some r c | .all r c | .atLeast _ r c | .atMost _ r c => RoleNoTop r ∧ Plain c
  | .nominal _ => False
  | .self r => RoleNoTop r

/-- No universal role (nominals allowed). -/
def TopFree : Concept → Prop
  | .atom _ | .top | .bot | .nominal _ => True
  | .not c => TopFree c
  | .and c d | .or c d => TopFree c ∧ TopFree d
  | .some r c | .all r c | .atLeast _ r c | .atMost _ r c => RoleNoTop r ∧ TopFree c
  | .self r => RoleNoTop r

theorem topFree_of_plain : ∀ c : Concept, Plain c → TopFree c
  | .atom _, _ | .top, _ | .bot, _ => trivial
  | .not c, h => topFree_of_plain c h
  | .and c d, h | .or c d, h => ⟨topFree_of_plain c h.1, topFree_of_plain d h.2⟩
  | .some _ c, h | .all _ c, h | .atLeast _ _ c, h | .atMost _ _ c, h =>
      ⟨h.1, topFree_of_plain c h.2⟩
  | .nominal _, h => h.elim
  | .self _, h => h

variable {V : Type u}

/-- Disjoint union: no role edge crosses sides; individuals live on the right. -/
def union (i : Interp U) (j : Interp V) : Interp (U ⊕ V) where
  cls n z := match z with
    | .inl x => i.cls n x
    | .inr y => j.cls n y
  rl n z w := match z, w with
    | .inl x, .inl x' => i.rl n x x'
    | .inr y, .inr y' => j.rl n y y'
    | _, _ => False
  ind n := .inr (j.ind n)

theorem union_role_ll (i : Interp U) (j : Interp V) {r : Role} (hr : RoleNoTop r) (x x' : U) :
    (union i j).role r (.inl x) (.inl x') ↔ i.role r x x' := by
  cases r with
  | name n => rfl
  | inv n => rfl
  | top => exact hr.elim
  | bot => rfl

theorem union_role_lr (i : Interp U) (j : Interp V) {r : Role} (hr : RoleNoTop r) (x : U) (y : V) :
    ¬ (union i j).role r (.inl x) (.inr y) := by
  cases r with
  | name n => exact id
  | inv n => exact id
  | top => exact hr.elim
  | bot => exact id

theorem union_role_rl (i : Interp U) (j : Interp V) {r : Role} (hr : RoleNoTop r) (x : U) (y : V) :
    ¬ (union i j).role r (.inr y) (.inl x) := by
  cases r with
  | name n => exact id
  | inv n => exact id
  | top => exact hr.elim
  | bot => exact id

theorem union_role_rr (i : Interp U) (j : Interp V) {r : Role} (hr : RoleNoTop r) (y y' : V) :
    (union i j).role r (.inr y) (.inr y') ↔ j.role r y y' := by
  cases r with
  | name n => rfl
  | inv n => rfl
  | top => exact hr.elim
  | bot => rfl

theorem list_inl {l : List (U ⊕ V)} (h : ∀ z ∈ l, ∃ x, z = .inl x) :
    ∃ l' : List U, l = l'.map Sum.inl := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons z zs ih =>
      obtain ⟨x, rfl⟩ := h z (by simp)
      obtain ⟨l', hl'⟩ := ih fun w hw => h w (by simp [hw])
      exact ⟨x :: l', by simp [hl']⟩

theorem list_inr {l : List (U ⊕ V)} (h : ∀ z ∈ l, ∃ y, z = .inr y) :
    ∃ l' : List V, l = l'.map Sum.inr := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons z zs ih =>
      obtain ⟨y, rfl⟩ := h z (by simp)
      obtain ⟨l', hl'⟩ := ih fun w hw => h w (by simp [hw])
      exact ⟨y :: l', by simp [hl']⟩

theorem atLeast_inl {k : Nat} {P : U ⊕ V → Prop} {P' : U → Prop}
    (hP : ∀ x, P (.inl x) ↔ P' x) (hR : ∀ y, ¬ P (.inr y)) :
    AtLeast k P ↔ AtLeast k P' := by
  constructor
  · rintro ⟨l, hn, hl, hp⟩
    obtain ⟨l', rfl⟩ := list_inl (l := l) fun z hz => by
      cases z with
      | inl x => exact ⟨x, rfl⟩
      | inr y => exact (hR y (hp _ hz)).elim
    refine ⟨l', hn.of_map _, by simpa using hl, fun y hy => (hP y).mp (hp _ ?_)⟩
    exact List.mem_map_of_mem hy
  · rintro ⟨l', hn, hl, hp⟩
    refine ⟨l'.map Sum.inl, hn.map (fun _ _ h => Sum.inl.inj h), by simpa using hl, ?_⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact (hP y).mpr (hp y hy)

theorem atLeast_inr {k : Nat} {P : U ⊕ V → Prop} {P' : V → Prop}
    (hP : ∀ y, P (.inr y) ↔ P' y) (hL : ∀ x, ¬ P (.inl x)) :
    AtLeast k P ↔ AtLeast k P' := by
  constructor
  · rintro ⟨l, hn, hl, hp⟩
    obtain ⟨l', rfl⟩ := list_inr (l := l) fun z hz => by
      cases z with
      | inl x => exact (hL x (hp _ hz)).elim
      | inr y => exact ⟨y, rfl⟩
    refine ⟨l', hn.of_map _, by simpa using hl, fun y hy => (hP y).mp (hp _ ?_)⟩
    exact List.mem_map_of_mem hy
  · rintro ⟨l', hn, hl, hp⟩
    refine ⟨l'.map Sum.inr, hn.map (fun _ _ h => Sum.inr.inj h), by simpa using hl, ?_⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact (hP y).mpr (hp y hy)

/-- Left elements keep the meaning of nominal- and universal-role-free concepts. -/
theorem eval_union_inl (i : Interp U) (j : Interp V) :
    ∀ c : Concept, Plain c → ∀ x, (eval (union i j) c (.inl x) ↔ eval i c x)
  | .atom n, _, x => Iff.rfl
  | .top, _, x => Iff.rfl
  | .bot, _, x => Iff.rfl
  | .not c, h, x => by simp only [eval]; rw [eval_union_inl i j c h x]
  | .and c d, h, x => by
      simp only [eval]; rw [eval_union_inl i j c h.1 x, eval_union_inl i j d h.2 x]
  | .or c d, h, x => by
      simp only [eval]; rw [eval_union_inl i j c h.1 x, eval_union_inl i j d h.2 x]
  | .some r c, h, x => by
      simp only [eval]
      constructor
      · rintro ⟨z, hr, hc⟩
        cases z with
        | inl x' => exact ⟨x', (union_role_ll i j h.1 x x').mp hr, (eval_union_inl i j c h.2 x').mp hc⟩
        | inr y => exact (union_role_lr i j h.1 x y hr).elim
      · rintro ⟨x', hr, hc⟩
        exact ⟨.inl x', (union_role_ll i j h.1 x x').mpr hr, (eval_union_inl i j c h.2 x').mpr hc⟩
  | .all r c, h, x => by
      simp only [eval]
      constructor
      · intro hall x' hr
        exact (eval_union_inl i j c h.2 x').mp (hall _ ((union_role_ll i j h.1 x x').mpr hr))
      · intro hall z hr
        cases z with
        | inl x' => exact (eval_union_inl i j c h.2 x').mpr (hall x' ((union_role_ll i j h.1 x x').mp hr))
        | inr y => exact (union_role_lr i j h.1 x y hr).elim
  | .atLeast k r c, h, x => by
      simp only [eval]
      exact atLeast_inl (fun x' => by rw [union_role_ll i j h.1 x x', eval_union_inl i j c h.2 x'])
        (fun y hy => union_role_lr i j h.1 x y hy.1)
  | .atMost k r c, h, x => by
      simp only [eval]
      exact not_congr (atLeast_inl
        (fun x' => by rw [union_role_ll i j h.1 x x', eval_union_inl i j c h.2 x'])
        (fun y hy => union_role_lr i j h.1 x y hy.1))
  | .nominal _, h, _ => h.elim
  | .self r, h, x => union_role_ll i j h x x

/-- Right elements keep the meaning of universal-role-free concepts. -/
theorem eval_union_inr (i : Interp U) (j : Interp V) :
    ∀ c : Concept, TopFree c → ∀ y, (eval (union i j) c (.inr y) ↔ eval j c y)
  | .atom n, _, y => Iff.rfl
  | .top, _, y => Iff.rfl
  | .bot, _, y => Iff.rfl
  | .not c, h, y => by simp only [eval]; rw [eval_union_inr i j c h y]
  | .and c d, h, y => by
      simp only [eval]; rw [eval_union_inr i j c h.1 y, eval_union_inr i j d h.2 y]
  | .or c d, h, y => by
      simp only [eval]; rw [eval_union_inr i j c h.1 y, eval_union_inr i j d h.2 y]
  | .some r c, h, y => by
      simp only [eval]
      constructor
      · rintro ⟨z, hr, hc⟩
        cases z with
        | inl x => exact (union_role_rl i j h.1 x y hr).elim
        | inr y' => exact ⟨y', (union_role_rr i j h.1 y y').mp hr, (eval_union_inr i j c h.2 y').mp hc⟩
      · rintro ⟨y', hr, hc⟩
        exact ⟨.inr y', (union_role_rr i j h.1 y y').mpr hr, (eval_union_inr i j c h.2 y').mpr hc⟩
  | .all r c, h, y => by
      simp only [eval]
      constructor
      · intro hall y' hr
        exact (eval_union_inr i j c h.2 y').mp (hall _ ((union_role_rr i j h.1 y y').mpr hr))
      · intro hall z hr
        cases z with
        | inl x => exact (union_role_rl i j h.1 x y hr).elim
        | inr y' => exact (eval_union_inr i j c h.2 y').mpr (hall y' ((union_role_rr i j h.1 y y').mp hr))
  | .atLeast k r c, h, y => by
      simp only [eval]
      exact atLeast_inr (fun y' => by rw [union_role_rr i j h.1 y y', eval_union_inr i j c h.2 y'])
        (fun x hx => union_role_rl i j h.1 x y hx.1)
  | .atMost k r c, h, y => by
      simp only [eval]
      exact not_congr (atLeast_inr
        (fun y' => by rw [union_role_rr i j h.1 y y', eval_union_inr i j c h.2 y'])
        (fun x hx => union_role_rl i j h.1 x y hx.1))
  | .nominal n, _, y => by
      simp only [eval]
      exact ⟨fun h => Sum.inr.inj h, fun h => by rw [h]; rfl⟩
  | .self r, h, y => union_role_rr i j h y y

/-- TBox axioms: nominal- and universal-role-free inclusions and role axioms. -/
def PlainAx : Axiom → Prop
  | .sub c d => Plain c ∧ Plain d
  | .roleSub r rs s => RoleNoTop r ∧ (∀ t ∈ rs, RoleNoTop t) ∧ RoleNoTop s
  | .trans r | .func r | .symm r | .asymm r | .irrefl r | .refl r => RoleNoTop r
  | .disjointRoles r s => RoleNoTop r ∧ RoleNoTop s
  | _ => False

/-- Assertions: universal-role-free statements about named individuals. -/
def AssertionAx : Axiom → Prop
  | .classAssert c _ => TopFree c
  | .roleAssert r _ _ | .negRoleAssert r _ _ => RoleNoTop r
  | .same _ _ | .diff _ _ => True
  | _ => False

theorem chain_union_l (i : Interp U) (j : Interp V) :
    ∀ (rs : List Role), (∀ t ∈ rs, RoleNoTop t) → ∀ x z,
      chain (union i j) rs (.inl x) z → ∃ x', z = .inl x' ∧ chain i rs x x'
  | [], _, x, z, h => ⟨x, h.symm, rfl⟩
  | r :: rs, ht, x, z, ⟨w, hr, hc⟩ => by
      cases w with
      | inl x' =>
          obtain ⟨x'', hz, hc'⟩ := chain_union_l i j rs (fun t h => ht t (by simp [h])) x' z hc
          exact ⟨x'', hz, x', (union_role_ll i j (ht r (by simp)) x x').mp hr, hc'⟩
      | inr y => exact (union_role_lr i j (ht r (by simp)) x y hr).elim

theorem chain_union_r (i : Interp U) (j : Interp V) :
    ∀ (rs : List Role), (∀ t ∈ rs, RoleNoTop t) → ∀ y z,
      chain (union i j) rs (.inr y) z → ∃ y', z = .inr y' ∧ chain j rs y y'
  | [], _, y, z, h => ⟨y, h.symm, rfl⟩
  | r :: rs, ht, y, z, ⟨w, hr, hc⟩ => by
      cases w with
      | inl x => exact (union_role_rl i j (ht r (by simp)) x y hr).elim
      | inr y' =>
          obtain ⟨y'', hz, hc'⟩ := chain_union_r i j rs (fun t h => ht t (by simp [h])) y' z hc
          exact ⟨y'', hz, y', (union_role_rr i j (ht r (by simp)) y y').mp hr, hc'⟩

/-- A role edge of the union stays on one side. -/
theorem union_role_cases (i : Interp U) (j : Interp V) {r : Role} (hr : RoleNoTop r)
    (z w : U ⊕ V) (h : (union i j).role r z w) :
    (∃ x x', z = .inl x ∧ w = .inl x' ∧ i.role r x x') ∨
      (∃ y y', z = .inr y ∧ w = .inr y' ∧ j.role r y y') := by
  cases z with
  | inl x => cases w with
    | inl x' => exact Or.inl ⟨x, x', rfl, rfl, (union_role_ll i j hr x x').mp h⟩
    | inr y => exact (union_role_lr i j hr x y h).elim
  | inr y => cases w with
    | inl x => exact (union_role_rl i j hr x y h).elim
    | inr y' => exact Or.inr ⟨y, y', rfl, rfl, (union_role_rr i j hr y y').mp h⟩

theorem union_sat_plain (i : Interp U) (j : Interp V) :
    ∀ a : Axiom, PlainAx a → sat i a → sat j a → sat (union i j) a
  | .sub c d, h, hi, hj => by
      intro z hz
      cases z with
      | inl x => exact (eval_union_inl i j d h.2 x).mpr (hi x ((eval_union_inl i j c h.1 x).mp hz))
      | inr y =>
          have hc := (eval_union_inr i j c (topFree_of_plain c h.1) y).mp hz
          exact (eval_union_inr i j d (topFree_of_plain d h.2) y).mpr (hj y hc)
  | .roleSub r rs s, h, hi, hj => by
      intro z w hc
      have hall : ∀ t ∈ r :: rs, RoleNoTop t := by
        intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact h.1
        · exact h.2.1 t ht
      cases z with
      | inl x =>
          obtain ⟨x', rfl, hc'⟩ := chain_union_l i j (r :: rs) hall x w hc
          exact (union_role_ll i j h.2.2 x x').mpr (hi x x' hc')
      | inr y =>
          obtain ⟨y', rfl, hc'⟩ := chain_union_r i j (r :: rs) hall y w hc
          exact (union_role_rr i j h.2.2 y y').mpr (hj y y' hc')
  | .trans r, h, hi, hj => by
      intro a b c hab hbc
      rcases union_role_cases i j h a b hab with ⟨x, x', rfl, rfl, h1⟩ | ⟨y, y', rfl, rfl, h1⟩
      · rcases union_role_cases i j h _ c hbc with ⟨u, u', hu, rfl, h2⟩ | ⟨_, _, hu, _, _⟩
        · cases hu; exact (union_role_ll i j h _ _).mpr (hi _ _ _ h1 h2)
        · cases hu
      · rcases union_role_cases i j h _ c hbc with ⟨_, _, hu, _, _⟩ | ⟨u, u', hu, rfl, h2⟩
        · cases hu
        · cases hu; exact (union_role_rr i j h _ _).mpr (hj _ _ _ h1 h2)
  | .func r, h, hi, hj => by
      intro a b c hab hac
      rcases union_role_cases i j h a b hab with ⟨x, x', rfl, rfl, h1⟩ | ⟨y, y', rfl, rfl, h1⟩
      · rcases union_role_cases i j h _ c hac with ⟨u, u', hu, rfl, h2⟩ | ⟨_, _, hu, _, _⟩
        · cases hu; rw [hi _ _ _ h1 h2]
        · cases hu
      · rcases union_role_cases i j h _ c hac with ⟨_, _, hu, _, _⟩ | ⟨u, u', hu, rfl, h2⟩
        · cases hu
        · cases hu; rw [hj _ _ _ h1 h2]
  | .symm r, h, hi, hj => by
      intro a b hab
      rcases union_role_cases i j h a b hab with ⟨x, x', rfl, rfl, h1⟩ | ⟨y, y', rfl, rfl, h1⟩
      · exact (union_role_ll i j h _ _).mpr (hi _ _ h1)
      · exact (union_role_rr i j h _ _).mpr (hj _ _ h1)
  | .asymm r, h, hi, hj => by
      intro a b hab hba
      rcases union_role_cases i j h a b hab with ⟨x, x', rfl, rfl, h1⟩ | ⟨y, y', rfl, rfl, h1⟩
      · exact hi _ _ h1 ((union_role_ll i j h _ _).mp hba)
      · exact hj _ _ h1 ((union_role_rr i j h _ _).mp hba)
  | .irrefl r, h, hi, hj => by
      intro a haa
      cases a with
      | inl x => exact hi x ((union_role_ll i j h x x).mp haa)
      | inr y => exact hj y ((union_role_rr i j h y y).mp haa)
  | .refl r, h, hi, hj => by
      intro a
      cases a with
      | inl x => exact (union_role_ll i j h x x).mpr (hi x)
      | inr y => exact (union_role_rr i j h y y).mpr (hj y)
  | .disjointRoles r s, h, hi, hj => by
      intro a b hr hs
      rcases union_role_cases i j h.1 a b hr with ⟨x, x', rfl, rfl, h1⟩ | ⟨y, y', rfl, rfl, h1⟩
      · exact hi _ _ h1 ((union_role_ll i j h.2 _ _).mp hs)
      · exact hj _ _ h1 ((union_role_rr i j h.2 _ _).mp hs)
  | .classAssert _ _, h, _, _ => h.elim
  | .roleAssert _ _ _, h, _, _ => h.elim
  | .negRoleAssert _ _ _, h, _, _ => h.elim
  | .same _ _, h, _, _ => h.elim
  | .diff _ _, h, _, _ => h.elim

theorem union_sat_assertion (i : Interp U) (j : Interp V) :
    ∀ a : Axiom, AssertionAx a → sat j a → sat (union i j) a
  | .classAssert c n, h, hj => (eval_union_inr i j c h (j.ind n)).mpr hj
  | .roleAssert r a b, h, hj => (union_role_rr i j h _ _).mpr hj
  | .negRoleAssert r a b, h, hj => fun e => hj ((union_role_rr i j h _ _).mp e)
  | .same a b, _, hj => by
      show Sum.inr (j.ind a) = Sum.inr (j.ind b)
      exact congrArg Sum.inr hj
  | .diff a b, _, hj => fun e => hj (Sum.inr.inj e)
  | .sub _ _, h, _ => h.elim
  | .roleSub _ _ _, h, _ => h.elim
  | .trans _, h, _ => h.elim
  | .func _, h, _ => h.elim
  | .symm _, h, _ => h.elim
  | .asymm _, h, _ => h.elim
  | .irrefl _, h, _ => h.elim
  | .refl _, h, _ => h.elim
  | .disjointRoles _ _, h, _ => h.elim

/-- Entailment over interpretations of every domain. -/
def EntailsC (O : Axiom → Prop) (q : Concept × Concept) : Prop :=
  ∀ (W : Type) (i : Interp W), (∀ a, O a → sat i a) → holds i q

/-- For a consistent ontology whose non-assertion axioms mention no individual
and no universal role, the assertions do not change any subsumption between
such concepts: the TBox alone decides it. -/
theorem tbox_entails_iff {O T : Axiom → Prop}
    (hT : ∀ a, T a → O a) (hplain : ∀ a, T a → PlainAx a)
    (hsplit : ∀ a, O a → T a ∨ AssertionAx a)
    (consistent : ∃ (W : Type) (j : Interp W), ∀ a, O a → sat j a)
    {q : Concept × Concept} (hq1 : Plain q.1) (hq2 : Plain q.2) :
    EntailsC O q ↔ EntailsC T q := by
  constructor
  · intro e W i hi x hx
    obtain ⟨W', j, hj⟩ := consistent
    have hk : ∀ a, O a → sat (union i j) a := by
      intro a ha
      rcases hsplit a ha with ht | has
      · exact union_sat_plain i j a (hplain a ht) (hi a ht) (hj a ha)
      · exact union_sat_assertion i j a has (hj a ha)
    have := e (W ⊕ W') (union i j) hk (.inl x) ((eval_union_inl i j q.1 hq1 x).mpr hx)
    exact (eval_union_inl i j q.2 hq2 x).mp this
  · intro e W i hi
    exact e W i fun a ha => hi a (hT a ha)


/-! ## Nominal TBoxes: nominals read as empty on the masked side

The retained session builds its TBox-mode locality index with nominals
(`ObjectOneOf`, `ObjectHasValue`) read as empty. A class whose module is
nominal-free and avoids the removed axioms keeps its row: on the masked left
side of a disjoint union no element is a named individual, so every nominal
is empty there, and the individuals live on the right side in a model of the
complete ontology. Axioms such as `⊤ ⊑ ∃r.{o}` are never local under this
reading, so they are always in the module and no class is unaffected. -/

/-- `eval` with every nominal empty. -/
def evalN (i : Interp U) : Concept → U → Prop
  | .atom n, x => i.cls n x
  | .top, _ => True
  | .bot, _ => False
  | .not c, x => ¬ evalN i c x
  | .and c d, x => evalN i c x ∧ evalN i d x
  | .or c d, x => evalN i c x ∨ evalN i d x
  | .some r c, x => ∃ y, i.role r x y ∧ evalN i c y
  | .all r c, x => ∀ y, i.role r x y → evalN i c y
  | .atLeast k r c, x => AtLeast k (fun y => i.role r x y ∧ evalN i c y)
  | .atMost k r c, x => ¬ AtLeast (k + 1) (fun y => i.role r x y ∧ evalN i c y)
  | .nominal _, _ => False
  | .self r, x => i.role r x x

mutual
/-- `notBot` with nominals provably empty. -/
def notBotN (S : Nat → Bool) : Concept → Bool
  | .atom n => S n
  | .top => true
  | .bot => false
  | .not c => notTopN S c
  | .and c d => notBotN S c && notBotN S d
  | .or c d => notBotN S c || notBotN S d
  | .some r c => roleIn S r && notBotN S c
  | .all _ _ => true
  | .atLeast 0 _ _ => true
  | .atLeast (_ + 1) r c => roleIn S r && notBotN S c
  | .atMost _ _ _ => true
  | .nominal _ => false
  | .self r => roleIn S r

/-- `notTop` with nominals provably empty. -/
def notTopN (S : Nat → Bool) : Concept → Bool
  | .atom _ => true
  | .top => false
  | .bot => true
  | .not c => notBotN S c
  | .and c d => notTopN S c || notTopN S d
  | .or c d => notTopN S c && notTopN S d
  | .some _ _ => true
  | .all r c => roleIn S r && notTopN S c
  | .atLeast 0 _ _ => false
  | .atLeast (_ + 1) _ _ => true
  | .atMost _ r c => roleIn S r && notBotN S c
  | .nominal _ => true
  | .self _ => true
end

/-- Soundness of the nominal-empty locality rules. -/
theorem localityN_sound (S : Nat → Bool) (i : Interp U) :
    ∀ (c : Concept) (x : U), (notBotN S c = false → ¬ evalN (mask S i) c x) ∧
      (notTopN S c = false → evalN (mask S i) c x)
  | .atom n, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBotN] at h; simp [evalN, mask, h]
      · simp [notTopN] at h
  | .top, x => by simp [notBotN, notTopN, evalN]
  | .bot, x => by simp [notBotN, notTopN, evalN]
  | .not c, x => by
      have ih := localityN_sound S i c x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN] at h; simp only [evalN, not_not]; exact ih.2 h
      · simp only [notTopN] at h; simp only [evalN]; exact ih.1 h
  | .and c d, x => by
      have ic := localityN_sound S i c x
      have id := localityN_sound S i d x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN, Bool.and_eq_false_iff] at h
        simp only [evalN, not_and_or]
        rcases h with h | h
        · exact Or.inl (ic.1 h)
        · exact Or.inr (id.1 h)
      · simp only [notTopN, Bool.or_eq_false_iff] at h
        exact ⟨ic.2 h.1, id.2 h.2⟩
  | .or c d, x => by
      have ic := localityN_sound S i c x
      have id := localityN_sound S i d x
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN, Bool.or_eq_false_iff] at h
        simp only [evalN, not_or]
        exact ⟨ic.1 h.1, id.1 h.2⟩
      · simp only [notTopN, Bool.and_eq_false_iff] at h
        rcases h with h | h
        · exact Or.inl (ic.2 h)
        · exact Or.inr (id.2 h)
  | .some r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN, Bool.and_eq_false_iff] at h
        rintro ⟨y, hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (localityN_sound S i c y).1 h hc
      · simp [notTopN] at h
  | .all r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBotN] at h
      · simp only [notTopN, Bool.and_eq_false_iff] at h
        intro y hr
        rcases h with h | h
        · exact absurd hr (role_mask_empty h i x y)
        · exact (localityN_sound S i c y).2 h
  | .atLeast 0 r c, x => by
      refine ⟨fun h => ?_, fun _ => atLeast_zero _⟩
      simp [notBotN] at h
  | .atLeast (k + 1) r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN, Bool.and_eq_false_iff] at h
        apply atLeast_succ_empty
        rintro y ⟨hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (localityN_sound S i c y).1 h hc
      · simp [notTopN] at h
  | .atMost k r c, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [notBotN] at h
      · simp only [notTopN, Bool.and_eq_false_iff] at h
        apply atLeast_succ_empty
        rintro y ⟨hr, hc⟩
        rcases h with h | h
        · exact role_mask_empty h i x y hr
        · exact (localityN_sound S i c y).1 h hc
  | .nominal n, x => by simp [notBotN, notTopN, evalN]
  | .self r, x => by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [notBotN] at h
        exact role_mask_empty h i x x
      · simp [notTopN] at h

/-- Left elements of the union read every nominal as empty. -/
theorem eval_union_inlN (i : Interp U) (j : Interp V) :
    ∀ c : Concept, TopFree c → ∀ x, (eval (union i j) c (.inl x) ↔ evalN i c x)
  | .atom n, _, x => Iff.rfl
  | .top, _, x => Iff.rfl
  | .bot, _, x => Iff.rfl
  | .not c, h, x => by simp only [eval, evalN]; rw [eval_union_inlN i j c h x]
  | .and c d, h, x => by
      simp only [eval, evalN]; rw [eval_union_inlN i j c h.1 x, eval_union_inlN i j d h.2 x]
  | .or c d, h, x => by
      simp only [eval, evalN]; rw [eval_union_inlN i j c h.1 x, eval_union_inlN i j d h.2 x]
  | .some r c, h, x => by
      simp only [eval, evalN]
      constructor
      · rintro ⟨z, hr, hc⟩
        cases z with
        | inl x' => exact ⟨x', (union_role_ll i j h.1 x x').mp hr, (eval_union_inlN i j c h.2 x').mp hc⟩
        | inr y => exact (union_role_lr i j h.1 x y hr).elim
      · rintro ⟨x', hr, hc⟩
        exact ⟨.inl x', (union_role_ll i j h.1 x x').mpr hr, (eval_union_inlN i j c h.2 x').mpr hc⟩
  | .all r c, h, x => by
      simp only [eval, evalN]
      constructor
      · intro hall x' hr
        exact (eval_union_inlN i j c h.2 x').mp (hall _ ((union_role_ll i j h.1 x x').mpr hr))
      · intro hall z hr
        cases z with
        | inl x' => exact (eval_union_inlN i j c h.2 x').mpr (hall x' ((union_role_ll i j h.1 x x').mp hr))
        | inr y => exact (union_role_lr i j h.1 x y hr).elim
  | .atLeast k r c, h, x => by
      simp only [eval, evalN]
      exact atLeast_inl (fun x' => by rw [union_role_ll i j h.1 x x', eval_union_inlN i j c h.2 x'])
        (fun y hy => union_role_lr i j h.1 x y hy.1)
  | .atMost k r c, h, x => by
      simp only [eval, evalN]
      exact not_congr (atLeast_inl
        (fun x' => by rw [union_role_ll i j h.1 x x', eval_union_inlN i j c h.2 x'])
        (fun y hy => union_role_lr i j h.1 x y hy.1))
  | .nominal n, _, x => by
      show Sum.inl x = Sum.inr (j.ind n) ↔ False
      constructor
      · intro h
        cases h
      · exact False.elim
  | .self r, h, x => union_role_ll i j h x x

/-- Nominal-free concepts do not see the difference. -/
theorem evalN_plain (i : Interp U) :
    ∀ c : Concept, Plain c → ∀ x, (evalN i c x ↔ eval i c x)
  | .atom n, _, x => Iff.rfl
  | .top, _, x => Iff.rfl
  | .bot, _, x => Iff.rfl
  | .not c, h, x => by simp only [eval, evalN]; rw [evalN_plain i c h x]
  | .and c d, h, x => by
      simp only [eval, evalN]; rw [evalN_plain i c h.1 x, evalN_plain i d h.2 x]
  | .or c d, h, x => by
      simp only [eval, evalN]; rw [evalN_plain i c h.1 x, evalN_plain i d h.2 x]
  | .some r c, h, x => by
      simp only [eval, evalN]
      exact exists_congr fun y => by rw [evalN_plain i c h.2 y]
  | .all r c, h, x => by
      simp only [eval, evalN]
      exact forall_congr' fun y => by rw [evalN_plain i c h.2 y]
  | .atLeast k r c, h, x => by
      simp only [eval, evalN, AtLeast]
      exact exists_congr fun l => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => forall_congr' fun _ => by rw [evalN_plain i c h.2 y]))
  | .atMost k r c, h, x => by
      simp only [eval, evalN, AtLeast]
      exact not_congr (exists_congr fun l => and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun y => forall_congr' fun _ => by rw [evalN_plain i c h.2 y])))
  | .nominal _, h, _ => h.elim
  | .self r, _, x => Iff.rfl

/-- The Rust compiler's TBox-mode non-locality condition (nominals empty). -/
def nonLocalN (S : Nat → Bool) : Axiom → Bool
  | .sub c d => notBotN S c && notTopN S d
  | a => nonLocal S a

/-- TBox axioms that may mention nominals but not the universal role. -/
def TBoxAx : Axiom → Prop
  | .sub c d => TopFree c ∧ TopFree d
  | .roleSub r rs s => RoleNoTop r ∧ (∀ t ∈ rs, RoleNoTop t) ∧ RoleNoTop s
  | .trans r | .func r | .symm r | .asymm r | .irrefl r | .refl r => RoleNoTop r
  | .disjointRoles r s => RoleNoTop r ∧ RoleNoTop s
  | _ => False

/-- A TBox axiom outside the module holds in the union of a masked
interpretation (left, no individuals) and any model of it (right). -/
theorem union_sat_localN (S : Nat → Bool) (i : Interp U) (j : Interp V) :
    ∀ a : Axiom, TBoxAx a → nonLocalN S a = false → sat j a → sat (union (mask S i) j) a
  | .sub c d, h, hl, hj => by
      intro z hz
      cases z with
      | inl x =>
          have hc := (eval_union_inlN (mask S i) j c h.1 x).mp hz
          simp only [nonLocalN, Bool.and_eq_false_iff] at hl
          rcases hl with hl | hl
          · exact absurd hc ((localityN_sound S i c x).1 hl)
          · exact (eval_union_inlN (mask S i) j d h.2 x).mpr ((localityN_sound S i d x).2 hl)
      | inr y =>
          exact (eval_union_inr (mask S i) j d h.2 y).mpr
            (hj y ((eval_union_inr (mask S i) j c h.1 y).mp hz))
  | .roleSub r rs s, h, hl, hj =>
      union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .trans r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .func r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .symm r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .asymm r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .irrefl r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .refl r, h, hl, hj => union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .disjointRoles r s, h, hl, hj =>
      union_sat_plain (mask S i) j _ h (axiom_local_sound S i _ hl) hj
  | .classAssert _ _, h, _, _ => h.elim
  | .roleAssert _ _ _, h, _, _ => h.elim
  | .negRoleAssert _ _ _, h, _, _ => h.elim
  | .same _ _, h, _, _ => h.elim
  | .diff _ _, h, _, _ => h.elim

/-- Hypotheses of nominal-TBox module reuse: `M` is a nominal-free,
universal-role-free subset of `O` over the signature `S`; every other axiom
of `O` is an assertion or a TBox axiom that is local under the nominal-empty
reading; and `O` is consistent. -/
structure NominalModule (O M : Axiom → Prop) (S : Nat → Prop) : Prop where
  sub : ∀ a, M a → O a
  plain : ∀ a, M a → PlainAx a
  cov : ∀ a, M a → ∀ n, OccursA n a → S n
  rest : ∀ a, O a → ¬ M a → AssertionAx a ∨ (TBoxAx a ∧ nonLocalN (bsig S) a = false)
  consistent : ∃ (W : Type) (j : Interp W), ∀ a, O a → sat j a

/-- Every model of the module, masked to its signature and joined with a model
of `O`, is a model of `O`. -/
theorem nominal_union_models {O M : Axiom → Prop} {S : Nat → Prop}
    (hm : NominalModule O M S) {W W' : Type} (i : Interp W) (hi : ∀ a, M a → sat i a)
    (j : Interp W') (hj : ∀ a, O a → sat j a) :
    ∀ a, O a → sat (union (mask (bsig S) i) j) a := by
  intro a ha
  by_cases hM : M a
  · have hmask : sat (mask (bsig S) i) a :=
      (sat_mask_agree (bsig S) i a
        (axinsig_of_occurs _ a fun n hn => bsig_true (hm.cov a hM n hn))).mpr (hi a hM)
    exact union_sat_plain _ j a (hm.plain a hM) hmask (hj a ha)
  · rcases hm.rest a ha hM with has | ⟨ht, hl⟩
    · exact union_sat_assertion _ j a has (hj a ha)
    · exact union_sat_localN (bsig S) i j a ht hl (hj a ha)

/-- A nominal-free module decides every nominal-free query over its signature. -/
theorem nominal_module_entails_iff {O M : Axiom → Prop} {S : Nat → Prop}
    (hm : NominalModule O M S) {q : Concept × Concept}
    (hq1 : Plain q.1) (hq2 : Plain q.2)
    (hs1 : ∀ n, OccursC n q.1 → S n) (hs2 : ∀ n, OccursC n q.2 → S n) :
    EntailsC O q ↔ EntailsC M q := by
  constructor
  · intro e W i hi x hx
    obtain ⟨W', j, hj⟩ := hm.consistent
    have hk := nominal_union_models hm i hi j hj
    have a1 := eval_mask_agree (bsig S) i q.1
      (insig_of_occurs _ q.1 fun n hn => bsig_true (hs1 n hn)) x
    have a2 := eval_mask_agree (bsig S) i q.2
      (insig_of_occurs _ q.2 fun n hn => bsig_true (hs2 n hn)) x
    have := e (W ⊕ W') _ hk (.inl x)
      ((eval_union_inl _ j q.1 hq1 x).mpr (a1.mpr hx))
    exact a2.mp ((eval_union_inl _ j q.2 hq2 x).mp this)
  · intro e W i hi
    exact e W i fun a ha => hi a (hm.sub a ha)

/-- A named superclass outside the module signature is entailed only by an
unsatisfiable subject. -/
theorem nominal_module_outside {O M : Axiom → Prop} {S : Nat → Prop}
    (hm : NominalModule O M S) {c : Concept} (hc : Plain c) (hs : ∀ n, OccursC n c → S n)
    {b : Nat} (hb : ¬ S b) (e : EntailsC O (c, .atom b)) : EntailsC O (c, .bot) := by
  apply (nominal_module_entails_iff hm (q := (c, .bot)) hc trivial hs (fun _ h => h.elim)).mpr
  intro W i hi x hx
  obtain ⟨W', j, hj⟩ := hm.consistent
  have hk := nominal_union_models hm i hi j hj
  have a1 := eval_mask_agree (bsig S) i c (insig_of_occurs _ c fun n hn => bsig_true (hs n hn)) x
  have := e (W ⊕ W') _ hk (.inl x) ((eval_union_inl _ j c hc x).mpr (a1.mpr hx))
  have hb' : bsig S b = false := by
    classical
    simp [bsig, hb]
  simp [eval, union, mask, hb'] at this

/-- Deletion: a nominal module of the base `O` that the deletion keeps is a
nominal module of the revision `O'`. -/
theorem nominal_module_deletion {O O' M : Axiom → Prop} {S : Nat → Prop}
    (hm : NominalModule O M S) (hsub : ∀ a, O' a → O a) (hkeep : ∀ a, M a → O' a) :
    NominalModule O' M S where
  sub := hkeep
  plain := hm.plain
  cov := hm.cov
  rest := fun a ha hM => hm.rest a (hsub a ha) hM
  consistent := by
    obtain ⟨W, j, hj⟩ := hm.consistent
    exact ⟨W, j, fun a ha => hj a (hsub a ha)⟩

/-- The retained row is exact: base and revision agree on every nominal-free
query over the module signature. -/
theorem nominal_unaffected_query {O O' M : Axiom → Prop} {S : Nat → Prop}
    (hm : NominalModule O M S) (hsub : ∀ a, O' a → O a) (hkeep : ∀ a, M a → O' a)
    {q : Concept × Concept} (hq1 : Plain q.1) (hq2 : Plain q.2)
    (hs1 : ∀ n, OccursC n q.1 → S n) (hs2 : ∀ n, OccursC n q.2 → S n) :
    EntailsC O q ↔ EntailsC O' q :=
  (nominal_module_entails_iff hm hq1 hq2 hs1 hs2).trans
    (nominal_module_entails_iff (nominal_module_deletion hm hsub hkeep) hq1 hq2 hs1 hs2).symm


/-! ## Told proofs: rows kept under deletion without reclassification

The retained session keeps the row of a satisfiable subject whose every
published superclass has a syntactic proof in the revision
(`source_locality::ToldProofs`): told inclusions, conjunction elimination and
introduction, disjunction introduction, transitivity. Every rule is sound, and
deletion cannot add consequences, so the row is exact. -/

inductive Told (O : Axiom → Prop) : Concept → Concept → Prop
  | refl (c : Concept) : Told O c c
  | ax {c d : Concept} : O (.sub c d) → Told O c d
  | trans {c d e : Concept} : Told O c d → Told O d e → Told O c e
  | andIntro {c d e : Concept} : Told O c d → Told O c e → Told O c (.and d e)
  | andElimL {c d e : Concept} : Told O c (.and d e) → Told O c d
  | andElimR {c d e : Concept} : Told O c (.and d e) → Told O c e
  | orIntroL {c d e : Concept} : Told O c d → Told O c (.or d e)
  | orIntroR {c d e : Concept} : Told O c e → Told O c (.or d e)
  | top (c : Concept) : Told O c .top

theorem told_sound {O : Axiom → Prop} {c d : Concept} (h : Told O c d) :
    EntailsC O (c, d) := by
  induction h with
  | refl c => intro W i _ x hx; exact hx
  | ax hax => intro W i hi x hx; exact hi _ hax x hx
  | trans _ _ ih1 ih2 => intro W i hi x hx; exact ih2 W i hi x (ih1 W i hi x hx)
  | andIntro _ _ ih1 ih2 => intro W i hi x hx; exact ⟨ih1 W i hi x hx, ih2 W i hi x hx⟩
  | andElimL _ ih => intro W i hi x hx; exact (ih W i hi x hx).1
  | andElimR _ ih => intro W i hi x hx; exact (ih W i hi x hx).2
  | orIntroL _ ih => intro W i hi x hx; exact Or.inl (ih W i hi x hx)
  | orIntroR _ ih => intro W i hi x hx; exact Or.inr (ih W i hi x hx)
  | top c => intro W i _ x _; trivial

theorem entailsC_mono {O O' : Axiom → Prop} (hsub : ∀ a, O' a → O a) {q : Concept × Concept}
    (h : EntailsC O' q) : EntailsC O q :=
  fun W i hi => h W i fun a ha => hi a (hsub a ha)

/-- A row `R` of subject `a` that is exact for the base `O` and told in the
deletion `O' ⊆ O` is exact for `O'` (for every query concept `b`). -/
theorem told_row_exact {O O' : Axiom → Prop} (hsub : ∀ a, O' a → O a)
    {a : Concept} {R : Concept → Prop}
    (hrow : ∀ b, EntailsC O (a, b) ↔ R b) (htold : ∀ b, R b → Told O' a b) :
    ∀ b, EntailsC O' (a, b) ↔ R b :=
  fun b => ⟨fun h => (hrow b).mp (entailsC_mono hsub h), fun h => told_sound (htold b h)⟩

#print axioms module_entails
#print axioms unaffected_query
#print axioms sandwich_query
#print axioms deletion_no_new_consequence
#print axioms inconsistent_superset
#print axioms module_inconsistent
#print axioms merged_publication_exact
#print axioms locality_sound
#print axioms axiom_local_sound
#print axioms eval_mask_agree
#print axioms sat_mask_agree
#print axioms local_of_nonLocal
#print axioms isModule_of_closed
#print axioms tbox_entails_iff
#print axioms localityN_sound
#print axioms nominal_module_entails_iff
#print axioms nominal_module_outside
#print axioms nominal_unaffected_query
#print axioms told_sound
#print axioms told_row_exact

end ContextCalculus.IncrementalModuleReuse
