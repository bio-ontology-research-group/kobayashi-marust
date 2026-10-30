import Lean

/-!
# Inert object sorts in the rule-consistency worker input

`engine/src/orchestrate/inert_sorts.rs` (docs/NOMINALS-CB.md section 6,
"Inert object sorts in the rule checker") rewrites the sorted clause set
before the rule-consistency worker reads it. For every definer `Q` of a
released set `P` it

* removes the concept sort clause `Q(x) ∧ D(x) → ⊥`, and
* drops the data-sort disjunct `D(t)` from every clause head that also
  carries `Q(t)` for some `Q ∈ P`.

This module formalises the clause language of that worker input (first-order
clauses over unary concepts, binary roles, equality, individual constants and
unary Skolem functions), the release transformation exactly as the Rust pass
computes it, and the guard conditions (B) and (H) of the module documentation
as an executable Boolean check. The capstone
`release_equisatisfiable` proves that, when the check accepts, the original
clause set and the released one are satisfiable together with any side
theory that reads only the reserved concept names; in particular they have
the same consistency verdict, in both directions.

The released set `P` and every guard are untrusted: the checker recomputes
the guard tables from the original clauses, and the theorem has no premise
about how `P` was found.
-/

namespace ContextCalculus.RulesInertSort

open Lean

/-! ## Clause language -/

/-- Terms of the worker input. `ind` covers named individuals and auxiliary
constants (`JTerm::Ind`, `JTerm::Aux`), `app` a unary Skolem function. -/
inductive Term where
  | var (index : Nat)
  | ind (index : Nat)
  | app (function : Nat) (arg : Term)
deriving DecidableEq, Repr, FromJson, ToJson

inductive Atom where
  | concept (concept : Nat) (term : Term)
  | role (role : Nat) (source target : Term)
  | eq (left right : Term)
deriving DecidableEq, Repr, FromJson, ToJson

/-- `body → head`: a conjunction of atoms implies a disjunction of atoms. -/
structure Clause where
  body : List Atom
  head : List Atom
deriving DecidableEq, Repr, FromJson, ToJson

/-- First-order interpretation over a domain `α`. -/
structure Interp (α : Type) where
  concept : Nat → α → Prop
  role : Nat → α → α → Prop
  ind : Nat → α
  app : Nat → α → α

def Term.eval (I : Interp α) (v : Nat → α) : Term → α
  | .var index => v index
  | .ind index => I.ind index
  | .app function arg => I.app function (arg.eval I v)

def Atom.Holds (I : Interp α) (v : Nat → α) : Atom → Prop
  | .concept c t => I.concept c (t.eval I v)
  | .role r s t => I.role r (s.eval I v) (t.eval I v)
  | .eq l r => l.eval I v = r.eval I v

def Clause.Holds (I : Interp α) (clause : Clause) : Prop :=
  ∀ v : Nat → α, (∀ atom ∈ clause.body, atom.Holds I v) →
    ∃ atom ∈ clause.head, atom.Holds I v

def Models (I : Interp α) (clauses : List Clause) : Prop :=
  ∀ clause ∈ clauses, clause.Holds I

/-- A side theory that the worker reads next to the clauses (rules,
cardinality and definer records, datatype semantics). It is any property of
an interpretation. -/
abbrev SideTheory := (α : Type) → Interp α → Prop

/-- Satisfiability of a clause set together with a side theory, over a
nonempty domain. -/
def Satisfiable (clauses : List Clause) (side : SideTheory) : Prop :=
  ∃ (α : Type) (I : Interp α), Nonempty α ∧ Models I clauses ∧ side α I

/-- The side theory reads no concept outside `reserved`: two interpretations
that agree on the domain, the roles, the constants, the functions and every
reserved concept satisfy it together. -/
def ReadsOnly (reserved : List Nat) (side : SideTheory) : Prop :=
  ∀ (α : Type) (I J : Interp α), I.role = J.role → I.ind = J.ind → I.app = J.app →
    (∀ concept ∈ reserved, I.concept concept = J.concept concept) →
    (side α I ↔ side α J)

/-- The empty side theory reads nothing. -/
theorem readsOnly_true (reserved : List Nat) :
    ReadsOnly reserved (fun _ _ => True) := by
  intro _ _ _ _ _ _ _
  exact Iff.rfl

/-! ## Sort clauses and the release transformation -/

/-- `g` of a concept sort clause `g(x) ∧ D(x) → ⊥` (either body order),
exactly `concept_sort_clause` in `inert_sorts.rs`. -/
def conceptSortOf (D : Nat) : Clause → Option Nat
  | ⟨[.concept a (.var x), .concept b (.var y)], []⟩ =>
      if x = y then
        if a = D ∧ b ≠ D then some b
        else if b = D ∧ a ≠ D then some a
        else none
      else none
  | _ => none

/-- `(p, true)` of a domain sort clause `p(x, y) ∧ D(x) → ⊥` and `(p, false)`
of a range sort clause `p(x, y) ∧ D(y) → ⊥`, with `x ≠ y` (either body
order), exactly `role_sort_clause` in `inert_sorts.rs`. -/
def roleSortOf (D : Nat) : Clause → Option (Nat × Bool)
  | ⟨[.role p (.var x) (.var y), .concept d (.var z)], []⟩
  | ⟨[.concept d (.var z), .role p (.var x) (.var y)], []⟩ =>
      if d = D ∧ x ≠ y then
        if z = x then some (p, true)
        else if z = y then some (p, false)
        else none
      else none
  | _ => none

/-- The sort clause of a released definer, removed by the pass. -/
def removedSortClause (D : Nat) (P : List Nat) (clause : Clause) : Bool :=
  match conceptSortOf D clause with
  | some concept => decide (concept ∈ P)
  | none => false

/-- Some head atom puts a released definer on `term`. -/
def releasedTerm (P : List Nat) (clause : Clause) (term : Term) : Bool :=
  clause.head.any fun
    | .concept concept other => decide (concept ∈ P) && decide (other = term)
    | _ => false

def keepHeadAtom (D : Nat) (P : List Nat) (clause : Clause) : Atom → Bool
  | .concept concept term => !(decide (concept = D) && releasedTerm P clause term)
  | _ => true

/-- Drop `D(t)` from the head when a released definer is on `t` there. -/
def dropData (D : Nat) (P : List Nat) (clause : Clause) : Clause :=
  { clause with head := clause.head.filter (keepHeadAtom D P clause) }

/-- The released clause set, in the order the Rust pass produces it. -/
def release (D : Nat) (P : List Nat) (clauses : List Clause) : List Clause :=
  (clauses.filter fun clause => !removedSortClause D P clause).map (dropData D P)

/-! ## Guards -/

/-- Guard tables recomputed from the original clause set. -/
structure Guards where
  /-- Object-sorted concepts with a sort clause, outside `P`. -/
  concepts : List Nat
  /-- Roles with a domain sort clause. -/
  domains : List Nat
  /-- Roles with a range sort clause. -/
  ranges : List Nat
  /-- Individuals that a unit fact over a guard puts outside `D`. -/
  pinned : List Nat
deriving Repr

def guardConcepts (D : Nat) (P : List Nat) (clauses : List Clause) : List Nat :=
  (clauses.filterMap (conceptSortOf D)).filter fun concept => !decide (concept ∈ P)

def domainRoles (D : Nat) (clauses : List Clause) : List Nat :=
  clauses.filterMap fun clause =>
    match roleSortOf D clause with
    | some (role, true) => some role
    | _ => none

def rangeRoles (D : Nat) (clauses : List Clause) : List Nat :=
  clauses.filterMap fun clause =>
    match roleSortOf D clause with
    | some (role, false) => some role
    | _ => none

def pinnedOf (concepts domains ranges : List Nat) : Clause → List Nat
  | ⟨[], [.concept concept (.ind a)]⟩ => if concept ∈ concepts then [a] else []
  | ⟨[], [.role role (.ind a) (.ind b)]⟩ =>
      (if role ∈ domains then [a] else []) ++ (if role ∈ ranges then [b] else [])
  | _ => []

def guards (D : Nat) (P : List Nat) (clauses : List Clause) : Guards :=
  let concepts := guardConcepts D P clauses
  let domains := domainRoles D clauses
  let ranges := rangeRoles D clauses
  { concepts, domains, ranges,
    pinned := clauses.flatMap (pinnedOf concepts domains ranges) }

/-- `atom` is a guard of `term`: false at every data element. -/
def guardsTerm (table : Guards) (term : Term) : Atom → Bool
  | .concept concept other => decide (other = term) && decide (concept ∈ table.concepts)
  | .role role source target =>
      (decide (source = term) && decide (role ∈ table.domains)) ||
        (decide (target = term) && decide (role ∈ table.ranges))
  | .eq _ _ => false

def pinnedTerm (table : Guards) : Term → Bool
  | .ind a => decide (a ∈ table.pinned)
  | _ => false

/-- `term` is outside `D` at every instance of the clause body. -/
def guarded (table : Guards) (clause : Clause) (term : Term) : Bool :=
  pinnedTerm table term || clause.body.any (guardsTerm table term)

/-- Condition (B): every body occurrence of a released definer is guarded. -/
def bodyOk (P : List Nat) (table : Guards) (clause : Clause) : Bool :=
  clause.body.all fun
    | .concept concept term => !decide (concept ∈ P) || guarded table clause term
    | _ => true

/-- Condition (H): every head occurrence of a released definer has `D` on the
same term in the head, or is guarded. -/
def headOk (D : Nat) (P : List Nat) (table : Guards) (clause : Clause) : Bool :=
  clause.head.all fun
    | .concept concept term =>
        !decide (concept ∈ P) || decide (Atom.concept D term ∈ clause.head) ||
          guarded table clause term
    | _ => true

def clauseOk (D : Nat) (P : List Nat) (table : Guards) (clause : Clause) : Bool :=
  removedSortClause D P clause || (bodyOk P table clause && headOk D P table clause)

/-- Executable acceptance condition of a release. -/
def conditions (D : Nat) (P reserved : List Nat) (clauses : List Clause) : Bool :=
  !decide (D ∈ P) && P.all (fun concept => !decide (concept ∈ reserved)) &&
    clauses.all (clauseOk D P (guards D P clauses))

/-! ## Shape lemmas -/

theorem conceptSortOf_spec {D g : Nat} {clause : Clause}
    (h : conceptSortOf D clause = some g) :
    g ≠ D ∧ ∃ x, clause = ⟨[.concept g (.var x), .concept D (.var x)], []⟩ ∨
      clause = ⟨[.concept D (.var x), .concept g (.var x)], []⟩ := by
  unfold conceptSortOf at h
  split at h
  · rename_i a x b y
    split at h
    · subst y
      split at h
      · rename_i hab
        cases h
        exact ⟨hab.2, x, Or.inr (by rw [hab.1])⟩
      · split at h
        · rename_i _ hba
          cases h
          exact ⟨hba.2, x, Or.inl (by rw [hba.1])⟩
        · cases h
    · cases h
  · cases h

theorem roleSortOf_domain_spec {D p : Nat} {clause : Clause}
    (h : roleSortOf D clause = some (p, true)) :
    ∃ x y, x ≠ y ∧
      (clause = ⟨[.role p (.var x) (.var y), .concept D (.var x)], []⟩ ∨
        clause = ⟨[.concept D (.var x), .role p (.var x) (.var y)], []⟩) := by
  unfold roleSortOf at h
  split at h
  · rename_i q x y d z
    split at h
    · rename_i hd
      split at h
      · rename_i hz
        cases h
        subst hz
        exact ⟨z, y, hd.2, Or.inl (by rw [hd.1])⟩
      · split at h <;> cases h
    · cases h
  · rename_i d z q x y
    split at h
    · rename_i hd
      split at h
      · rename_i hz
        cases h
        subst hz
        exact ⟨z, y, hd.2, Or.inr (by rw [hd.1])⟩
      · split at h <;> cases h
    · cases h
  · cases h

theorem roleSortOf_range_spec {D p : Nat} {clause : Clause}
    (h : roleSortOf D clause = some (p, false)) :
    ∃ x y, x ≠ y ∧
      (clause = ⟨[.role p (.var x) (.var y), .concept D (.var y)], []⟩ ∨
        clause = ⟨[.concept D (.var y), .role p (.var x) (.var y)], []⟩) := by
  unfold roleSortOf at h
  split at h
  · rename_i q x y d z
    split at h
    · rename_i hd
      split at h
      · cases h
      · split at h
        · rename_i _ hz
          cases h
          subst hz
          exact ⟨x, z, hd.2, Or.inl (by rw [hd.1])⟩
        · cases h
    · cases h
  · rename_i d z q x y
    split at h
    · rename_i hd
      split at h
      · cases h
      · split at h
        · rename_i _ hz
          cases h
          subst hz
          exact ⟨x, z, hd.2, Or.inr (by rw [hd.1])⟩
        · cases h
    · cases h
  · cases h

theorem conceptSortOf_role_none {D : Nat} {clause : Clause} {rb : Nat × Bool}
    (h : roleSortOf D clause = some rb) : conceptSortOf D clause = none := by
  rcases rb with ⟨p, b⟩
  cases b with
  | true =>
      rcases roleSortOf_domain_spec h with ⟨x, y, _, hc | hc⟩ <;> subst hc <;> rfl
  | false =>
      rcases roleSortOf_range_spec h with ⟨x, y, _, hc | hc⟩ <;> subst hc <;> rfl

/-! ## Semantics of sort clauses -/

theorem conceptSort_excludes {I : Interp α} {D g : Nat} {clause : Clause}
    (hshape : conceptSortOf D clause = some g) (hholds : clause.Holds I)
    (value : α) (hg : I.concept g value) (hD : I.concept D value) : False := by
  rcases (conceptSortOf_spec hshape).2 with ⟨x, hc | hc⟩ <;> subst hc
  · rcases hholds (fun _ => value) (by
      intro atom hatom
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl <;> simpa [Atom.Holds, Term.eval]) with ⟨_, hmem, _⟩
    simp at hmem
  · rcases hholds (fun _ => value) (by
      intro atom hatom
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl <;> simpa [Atom.Holds, Term.eval]) with ⟨_, hmem, _⟩
    simp at hmem

theorem domainSort_excludes {I : Interp α} {D p : Nat} {clause : Clause}
    (hshape : roleSortOf D clause = some (p, true)) (hholds : clause.Holds I)
    (source target : α) (hp : I.role p source target) (hD : I.concept D source) :
    False := by
  classical
  rcases roleSortOf_domain_spec hshape with ⟨x, y, hxy, hc | hc⟩ <;> subst hc
  all_goals
    have hy : y ≠ x := fun h => hxy h.symm
    rcases hholds (fun index => if index = x then source else target) (by
      intro atom hatom
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl <;>
        simp [Atom.Holds, Term.eval, hy, hp, hD]) with ⟨_, hmem, _⟩
    simp at hmem

theorem rangeSort_excludes {I : Interp α} {D p : Nat} {clause : Clause}
    (hshape : roleSortOf D clause = some (p, false)) (hholds : clause.Holds I)
    (source target : α) (hp : I.role p source target) (hD : I.concept D target) :
    False := by
  classical
  rcases roleSortOf_range_spec hshape with ⟨x, y, hxy, hc | hc⟩ <;> subst hc
  all_goals
    have hy : y ≠ x := fun h => hxy h.symm
    rcases hholds (fun index => if index = x then source else target) (by
      intro atom hatom
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hatom
      rcases hatom with rfl | rfl <;>
        simp [Atom.Holds, Term.eval, hy, hp, hD]) with ⟨_, hmem, _⟩
    simp at hmem

/-! ## Witness clauses survive the release -/

/-- The clauses of the original set that justify a guard. -/
def Witness (D : Nat) (P : List Nat) (clauses : List Clause) (clause : Clause) : Prop :=
  (∃ g, conceptSortOf D clause = some g ∧ g ∉ P) ∨
  (∃ rb, roleSortOf D clause = some rb) ∨
  (∃ g a, clause = ⟨[], [.concept g (.ind a)]⟩ ∧ g ∈ guardConcepts D P clauses) ∨
  (∃ p a b, clause = ⟨[], [.role p (.ind a) (.ind b)]⟩)

theorem mem_guardConcepts {D g : Nat} {P : List Nat} {clauses : List Clause}
    (h : g ∈ guardConcepts D P clauses) :
    g ∉ P ∧ ∃ clause ∈ clauses, conceptSortOf D clause = some g := by
  unfold guardConcepts at h
  rw [List.mem_filter, List.mem_filterMap] at h
  rcases h with ⟨⟨clause, hmem, hshape⟩, hP⟩
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hP
  exact ⟨hP, clause, hmem, hshape⟩

theorem mem_domainRoles {D p : Nat} {clauses : List Clause}
    (h : p ∈ domainRoles D clauses) :
    ∃ clause ∈ clauses, roleSortOf D clause = some (p, true) := by
  unfold domainRoles at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨clause, hmem, hshape⟩
  refine ⟨clause, hmem, ?_⟩
  split at hshape
  · rename_i role heq
    cases hshape
    exact heq
  · cases hshape

theorem mem_rangeRoles {D p : Nat} {clauses : List Clause}
    (h : p ∈ rangeRoles D clauses) :
    ∃ clause ∈ clauses, roleSortOf D clause = some (p, false) := by
  unfold rangeRoles at h
  rw [List.mem_filterMap] at h
  rcases h with ⟨clause, hmem, hshape⟩
  refine ⟨clause, hmem, ?_⟩
  split at hshape
  · rename_i role heq
    cases hshape
    exact heq
  · cases hshape

theorem mem_pinnedOf {concepts domains ranges : List Nat} {clause : Clause} {a : Nat}
    (h : a ∈ pinnedOf concepts domains ranges clause) :
    (∃ g, clause = ⟨[], [.concept g (.ind a)]⟩ ∧ g ∈ concepts) ∨
    (∃ p b, clause = ⟨[], [.role p (.ind a) (.ind b)]⟩ ∧ p ∈ domains) ∨
    (∃ p b, clause = ⟨[], [.role p (.ind b) (.ind a)]⟩ ∧ p ∈ ranges) := by
  unfold pinnedOf at h
  split at h
  · rename_i g a'
    split at h
    · rename_i hg
      simp only [List.mem_singleton] at h
      subst h
      exact Or.inl ⟨g, rfl, hg⟩
    · simp at h
  · rename_i p a' b'
    rw [List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hp
        simp only [List.mem_singleton] at h
        subst h
        exact Or.inr (Or.inl ⟨p, b', rfl, hp⟩)
      · simp at h
    · split at h
      · rename_i hp
        simp only [List.mem_singleton] at h
        subst h
        exact Or.inr (Or.inr ⟨p, a', rfl, hp⟩)
      · simp at h
  · simp at h

theorem witness_mem_release {D : Nat} {P : List Nat} {clauses : List Clause}
    {clause : Clause} (hmem : clause ∈ clauses) (hwit : Witness D P clauses clause) :
    clause ∈ release D P clauses := by
  have hnotRemoved : removedSortClause D P clause = false := by
    rcases hwit with ⟨g, hshape, hg⟩ | ⟨rb, hshape⟩ | ⟨g, a, hc, _⟩ | ⟨p, a, b, hc⟩
    · simp [removedSortClause, hshape, hg]
    · simp [removedSortClause, conceptSortOf_role_none hshape]
    · subst hc; rfl
    · subst hc; rfl
  have hdrop : dropData D P clause = clause := by
    rcases hwit with ⟨g, hshape, hg⟩ | ⟨rb, hshape⟩ | ⟨g, a, hc, hgc⟩ | ⟨p, a, b, hc⟩
    · rcases (conceptSortOf_spec hshape).2 with ⟨x, hc | hc⟩ <;> subst hc <;> rfl
    · rcases rb with ⟨p, side⟩
      cases side with
      | true =>
          rcases roleSortOf_domain_spec hshape with ⟨x, y, _, hc | hc⟩ <;> subst hc <;> rfl
      | false =>
          rcases roleSortOf_range_spec hshape with ⟨x, y, _, hc | hc⟩ <;> subst hc <;> rfl
    · subst hc
      rcases mem_guardConcepts hgc with ⟨_, witness, _, hshape⟩
      have hgD := (conceptSortOf_spec hshape).1
      simp [dropData, keepHeadAtom, hgD]
    · subst hc; rfl
  unfold release
  rw [List.mem_map]
  exact ⟨clause, List.mem_filter.mpr ⟨hmem, by simp [hnotRemoved]⟩, hdrop⟩

/-! ## Guards exclude data elements -/

section Exclusion

variable {α : Type} {D : Nat} {P : List Nat} {clauses : List Clause}
  {N : Interp α} {target : List Clause}

/-- In any model of a clause set that keeps every witness clause, a guard is
false at every data element. -/
theorem guard_concept_excludes
    (hmodels : Models N target)
    (hkeep : ∀ clause ∈ clauses, Witness D P clauses clause → clause ∈ target)
    {g : Nat} (hg : g ∈ guardConcepts D P clauses) (value : α)
    (hgv : N.concept g value) (hD : N.concept D value) : False := by
  rcases mem_guardConcepts hg with ⟨hgP, witness, hmem, hshape⟩
  exact conceptSort_excludes hshape
    (hmodels witness (hkeep witness hmem (Or.inl ⟨g, hshape, hgP⟩))) value hgv hD

theorem guard_domain_excludes
    (hmodels : Models N target)
    (hkeep : ∀ clause ∈ clauses, Witness D P clauses clause → clause ∈ target)
    {p : Nat} (hp : p ∈ domainRoles D clauses) (source other : α)
    (hrole : N.role p source other) (hD : N.concept D source) : False := by
  rcases mem_domainRoles hp with ⟨witness, hmem, hshape⟩
  exact domainSort_excludes hshape
    (hmodels witness (hkeep witness hmem (Or.inr (Or.inl ⟨_, hshape⟩)))) source other hrole hD

theorem guard_range_excludes
    (hmodels : Models N target)
    (hkeep : ∀ clause ∈ clauses, Witness D P clauses clause → clause ∈ target)
    {p : Nat} (hp : p ∈ rangeRoles D clauses) (other value : α)
    (hrole : N.role p other value) (hD : N.concept D value) : False := by
  rcases mem_rangeRoles hp with ⟨witness, hmem, hshape⟩
  exact rangeSort_excludes hshape
    (hmodels witness (hkeep witness hmem (Or.inr (Or.inl ⟨_, hshape⟩)))) other value hrole hD

theorem pinned_excludes
    (hmodels : Models N target)
    (hkeep : ∀ clause ∈ clauses, Witness D P clauses clause → clause ∈ target)
    {a : Nat} (ha : a ∈ (guards D P clauses).pinned) (hD : N.concept D (N.ind a)) :
    False := by
  simp only [guards, List.mem_flatMap] at ha
  rcases ha with ⟨fact, hmem, hpin⟩
  rcases mem_pinnedOf hpin with ⟨g, hc, hg⟩ | ⟨p, b, hc, hp⟩ | ⟨p, b, hc, hp⟩
  · subst hc
    have hholds := hmodels _ (hkeep _ hmem (Or.inr (Or.inr (Or.inl ⟨g, a, rfl, hg⟩))))
    rcases hholds (fun _ => N.ind a) (by simp) with ⟨atom, hatom, hval⟩
    simp only [List.mem_singleton] at hatom
    subst hatom
    exact guard_concept_excludes hmodels hkeep hg (N.ind a) hval hD
  · subst hc
    have hholds := hmodels _ (hkeep _ hmem (Or.inr (Or.inr (Or.inr ⟨p, a, b, rfl⟩))))
    rcases hholds (fun _ => N.ind a) (by simp) with ⟨atom, hatom, hval⟩
    simp only [List.mem_singleton] at hatom
    subst hatom
    exact guard_domain_excludes hmodels hkeep hp (N.ind a) (N.ind b) hval hD
  · subst hc
    have hholds := hmodels _ (hkeep _ hmem (Or.inr (Or.inr (Or.inr ⟨p, b, a, rfl⟩))))
    rcases hholds (fun _ => N.ind a) (by simp) with ⟨atom, hatom, hval⟩
    simp only [List.mem_singleton] at hatom
    subst hatom
    exact guard_range_excludes hmodels hkeep hp (N.ind b) (N.ind a) hval hD

/-- A guarded term of a clause instance whose guard atoms hold is not a data
element. -/
theorem guarded_excludes
    (hmodels : Models N target)
    (hkeep : ∀ clause ∈ clauses, Witness D P clauses clause → clause ∈ target)
    {clause : Clause} {term : Term} (v : Nat → α)
    (hguarded : guarded (guards D P clauses) clause term = true)
    (hguards : ∀ atom ∈ clause.body,
      guardsTerm (guards D P clauses) term atom = true → atom.Holds N v)
    (hD : N.concept D (term.eval N v)) : False := by
  unfold guarded at hguarded
  rw [Bool.or_eq_true] at hguarded
  rcases hguarded with hpin | hbody
  · cases term with
    | ind a =>
        simp only [pinnedTerm, decide_eq_true_eq] at hpin
        exact pinned_excludes hmodels hkeep hpin hD
    | var _ => simp [pinnedTerm] at hpin
    | app _ _ => simp [pinnedTerm] at hpin
  · rw [List.any_eq_true] at hbody
    rcases hbody with ⟨atom, hatom, hguard⟩
    have hholds := hguards atom hatom hguard
    cases atom with
    | concept g other =>
        simp only [guardsTerm, Bool.and_eq_true, decide_eq_true_eq] at hguard
        rcases hguard with ⟨rfl, hg⟩
        exact guard_concept_excludes hmodels hkeep (by simpa [guards] using hg) _ hholds hD
    | role p source other =>
        simp only [guardsTerm, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hguard
        rcases hguard with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
        · exact guard_domain_excludes hmodels hkeep (by simpa [guards] using hp) _ _ hholds hD
        · exact guard_range_excludes hmodels hkeep (by simpa [guards] using hp) _ _ hholds hD
    | eq _ _ => simp [guardsTerm] at hguard

end Exclusion

/-! ## The two model transformations -/

/-- Put every released definer on every data element. -/
def Interp.extend (I : Interp α) (D : Nat) (P : List Nat) : Interp α :=
  { I with concept := fun concept value => I.concept concept value ∨ (concept ∈ P ∧ I.concept D value) }

/-- Remove every released definer from every data element. -/
def Interp.restrict (I : Interp α) (D : Nat) (P : List Nat) : Interp α :=
  { I with concept := fun concept value => I.concept concept value ∧ ¬(concept ∈ P ∧ I.concept D value) }

@[simp] theorem Term.eval_extend (I : Interp α) (D : Nat) (P : List Nat)
    (v : Nat → α) (term : Term) : term.eval (I.extend D P) v = term.eval I v := by
  induction term with
  | var => rfl
  | ind => rfl
  | app f arg ih => simp only [Term.eval, ih]; rfl

@[simp] theorem Term.eval_restrict (I : Interp α) (D : Nat) (P : List Nat)
    (v : Nat → α) (term : Term) : term.eval (I.restrict D P) v = term.eval I v := by
  induction term with
  | var => rfl
  | ind => rfl
  | app f arg ih => simp only [Term.eval, ih]; rfl

theorem holds_concept_extend {I : Interp α} {D c : Nat} {P : List Nat} {v : Nat → α}
    {t : Term} : (Atom.concept c t).Holds (I.extend D P) v ↔
      I.concept c (t.eval I v) ∨ (c ∈ P ∧ I.concept D (t.eval I v)) := by
  simp only [Atom.Holds, Term.eval_extend]
  rfl

theorem holds_concept_restrict {I : Interp α} {D c : Nat} {P : List Nat} {v : Nat → α}
    {t : Term} : (Atom.concept c t).Holds (I.restrict D P) v ↔
      I.concept c (t.eval I v) ∧ ¬(c ∈ P ∧ I.concept D (t.eval I v)) := by
  simp only [Atom.Holds, Term.eval_restrict]
  rfl

theorem extend_concept_notMem {I : Interp α} {D concept : Nat} {P : List Nat}
    (h : concept ∉ P) : (I.extend D P).concept concept = I.concept concept := by
  funext value
  apply propext
  simp [Interp.extend, h]

theorem restrict_concept_notMem {I : Interp α} {D concept : Nat} {P : List Nat}
    (h : concept ∉ P) : (I.restrict D P).concept concept = I.concept concept := by
  funext value
  apply propext
  simp [Interp.restrict, h]

theorem extend_holds_mono {I : Interp α} {D : Nat} {P : List Nat} {v : Nat → α}
    {atom : Atom} (h : atom.Holds I v) : atom.Holds (I.extend D P) v := by
  cases atom with
  | concept c t => simp only [Atom.Holds, Term.eval_extend] at h ⊢; exact Or.inl h
  | role r s t => simpa [Atom.Holds] using h
  | eq l r => simpa [Atom.Holds] using h

theorem restrict_holds_anti {I : Interp α} {D : Nat} {P : List Nat} {v : Nat → α}
    {atom : Atom} (h : atom.Holds (I.restrict D P) v) : atom.Holds I v := by
  cases atom with
  | concept c t => simp only [Atom.Holds, Term.eval_restrict] at h ⊢; exact h.1
  | role r s t => simpa [Atom.Holds] using h
  | eq l r => simpa [Atom.Holds] using h

theorem clauseOk_of_conditions {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true) {clause : Clause}
    (hmem : clause ∈ clauses) : clauseOk D P (guards D P clauses) clause = true := by
  simp only [conditions, Bool.and_eq_true, List.all_eq_true] at hcheck
  exact hcheck.2 clause hmem

theorem dataNotReleased {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true) : D ∉ P := by
  simp only [conditions, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hcheck
  exact hcheck.1.1

theorem reservedNotReleased {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true) :
    ∀ concept ∈ reserved, concept ∉ P := by
  simp only [conditions, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hcheck
  intro concept hres hP
  exact hcheck.1.2 concept hP hres

/-- Original model to released model: add the released definers on data. -/
theorem extend_models {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true)
    {I : Interp α} (hmodels : Models I clauses) :
    Models (I.extend D P) (release D P clauses) := by
  have hDP := dataNotReleased hcheck
  intro released hreleased
  unfold release at hreleased
  rw [List.mem_map] at hreleased
  rcases hreleased with ⟨clause, hfilter, rfl⟩
  rw [List.mem_filter] at hfilter
  rcases hfilter with ⟨hmem, hkept⟩
  have hnotRemoved : removedSortClause D P clause = false := by simpa using hkept
  have hok := clauseOk_of_conditions hcheck hmem
  simp only [clauseOk, hnotRemoved, Bool.false_or, Bool.and_eq_true] at hok
  rcases hok with ⟨hbodyOk, _⟩
  intro v hbody'
  -- Every body atom already holds in `I`.
  have hbody : ∀ atom ∈ clause.body, atom.Holds I v := by
    intro atom hatom
    have h' := hbody' atom hatom
    cases atom with
    | concept q t =>
        rw [holds_concept_extend] at h'
        rcases h' with h | ⟨hq, hD⟩
        · exact h
        · exfalso
          have hguard : guarded (guards D P clauses) clause t = true := by
            unfold bodyOk at hbodyOk
            rw [List.all_eq_true] at hbodyOk
            have := hbodyOk _ hatom
            simpa [hq] using this
          refine guarded_excludes (N := I) hmodels (fun c hc _ => hc) v hguard ?_ hD
          intro other hother hguardOther
          have hholds' := hbody' other hother
          cases other with
          | concept g u =>
              simp only [guardsTerm, Bool.and_eq_true, decide_eq_true_eq] at hguardOther
              have hgP := (mem_guardConcepts (by simpa [guards] using hguardOther.2)).1
              simpa [Atom.Holds, extend_concept_notMem hgP] using hholds'
          | role p s u => simpa [Atom.Holds] using hholds'
          | eq l r => simpa [Atom.Holds] using hholds'
    | role p s t => simpa [Atom.Holds] using h'
    | eq l r => simpa [Atom.Holds] using h'
  rcases hmodels clause hmem v hbody with ⟨atom, hatom, hholds⟩
  by_cases hkeep : keepHeadAtom D P clause atom = true
  · exact ⟨atom, List.mem_filter.mpr ⟨hatom, hkeep⟩, extend_holds_mono hholds⟩
  · cases atom with
    | concept d t =>
        have hkeep' : (decide (d = D) && releasedTerm P clause t) = true := by
          simpa [keepHeadAtom] using hkeep
        rw [Bool.and_eq_true, decide_eq_true_eq] at hkeep'
        rcases hkeep' with ⟨rfl, hrel⟩
        unfold releasedTerm at hrel
        rw [List.any_eq_true] at hrel
        rcases hrel with ⟨other, hother, hmatch⟩
        cases other with
        | concept q u =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
            rcases hmatch with ⟨hq, rfl⟩
            have hqD : q ≠ d := fun h => hDP (h ▸ hq)
            refine ⟨.concept q u, List.mem_filter.mpr ⟨hother, ?_⟩, ?_⟩
            · simp [keepHeadAtom, hqD]
            · exact holds_concept_extend.mpr (Or.inr ⟨hq, hholds⟩)
        | role => simp at hmatch
        | eq => simp at hmatch
    | role => simp [keepHeadAtom] at hkeep
    | eq => simp [keepHeadAtom] at hkeep

/-- Released model to original model: remove the released definers from data. -/
theorem restrict_models {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true)
    {J : Interp α} (hmodels : Models J (release D P clauses)) :
    Models (J.restrict D P) clauses := by
  have hDP := dataNotReleased hcheck
  have hkeepWit : ∀ clause ∈ clauses, Witness D P clauses clause →
      clause ∈ release D P clauses := fun _ hmem hwit => witness_mem_release hmem hwit
  intro clause hmem v hbody'
  have hbody : ∀ atom ∈ clause.body, atom.Holds J v :=
    fun atom hatom => restrict_holds_anti (hbody' atom hatom)
  by_cases hremoved : removedSortClause D P clause = true
  · exfalso
    unfold removedSortClause at hremoved
    split at hremoved
    · rename_i q hshape
      simp only [decide_eq_true_eq] at hremoved
      rcases (conceptSortOf_spec hshape).2 with ⟨x, hc | hc⟩ <;> subst hc
      · have hq := hbody' (.concept q (.var x)) (by simp)
        have hD := hbody (.concept D (.var x)) (by simp)
        rw [holds_concept_restrict] at hq
        exact hq.2 ⟨hremoved, hD⟩
      · have hq := hbody' (.concept q (.var x)) (by simp)
        have hD := hbody (.concept D (.var x)) (by simp)
        rw [holds_concept_restrict] at hq
        exact hq.2 ⟨hremoved, hD⟩
    · cases hremoved
  · have hnotRemoved : removedSortClause D P clause = false := by simpa using hremoved
    have hok := clauseOk_of_conditions hcheck hmem
    simp only [clauseOk, hnotRemoved, Bool.false_or, Bool.and_eq_true] at hok
    rcases hok with ⟨_, hheadOk⟩
    have hdropMem : dropData D P clause ∈ release D P clauses := by
      unfold release
      rw [List.mem_map]
      exact ⟨clause, List.mem_filter.mpr ⟨hmem, by simp [hnotRemoved]⟩, rfl⟩
    rcases hmodels _ hdropMem v hbody with ⟨atom, hatom, hholds⟩
    have hatomMem : atom ∈ clause.head := (List.mem_filter.mp hatom).1
    cases atom with
    | concept q t =>
        by_cases hdata : q ∈ P ∧ J.concept D (t.eval J v)
        · have hcases : Atom.concept D t ∈ clause.head ∨
              guarded (guards D P clauses) clause t = true := by
            unfold headOk at hheadOk
            rw [List.all_eq_true] at hheadOk
            have := hheadOk _ hatomMem
            simp only [hdata.1, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
              decide_eq_true_eq] at this
            exact this
          rcases hcases with hDmem | hguard
          · exact ⟨.concept D t, hDmem, holds_concept_restrict.mpr ⟨hdata.2, fun h => hDP h.1⟩⟩
          · exact (guarded_excludes (N := J) hmodels hkeepWit v hguard
              (fun other hother _ => hbody other hother) hdata.2).elim
        · exact ⟨.concept q t, hatomMem, holds_concept_restrict.mpr ⟨hholds, hdata⟩⟩
    | role p s u => exact ⟨.role p s u, hatomMem, by simpa [Atom.Holds] using hholds⟩
    | eq l r => exact ⟨.eq l r, hatomMem, by simpa [Atom.Holds] using hholds⟩

/-! ## Capstone -/

theorem extend_agrees {I : Interp α} {D : Nat} {P reserved : List Nat}
    (hdisjoint : ∀ concept ∈ reserved, concept ∉ P) :
    ∀ concept ∈ reserved, (I.extend D P).concept concept = I.concept concept :=
  fun concept hres => extend_concept_notMem (hdisjoint concept hres)

theorem restrict_agrees {I : Interp α} {D : Nat} {P reserved : List Nat}
    (hdisjoint : ∀ concept ∈ reserved, concept ∉ P) :
    ∀ concept ∈ reserved, (I.restrict D P).concept concept = I.concept concept :=
  fun concept hres => restrict_concept_notMem (hdisjoint concept hres)

/-- **Equisatisfiability of the inert-sort release.** When the executable
guard check accepts the released set `P` for the original clause set, the
original and the released clause sets are satisfiable together with any side
theory that reads only reserved concepts. Both directions hold, so the
rule-consistency worker's verdict (consistent or inconsistent) is the same on
both inputs. -/
theorem release_equisatisfiable {D : Nat} {P reserved : List Nat} {clauses : List Clause}
    (hcheck : conditions D P reserved clauses = true)
    {side : SideTheory} (hside : ReadsOnly reserved side) :
    Satisfiable clauses side ↔ Satisfiable (release D P clauses) side := by
  have hdisjoint := reservedNotReleased hcheck
  constructor
  · rintro ⟨α, I, hne, hmodels, hsideI⟩
    refine ⟨α, I.extend D P, hne, extend_models hcheck hmodels, ?_⟩
    exact (hside α (I.extend D P) I rfl rfl rfl (extend_agrees hdisjoint)).mpr hsideI
  · rintro ⟨α, J, hne, hmodels, hsideJ⟩
    refine ⟨α, J.restrict D P, hne, restrict_models hcheck hmodels, ?_⟩
    exact (hside α (J.restrict D P) J rfl rfl rfl (restrict_agrees hdisjoint)).mpr hsideJ

/-- The same statement for the clauses alone. -/
theorem release_equisatisfiable_clauses {D : Nat} {P reserved : List Nat}
    {clauses : List Clause} (hcheck : conditions D P reserved clauses = true) :
    Satisfiable clauses (fun _ _ => True) ↔
      Satisfiable (release D P clauses) (fun _ _ => True) :=
  release_equisatisfiable hcheck (readsOnly_true reserved)

/-! ## Certificate document -/

/-- The certificate KM emits under `KM_RULES_INERT_CERT`: the sorted clause
set the frontend produced, the released definers, the reserved concepts (every
name a side channel of the worker input reads), and the clause set the worker
actually reads. Names are for audit only; the checker uses the numeric ids. -/
structure WireInertSortRelease where
  version : Nat
  data_sort : Nat
  released : List Nat
  reserved : List Nat
  original : List Clause
  result : List Clause
  concept_names : List String
  role_names : List String
deriving FromJson, ToJson, Repr

def WireInertSortRelease.check (wire : WireInertSortRelease) : Bool :=
  wire.version == 1 &&
    conditions wire.data_sort wire.released wire.reserved wire.original &&
    decide (release wire.data_sort wire.released wire.original = wire.result)

/-- **Checker soundness.** An accepted certificate's worker input is
satisfiable with a side theory reading only reserved concepts iff the original
sorted clause set is. -/
theorem WireInertSortRelease.check_sound (wire : WireInertSortRelease)
    (hcheck : wire.check = true) {side : SideTheory}
    (hside : ReadsOnly wire.reserved side) :
    Satisfiable wire.original side ↔ Satisfiable wire.result side := by
  simp only [WireInertSortRelease.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨_, hconditions⟩, hresult⟩
  rw [← hresult]
  exact release_equisatisfiable hconditions hside

namespace Tests

private def x : Term := .var 0
private def y : Term := .var 1
private def D : Nat := 0
private def Qtop : Nat := 1
private def Q : Nat := 2
private def A : Nat := 3
private def p : Nat := 0

/-- `Q_⊤(x) → Q(x) ∨ D(x)`, `Q(x) ∧ D(x) → ⊥`, `A(x) ∧ D(x) → ⊥`,
`p(x,y) ∧ D(x) → ⊥`, `Q(y) ∧ p(x,y) ∧ A(y) → A(x)`. -/
private def sorted : List Clause := [
  ⟨[.concept Qtop x], [.concept Q x, .concept D x]⟩,
  ⟨[.concept Q x, .concept D x], []⟩,
  ⟨[.concept A x, .concept D x], []⟩,
  ⟨[.role p x y, .concept D x], []⟩,
  ⟨[.concept Q y, .role p x y, .concept A y], [.concept A x]⟩
]

example : conditions D [Q] [] sorted = true := by native_decide

example : release D [Q] sorted = [
  ⟨[.concept Qtop x], [.concept Q x]⟩,
  ⟨[.concept A x, .concept D x], []⟩,
  ⟨[.role p x y, .concept D x], []⟩,
  ⟨[.concept Q y, .role p x y, .concept A y], [.concept A x]⟩
] := by native_decide

/-- `Q(x) → A2(x)` with `A2` unguarded reads `Q` on data: rejected. -/
example : conditions D [Q] [] (sorted ++ [⟨[.concept Q x], [.concept 4 x]⟩]) = false := by
  native_decide

/-- A reserved definer is never released. -/
example : conditions D [Q] [Q] sorted = false := by native_decide

end Tests

#print axioms release_equisatisfiable
#print axioms release_equisatisfiable_clauses
#print axioms WireInertSortRelease.check_sound
#print axioms extend_models
#print axioms restrict_models

end ContextCalculus.RulesInertSort
