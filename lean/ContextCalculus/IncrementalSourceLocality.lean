/-!
# Source-level locality for positive existential incremental revisions

Interpret inactive atomic classes as empty and retain every role relation.
Closed activation makes this restriction preserve each active expression and
empty each inactive expression. Inactive changed axioms then preserve all
subsumptions of an active query. No generated concept names occur here.

This is a source-semantics theorem, not a certificate for the Rust scanner,
finite bit matrix, typed side-state comparison, or source metadata coverage.
Binary conjunction represents an iterated finite conjunction; equivalent
classes require two inclusions and disjointness an inclusion into bottom.
-/
namespace ContextCalculus.IncrementalSourceLocality

inductive Expr where
  | atom : Nat → Expr
  | top : Expr
  | bottom : Expr
  | conj : Expr → Expr → Expr
  | some : Nat → Expr → Expr
  deriving DecidableEq

structure Model (U : Type) where
  classes : Nat → U → Prop
  roles : Nat → U → U → Prop

def eval (m : Model U) : Expr → U → Prop
  | .atom a, x => m.classes a x
  | .top, _ => True
  | .bottom, _ => False
  | .conj a b, x => eval m a x ∧ eval m b x
  | .some r a, x => ∃ y, m.roles r x y ∧ eval m a y

def mask (active : Expr → Prop) (m : Model U) : Model U :=
  { classes := fun a x => active (.atom a) ∧ m.classes a x
    roles := m.roles }

/-- The structural activation edges required for each observed expression. -/
def Stable (active : Expr → Prop) : Expr → Prop
  | .atom _ => True
  | .top => active .top
  | .bottom => True
  | .conj a b => Stable active a ∧ Stable active b ∧
      (active (.conj a b) ↔ active a ∧ active b)
  | .some r a => Stable active a ∧ (active (.some r a) ↔ active a)

theorem eval_mask {active : Expr → Prop} {e : Expr}
    (stable : Stable active e) (m : Model U) (x : U) :
    eval (mask active m) e x ↔ active e ∧ eval m e x := by
  induction e generalizing x with
  | atom a => rfl
  | top => exact ⟨fun _ => ⟨stable, trivial⟩, fun _ => trivial⟩
  | bottom => exact ⟨False.elim, fun h => h.2⟩
  | conj a b ia ib =>
    rcases stable with ⟨sa, sb, closed⟩
    constructor
    · intro h
      have ha := (ia sa x).mp h.1
      have hb := (ib sb x).mp h.2
      exact ⟨closed.mpr ⟨ha.1, hb.1⟩, ha.2, hb.2⟩
    · intro h
      have both := closed.mp h.1
      exact ⟨(ia sa x).mpr ⟨both.1, h.2.1⟩,
        (ib sb x).mpr ⟨both.2, h.2.2⟩⟩
  | some r a ia =>
    rcases stable with ⟨sa, closed⟩
    constructor
    · rintro ⟨y, edge, holds⟩
      have h := (ia sa y).mp holds
      exact ⟨closed.mpr h.1, y, edge, h.2⟩
    · rintro ⟨enabled, y, edge, holds⟩
      exact ⟨y, edge, (ia sa y).mpr ⟨closed.mp enabled, holds⟩⟩

abbrev Axiom := Expr × Expr

def Satisfies (m : Model U) (theory : List Axiom) : Prop :=
  ∀ ax, ax ∈ theory → ∀ x, eval m ax.1 x → eval m ax.2 x

/-- Changed inactive inclusions need no evaluation or retained completion state. -/
theorem transfer_model {old newer : List Axiom} {active : Expr → Prop}
    (stable : ∀ ax, ax ∈ newer → Stable active ax.1 ∧ Stable active ax.2)
    (closed : ∀ ax, ax ∈ newer → active ax.1 → active ax.2)
    (inactive : ∀ ax, ax ∈ newer → ax ∉ old → ¬ active ax.1)
    (m : Model U) (valid : Satisfies m old) :
    Satisfies (mask active m) newer := by
  classical
  intro ax member x premise
  have left := (eval_mask (stable ax member).1 m x).mp premise
  by_cases kept : ax ∈ old
  · exact (eval_mask (stable ax member).2 m x).mpr
      ⟨closed ax member left.1, valid ax kept x left.2⟩
  · exact False.elim (inactive ax member kept left.1)

/-- A fixed role-only theory may contain arbitrary role chains, inclusions,
domains of the relation universe, or transitivity constraints. Masking changes
no role. Class-valued role domains/ranges must be included in the source
inclusions or justified separately; they are not hidden in this assumption. -/
def Subsumes (roleLaw : (Nat → U → U → Prop) → Prop)
    (theory : List Axiom) (query target : Nat) : Prop :=
  ∀ m : Model U, roleLaw m.roles → Satisfies m theory →
    ∀ x, m.classes query x → m.classes target x

theorem inactive_delta_preserves_subsumptions
    {old newer : List Axiom} {active : Expr → Prop}
    (stable : ∀ ax, ax ∈ old ∨ ax ∈ newer →
      Stable active ax.1 ∧ Stable active ax.2)
    (closed : ∀ ax, ax ∈ old ∨ ax ∈ newer → active ax.1 → active ax.2)
    (removed : ∀ ax, ax ∈ old → ax ∉ newer → ¬ active ax.1)
    (added : ∀ ax, ax ∈ newer → ax ∉ old → ¬ active ax.1)
    (query target : Nat) (seed : active (.atom query))
    (roleLaw : (Nat → U → U → Prop) → Prop) :
    Subsumes roleLaw old query target ↔ Subsumes roleLaw newer query target := by
  constructor
  · intro entails m law valid x holds
    have restricted := transfer_model
      (fun ax h => stable ax (Or.inl h))
      (fun ax h => closed ax (Or.inl h)) removed m valid
    exact (entails (mask active m) law restricted x ⟨seed, holds⟩).2
  · intro entails m law valid x holds
    have restricted := transfer_model
      (fun ax h => stable ax (Or.inr h))
      (fun ax h => closed ax (Or.inr h)) added m valid
    exact (entails (mask active m) law restricted x ⟨seed, holds⟩).2

def QuerySatisfiable (roleLaw : (Nat → U → U → Prop) → Prop)
    (theory : List Axiom) (query : Nat) : Prop :=
  ∃ m : Model U, roleLaw m.roles ∧ Satisfies m theory ∧ ∃ x, m.classes query x

theorem inactive_delta_preserves_query_satisfiability
    {old newer : List Axiom} {active : Expr → Prop}
    (stable : ∀ ax, ax ∈ old ∨ ax ∈ newer →
      Stable active ax.1 ∧ Stable active ax.2)
    (closed : ∀ ax, ax ∈ old ∨ ax ∈ newer → active ax.1 → active ax.2)
    (removed : ∀ ax, ax ∈ old → ax ∉ newer → ¬ active ax.1)
    (added : ∀ ax, ax ∈ newer → ax ∉ old → ¬ active ax.1)
    (query : Nat) (seed : active (.atom query))
    (roleLaw : (Nat → U → U → Prop) → Prop) :
    QuerySatisfiable roleLaw old query ↔ QuerySatisfiable roleLaw newer query := by
  constructor
  · rintro ⟨m, law, valid, x, holds⟩
    exact ⟨mask active m, law, transfer_model
      (fun ax h => stable ax (Or.inr h))
      (fun ax h => closed ax (Or.inr h)) added m valid, x, seed, holds⟩
  · rintro ⟨m, law, valid, x, holds⟩
    exact ⟨mask active m, law, transfer_model
      (fun ax h => stable ax (Or.inl h))
      (fun ax h => closed ax (Or.inl h)) removed m valid, x, seed, holds⟩

#print axioms eval_mask
#print axioms transfer_model
#print axioms inactive_delta_preserves_subsumptions
#print axioms inactive_delta_preserves_query_satisfiability

end ContextCalculus.IncrementalSourceLocality
