/-!
SQWRL observers collect results outside the ontology and impose no object-model
constraint. This module proves that projecting rules with exclusively observer
heads preserves models and all object-language consequences. The Rust source
recognizer and the published observer contract remain the explicit boundary;
mixed logical heads retain every logical conjunct.
-/
namespace ContextCalculus.SQWRLClassificationProjection

inductive Head (M B : Type) where
  | logical : (M → B → Prop) → Head M B
  | observer : Head M B

def satisfiesHead (m : M) (b : B) : Head M B → Prop
  | .logical p => p m b
  | .observer => True

def observerOnly : Head M B → Prop
  | .logical _ => False
  | .observer => True

def rule (body : M → B → Prop) (head : List (Head M B)) (m : M) : Prop :=
  ∀ b, body m b → ∀ h ∈ head, satisfiesHead m b h

def project : List (Head M B) → List (Head M B)
  | [] => []
  | .observer :: rest => project rest
  | .logical p :: rest => .logical p :: project rest

theorem head_projection (m : M) (b : B) (head : List (Head M B)) :
    (∀ h ∈ head, satisfiesHead m b h) ↔
      (∀ h ∈ project head, satisfiesHead m b h) := by
  induction head with
  | nil => simp [project]
  | cons h rest ih =>
    cases h with
    | logical p =>
      simpa only [project, List.forall_mem_cons] using
        (and_congr (Iff.rfl : satisfiesHead m b (.logical p) ↔ satisfiesHead m b (.logical p)) ih)
    | observer =>
      simpa only [project, List.forall_mem_cons, satisfiesHead, true_and] using ih

theorem mixed_rule_preserved (body : M → B → Prop) (head : List (Head M B))
    (m : M) : rule body head m ↔ rule body (project head) m := by
  unfold rule
  exact forall_congr' fun b => imp_congr_right fun _ => head_projection m b head

theorem observer_rule_true (body : M → B → Prop) (head : List (Head M B))
    (observed : ∀ h ∈ head, observerOnly h) (m : M) : rule body head m := by
  intro b _ h hh
  have ho := observed h hh
  cases h with
  | logical p => exact False.elim ho
  | observer => trivial

theorem models_preserved (base : M → Prop)
    (bodies : R → M → B → Prop) (heads : R → List (Head M B))
    (observed : ∀ r h, h ∈ heads r → observerOnly h) (m : M) :
    (base m ∧ ∀ r, rule (bodies r) (heads r) m) ↔ base m := by
  constructor
  · exact And.left
  · intro hb
    exact ⟨hb, fun r => observer_rule_true (bodies r) (heads r) (observed r) m⟩

theorem consequences_preserved (base consequence : M → Prop)
    (bodies : R → M → B → Prop) (heads : R → List (Head M B))
    (observed : ∀ r h, h ∈ heads r → observerOnly h) :
    (∀ m, (base m ∧ ∀ r, rule (bodies r) (heads r) m) → consequence m) ↔
      (∀ m, base m → consequence m) := by
  constructor
  · intro h m hb
    exact h m ((models_preserved base bodies heads observed m).mpr hb)
  · intro h m hb
    exact h m hb.1

#print axioms models_preserved
#print axioms consequences_preserved
#print axioms mixed_rule_preserved

end ContextCalculus.SQWRLClassificationProjection
