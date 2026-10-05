/-!
Semantic building blocks for finite named-object rule grounding through a fresh
anchor. No unique-name assumption is used. These lemmas do not certify a source
coverage check or a backend classification result.
-/
namespace ContextCalculus.DLSafeGroundRuleNormalization
variable {Object : Type}
theorem singleton_link_lift (link : Object → Object → Prop)
    (anchor target : Object) (concept : Object → Prop)
    (present : link anchor target)
    (only : ∀ x, link anchor x → x = target) :
    (∃ x, link anchor x ∧ concept x) ↔ concept target := by
  constructor
  · rintro ⟨x, edge, member⟩
    exact (only x edge) ▸ member
  · intro member
    exact ⟨target, present, member⟩
theorem canonical_link_exists (anchor target : Object) :
    ∃ link : Object → Object → Prop,
      link anchor target ∧ (∀ x, link anchor x → x = target) := by
  exact ⟨fun x y => x = anchor ∧ y = target, ⟨rfl, rfl⟩,
    fun _ edge => edge.2⟩
theorem anchored_implication_iff (anchor : Object)
    (body head : Object → Prop) (premise conclusion : Prop)
    (body_exact : body anchor ↔ premise)
    (head_exact : head anchor ↔ conclusion) :
    (∀ x, x = anchor → body x → head x) ↔ (premise → conclusion) := by
  constructor
  · intro rule hp
    exact head_exact.mp (rule anchor rfl (body_exact.mpr hp))
  · intro rule x hx hb
    subst x
    exact head_exact.mpr (rule (body_exact.mp hb))
/-- Coverage suffices even when different names denote the same assignment. -/
theorem named_grounding_iff {Names Binding : Type}
    (denote : Names → Binding) (covers : ∀ b, ∃ n, denote n = b)
    (satisfies : Binding → Prop) :
    (∀ b, satisfies b) ↔ (∀ n, satisfies (denote n)) := by
  constructor
  · intro all n
    exact all (denote n)
  · intro all b
    obtain ⟨n, rfl⟩ := covers b
    exact all n
#print axioms singleton_link_lift
#print axioms canonical_link_exists
#print axioms anchored_implication_iff
#print axioms named_grounding_iff
end ContextCalculus.DLSafeGroundRuleNormalization

namespace ContextCalculus.DLSafeGroundRuleNormalization

/-- Ground atoms retained by the object-rule compiler. Names may co-denote. -/
inductive GroundAtom (Name Class Role : Type) where
  | member : Class → Name → GroundAtom Name Class Role
  | edge : Role → Name → Name → GroundAtom Name Class Role
  | same : Name → Name → GroundAtom Name Class Role
  | different : Name → Name → GroundAtom Name Class Role

variable {Object Name Class Role Atom : Type}

def groundTruth (classes : Class → Object → Prop)
    (roles : Role → Object → Object → Prop) (denote : Name → Object) :
    GroundAtom Name Class Role → Prop
  | .member c a => classes c (denote a)
  | .edge r a b => roles r (denote a) (denote b)
  | .same a b => denote a = denote b
  | .different a b => denote a ≠ denote b

def liftedTruth (classes : Class → Object → Prop)
    (roles : Role → Object → Object → Prop) (denote : Name → Object)
    (links : Name → Object → Object → Prop) (anchor : Object) :
    GroundAtom Name Class Role → Prop
  | .member c a => ∃ x, links a anchor x ∧ classes c x
  | .edge r a b => ∃ x, links a anchor x ∧ ∃ y, roles r x y ∧ y = denote b
  | .same a b => ∃ x, links a anchor x ∧ x = denote b
  | .different a b => ∃ x, links a anchor x ∧ x ≠ denote b

theorem ground_atom_exact (classes : Class → Object → Prop)
    (roles : Role → Object → Object → Prop) (denote : Name → Object)
    (links : Name → Object → Object → Prop) (anchor : Object)
    (present : ∀ a, links a anchor (denote a))
    (only : ∀ a x, links a anchor x → x = denote a)
    (atom : GroundAtom Name Class Role) :
    liftedTruth classes roles denote links anchor atom ↔ groundTruth classes roles denote atom := by
  cases atom with
  | member c a => exact singleton_link_lift (links a) anchor (denote a) (classes c) (present a) (only a)
  | edge r a b =>
      refine (singleton_link_lift (links a) anchor (denote a)
        (fun x => ∃ y, roles r x y ∧ y = denote b) (present a) (only a)).trans ?_
      constructor
      · rintro ⟨y, edge, equality⟩
        change roles r (denote a) (denote b)
        exact equality ▸ edge
      · intro edge
        exact ⟨denote b, edge, rfl⟩
  | same a b =>
      exact singleton_link_lift (links a) anchor (denote a)
        (fun x => x = denote b) (present a) (only a)
  | different a b =>
      exact singleton_link_lift (links a) anchor (denote a)
        (fun x => x ≠ denote b) (present a) (only a)

def conjunction (truth : Atom → Prop) : List Atom → Prop
  | [] => True
  | atom :: rest => truth atom ∧ conjunction truth rest

/-- An empty SWRL consequent is false; a nonempty consequent is conjunctive. -/
def consequent (truth : Atom → Prop) (head : List Atom) : Prop :=
  match head with
  | [] => False
  | atom :: rest => truth atom ∧ conjunction truth rest

theorem conjunction_exact (left right : Atom → Prop)
    (exact : ∀ atom, left atom ↔ right atom) (atoms : List Atom) :
    conjunction left atoms ↔ conjunction right atoms := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih => exact and_congr (exact atom) ih

theorem consequent_exact (left right : Atom → Prop)
    (exact : ∀ atom, left atom ↔ right atom) (atoms : List Atom) :
    consequent left atoms ↔ consequent right atoms := by
  cases atoms with
  | nil => rfl
  | cons atom rest => exact and_congr (exact atom) (conjunction_exact left right exact rest)

theorem grounded_rule_exact (classes : Class → Object → Prop)
    (roles : Role → Object → Object → Prop) (denote : Name → Object)
    (links : Name → Object → Object → Prop) (anchor : Object)
    (present : ∀ a, links a anchor (denote a))
    (only : ∀ a x, links a anchor x → x = denote a)
    (body head : List (GroundAtom Name Class Role)) :
    (∀ x, x = anchor → conjunction (liftedTruth classes roles denote links x) body →
      consequent (liftedTruth classes roles denote links x) head) ↔
    (conjunction (groundTruth classes roles denote) body →
      consequent (groundTruth classes roles denote) head) := by
  apply anchored_implication_iff anchor _ _ _ _
  · exact conjunction_exact _ _ (ground_atom_exact classes roles denote links anchor present only) body
  · exact consequent_exact _ _ (ground_atom_exact classes roles denote links anchor present only) head

theorem ground_family_extension_iff (classes : Class → Object → Prop)
    (roles : Role → Object → Object → Prop) (denote : Name → Object)
    (anchor : Object) (rules : List (List (GroundAtom Name Class Role) ×
      List (GroundAtom Name Class Role))) :
    (∃ links : Name → Object → Object → Prop,
      (∀ a, links a anchor (denote a)) ∧
      (∀ a x, links a anchor x → x = denote a) ∧
      (∀ rule ∈ rules, ∀ x, x = anchor →
        conjunction (liftedTruth classes roles denote links x) rule.1 →
        consequent (liftedTruth classes roles denote links x) rule.2)) ↔
    (∀ rule ∈ rules, conjunction (groundTruth classes roles denote) rule.1 →
      consequent (groundTruth classes roles denote) rule.2) := by
  constructor
  · rintro ⟨links, present, only, compiled⟩ rule member
    exact (grounded_rule_exact classes roles denote links anchor present only rule.1 rule.2).mp
      (compiled rule member)
  · intro source
    let links : Name → Object → Object → Prop := fun a x y => x = anchor ∧ y = denote a
    have present : ∀ a, links a anchor (denote a) := fun _ => ⟨rfl, rfl⟩
    have only : ∀ a x, links a anchor x → x = denote a := fun _ _ edge => edge.2
    refine ⟨links, present, only, ?_⟩
    intro rule member
    exact (grounded_rule_exact classes roles denote links anchor present only rule.1 rule.2).mpr
      (source rule member)

#print axioms ground_family_extension_iff
#print axioms ground_atom_exact
#print axioms conjunction_exact
#print axioms consequent_exact
#print axioms grounded_rule_exact
end ContextCalculus.DLSafeGroundRuleNormalization
