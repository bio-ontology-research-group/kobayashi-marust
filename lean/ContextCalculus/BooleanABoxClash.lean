/-! Sound Boolean inclusion projection for the named ABox clash precheck.
These are the two permitted recursion steps in `collect_named_inclusions`.
All other Boolean directions are left to the complete reasoner. -/
namespace ContextCalculus.BooleanABoxClash

variable {Domain : Type}

def Subset (a b : Domain → Prop) : Prop := ∀ x, a x → b x
def Union (parts : List (Domain → Prop)) (x : Domain) : Prop :=
  ∃ part ∈ parts, part x
def Intersection (parts : List (Domain → Prop)) (x : Domain) : Prop :=
  ∀ part ∈ parts, part x

theorem left_union_member (parts : List (Domain → Prop)) (part target : Domain → Prop)
    (hmem : part ∈ parts) (hsub : Subset (Union parts) target) : Subset part target := by
  intro x hx
  exact hsub x ⟨part, hmem, hx⟩

theorem right_intersection_member (parts : List (Domain → Prop))
    (source part : Domain → Prop) (hmem : part ∈ parts)
    (hsub : Subset source (Intersection parts)) : Subset source part := by
  intro x hx
  exact hsub x hx part hmem

theorem equivalent_inclusions (left right : Domain → Prop)
    (heq : ∀ x, left x ↔ right x) : Subset left right ∧ Subset right left := by
  exact ⟨fun x hx => (heq x).mp hx, fun x hx => (heq x).mpr hx⟩

theorem path_composition (a b c : Domain → Prop)
    (hab : Subset a b) (hbc : Subset b c) : Subset a c := by
  intro x hx
  exact hbc x (hab x hx)

theorem asserted_disjoint_clash (source left right : Domain → Prop) (x : Domain)
    (hx : source x) (hl : Subset source left) (hr : Subset source right)
    (hd : ∀ y, ¬(left y ∧ right y)) : False := by
  exact hd x ⟨hl x hx, hr x hx⟩

/-- Unknown additional rules cannot make an inconsistent base satisfiable.
The implementation may suppress a rule-coverage error only with this base
inconsistency premise; it may not publish a consistent partial result. -/
theorem inconsistent_extension {Model : Type} (base extra : Model → Prop)
    (hbase : ¬∃ m, base m) : ¬∃ m, base m ∧ extra m := by
  rintro ⟨m, h, _⟩
  exact hbase ⟨m, h⟩

#print axioms left_union_member
#print axioms right_intersection_member
#print axioms equivalent_inclusions
#print axioms path_composition
#print axioms asserted_disjoint_clash
#print axioms inconsistent_extension
end ContextCalculus.BooleanABoxClash
