namespace ContextCalculus.DLSafeRulePath
universe u v

/-- A role path with every variable restricted to the named-object domain. -/
def namedPath {D : Type u} (named : D → Prop) : List (D → D → Prop) → D → D → Prop
  | [], x, y => named x ∧ x = y
  | r :: rs, x, y => named x ∧ ∃ z, r x z ∧ namedPath named rs z y

/-- Semantics of the nested existential concept ending in a fixed nominal.
Each nonterminal variable retains its DL-safety guard. -/
def rolled {D : Type u} (named : D → Prop) : List (D → D → Prop) → D → D → Prop
  | [], x, y => x = y
  | r :: rs, x, y => named x ∧ ∃ z, r x z ∧ rolled named rs z y

theorem rolling_iff {D : Type u} (named : D → Prop) (rs : List (D → D → Prop))
    (x y : D) : namedPath named rs x y ↔ named y ∧ rolled named rs x y := by
  induction rs generalizing x with
  | nil =>
      constructor
      · rintro ⟨hx, hxy⟩
        cases hxy
        exact ⟨hx, rfl⟩
      · rintro ⟨hy, hxy⟩
        cases hxy
        exact ⟨hy, rfl⟩
  | cons r rs ih =>
      constructor
      · rintro ⟨hx, z, edge, path⟩
        obtain ⟨hy, rest⟩ := (ih z).mp path
        exact ⟨hy, hx, z, edge, rest⟩
      · rintro ⟨hy, hx, z, edge, rest⟩
        exact ⟨hx, z, edge, (ih z).mpr ⟨hy, rest⟩⟩

/-- One compiled axiom per original named endpoint is equivalent to the DL-safe
path rule. The name interpretation need not be injective: there is no UNA.
Unnamed intermediate objects remain excluded on both sides. -/
theorem endpoint_compilation_iff {D : Type u} {I : Type v} (name : I → D)
    (rs : List (D → D → Prop)) (head : D → D → Prop) :
    (∀ x y, namedPath (fun z => ∃ i, name i = z) rs x y → head x y) ↔
    (∀ i x, rolled (fun z => ∃ j, name j = z) rs x (name i) → head x (name i)) := by
  constructor
  · intro rule i x path
    apply rule x (name i)
    exact (rolling_iff _ rs x (name i)).mpr ⟨⟨i, rfl⟩, path⟩
  · intro compiled x y path
    obtain ⟨⟨i, hi⟩, rest⟩ := (rolling_iff _ rs x y).mp path
    subst y
    exact compiled i x rest

#print axioms rolling_iff
#print axioms endpoint_compilation_iff
end ContextCalculus.DLSafeRulePath
