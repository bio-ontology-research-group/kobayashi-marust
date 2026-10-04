namespace ContextCalculus.DataABoxProjection
universe u v w z

/-- Least data extension of an object interpretation and asserted data edges.
The assertion relation includes the transitive superproperty closure. -/
def extension {P : Type u} {N : Type v} {O : Type w} {D : Type z}
    (asserted : P → N → D → Prop) (owner : N → O) (p : P) (x : O) (d : D) : Prop :=
  ∃ n, asserted p n d ∧ owner n = x

/-- Functional data edges are equivalent to all unequal-value owner constraints.
Object names may denote the same element; no unique-name premise is needed. -/
theorem functionality_iff {P : Type u} {N : Type v} {O : Type w} {D : Type z} [DecidableEq D]
    (asserted : P → N → D → Prop) (owner : N → O) (p : P) :
    (∀ x d e, extension asserted owner p x d → extension asserted owner p x e → d = e) ↔
    (∀ a b d e, asserted p a d → asserted p b e → d ≠ e → owner a ≠ owner b) := by
  constructor
  · intro functional a b d e ha hb different same
    exact different (functional (owner a) d e ⟨a, ha, rfl⟩ ⟨b, hb, same.symm⟩)
  · intro constraints x d e hd he
    rcases hd with ⟨a, ha, ax⟩
    rcases he with ⟨b, hb, bx⟩
    cases (inferInstance : Decidable (d = e)) with
    | isTrue same => exact same
    | isFalse different => exact False.elim (constraints a b d e ha hb different (ax.trans bx.symm))

/-- The projected domain assertion is exactly the obligation on every owner. -/
theorem domain_iff {P : Type u} {N : Type v} {O : Type w} {D : Type z}
    (asserted : P → N → D → Prop) (owner : N → O) (p : P) (domain : O → Prop) :
    (∀ x d, extension asserted owner p x d → domain x) ↔
    (∀ n d, asserted p n d → domain (owner n)) := by
  constructor
  · intro h n d edge
    exact h (owner n) d ⟨n, edge, rfl⟩
  · intro h x d edge
    rcases edge with ⟨n, hn, rfl⟩
    exact h n d hn

/-- Concrete range membership is checked on every inherited assertion. -/
theorem range_iff {P : Type u} {N : Type v} {O : Type w} {D : Type z}
    (asserted : P → N → D → Prop) (owner : N → O) (p : P) (range : D → Prop) :
    (∀ x d, extension asserted owner p x d → range d) ↔
    (∀ n d, asserted p n d → range d) := by
  constructor
  · intro h n d edge
    exact h (owner n) d ⟨n, edge, rfl⟩
  · intro h x d edge
    rcases edge with ⟨n, hn, _⟩
    exact h n d hn

/-- Closing asserted edges under property inclusion preserves that inclusion. -/
theorem inclusion_preserved {P : Type u} {N : Type v} {O : Type w} {D : Type z}
    (asserted : P → N → D → Prop) (owner : N → O) (p q : P)
    (closed : ∀ n d, asserted p n d → asserted q n d) :
    ∀ x d, extension asserted owner p x d → extension asserted owner q x d := by
  intro x d edge
  rcases edge with ⟨n, hn, hx⟩
  exact ⟨n, closed n d hn, hx⟩

#print axioms functionality_iff
#print axioms domain_iff
#print axioms range_iff
#print axioms inclusion_preserved
end ContextCalculus.DataABoxProjection
