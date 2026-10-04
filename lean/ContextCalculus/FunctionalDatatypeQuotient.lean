namespace ContextCalculus.FunctionalDatatypeQuotient
universe u v w

def imageRole {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (x : O) (y : W) : Prop :=
  ∃ v, r x v ∧ f v = y

theorem functional_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop)
    (functional : ∀ x a b, r x a → r x b → a = b) :
    ∀ x a b, imageRole f r x a → imageRole f r x b → a = b := by
  rintro x a b ⟨v, hv, ha⟩ ⟨w, hw, hb⟩
  have equal := congrArg f (functional x v w hv hw)
  exact ha.symm.trans (equal.trans hb)

theorem exists_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (p : V → Prop) (q : W → Prop)
    (profile : ∀ v, p v ↔ q (f v)) (x : O) :
    (∃ v, r x v ∧ p v) ↔ ∃ w, imageRole f r x w ∧ q w := by
  constructor
  · rintro ⟨v, edge, hv⟩
    exact ⟨f v, ⟨v, edge, rfl⟩, (profile v).mp hv⟩
  · rintro ⟨w, ⟨v, edge, rfl⟩, hw⟩
    exact ⟨v, edge, (profile v).mpr hw⟩

theorem forall_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (p : V → Prop) (q : W → Prop)
    (profile : ∀ v, p v ↔ q (f v)) (x : O) :
    (∀ v, r x v → p v) ↔ ∀ w, imageRole f r x w → q w := by
  constructor
  · rintro universal w ⟨v, edge, rfl⟩
    exact (profile v).mp (universal v edge)
  · intro universal v edge
    exact (profile v).mpr (universal (f v) ⟨v, edge, rfl⟩)

/-- Singleton profiles are necessary for negative as well as positive literal
assertions. Merely preserving interval membership would not be enough. -/
theorem literal_assertion_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (literal : V) (target : W)
    (singleton : ∀ v, f v = target ↔ v = literal) (x : O) :
    imageRole f r x target ↔ r x literal := by
  constructor
  · rintro ⟨v, edge, mapped⟩
    have h := (singleton v).mp mapped
    exact h ▸ edge
  · intro edge
    exact ⟨literal, edge, (singleton literal).mpr rfl⟩

#print axioms functional_preserved
#print axioms exists_preserved
#print axioms forall_preserved
#print axioms literal_assertion_preserved
/-- Qualified minimum cardinality in the ordinary distinct-witness semantics. -/
def atLeast {O : Type u} {V : Type v} (r : O → V → Prop)
    (p : V → Prop) (x : O) (n : Nat) : Prop :=
  ∃ witnesses : Fin n → V,
    (∀ i, r x (witnesses i) ∧ p (witnesses i)) ∧
    (∀ i j, witnesses i = witnesses j → i = j)

/-- Functionality prevents a quotient from collapsing distinct successors of
one subject. Literal/global-range profile proofs remain separate premises. -/
theorem cardinality_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (p : V → Prop) (q : W → Prop)
    (functional : ∀ x a b, r x a → r x b → a = b)
    (profile : ∀ v, p v ↔ q (f v)) (x : O) (n : Nat) :
    atLeast r p x n ↔ atLeast (imageRole f r) q x n := by
  constructor
  · rintro ⟨vs, edges, distinct⟩
    refine ⟨fun i => f (vs i), ?_, ?_⟩
    · intro i
      exact ⟨⟨vs i, (edges i).1, rfl⟩, (profile (vs i)).mp (edges i).2⟩
    · intro i j _
      exact distinct i j (functional x (vs i) (vs j) (edges i).1 (edges j).1)
  · rintro ⟨ws, edges, distinct⟩
    classical
    let vs : Fin n → V := fun i => Classical.choose (edges i).1
    have lifted : ∀ i, r x (vs i) ∧ f (vs i) = ws i :=
      fun i => Classical.choose_spec (edges i).1
    refine ⟨vs, ?_, ?_⟩
    · intro i
      exact ⟨(lifted i).1, (profile (vs i)).mpr ((lifted i).2.symm ▸ (edges i).2)⟩
    · intro i j equal
      apply distinct i j
      exact (lifted i).2.symm.trans ((congrArg f equal).trans (lifted j).2)

/-- Maximum cardinality is the absence of n+1 distinct qualified witnesses. -/
theorem maximum_cardinality_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (p : V → Prop) (q : W → Prop)
    (functional : ∀ x a b, r x a → r x b → a = b)
    (profile : ∀ v, p v ↔ q (f v)) (x : O) (n : Nat) :
    (¬ atLeast r p x (n+1)) ↔ (¬ atLeast (imageRole f r) q x (n+1)) :=
  not_congr (cardinality_preserved f r p q functional profile x (n+1))

theorem exact_cardinality_preserved {O : Type u} {V : Type v} {W : Type w}
    (f : V → W) (r : O → V → Prop) (p : V → Prop) (q : W → Prop)
    (functional : ∀ x a b, r x a → r x b → a = b)
    (profile : ∀ v, p v ↔ q (f v)) (x : O) (n : Nat) :
    (atLeast r p x n ∧ ¬ atLeast r p x (n+1)) ↔
    (atLeast (imageRole f r) q x n ∧ ¬ atLeast (imageRole f r) q x (n+1)) :=
  and_congr (cardinality_preserved f r p q functional profile x n)
    (maximum_cardinality_preserved f r p q functional profile x n)

#print axioms exact_cardinality_preserved
#print axioms cardinality_preserved
#print axioms maximum_cardinality_preserved
end ContextCalculus.FunctionalDatatypeQuotient
