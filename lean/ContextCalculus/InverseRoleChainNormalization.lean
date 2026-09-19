import ContextCalculus.CBRoleChainEncoding

/-! Inverse expressions in a chain are replaced by fresh converse symbols.
The two namespaces model the frontend's disjoint source/internal symbol ranges.
This certificate concerns normalization, not the completeness of a worker.
-/
namespace ContextCalculus.InverseRoleChainNormalization

inductive Expr (R : Type) where
  | named : R → Expr R
  | inverse : R → Expr R

def eval (i : R → D → D → Prop) : Expr R → D → D → Prop
  | .named r => i r
  | .inverse r => fun x y => i r y x

def symbol : Expr R → Sum R R
  | .named r => .inl r
  | .inverse r => .inr r

def expand (i : R → D → D → Prop) : Sum R R → D → D → Prop
  | .inl r => i r
  | .inr r => fun x y => i r y x

def bridges (j : Sum R R → D → D → Prop) : Prop :=
  ∀ r x y, j (.inr r) x y ↔ j (.inl r) y x

def path (i : R → D → D → Prop) : List R → D → D → Prop
  | [], x, y => x = y
  | r :: rs, x, y => ∃ z, i r x z ∧ path i rs z y

def inclusion (i : R → D → D → Prop) (rs : List R) (sup : R) : Prop :=
  ∀ x y, path i rs x y → i sup x y

theorem expand_bridges (i : R → D → D → Prop) : bridges (expand i) := by
  intro r x y
  rfl

theorem eval_symbol (j : Sum R R → D → D → Prop) (h : bridges j)
    (r : Expr R) (x y : D) :
    eval (fun r => j (.inl r)) r x y ↔ j (symbol r) x y := by
  cases r with
  | named r => rfl
  | inverse r => exact (h r x y).symm

theorem path_symbols (j : Sum R R → D → D → Prop) (h : bridges j)
    (rs : List (Expr R)) (x y : D) :
    path (eval (fun r => j (.inl r))) rs x y ↔
      path j (rs.map symbol) x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [path, List.map_cons]
    exact exists_congr fun z => and_congr (eval_symbol j h r x z) (ih z)

theorem inclusion_symbols (j : Sum R R → D → D → Prop) (h : bridges j)
    (rs : List (Expr R)) (sup : Expr R) :
    inclusion (eval (fun r => j (.inl r))) rs sup ↔
      inclusion j (rs.map symbol) (symbol sup) := by
  unfold inclusion
  exact forall_congr' fun x => forall_congr' fun y =>
    imp_congr (path_symbols j h rs x y) (eval_symbol j h sup x y)

/-- Only inverse symbols actually used by a chain require defining bridges. -/
def realizes (j : Sum R R → D → D → Prop) (r : Expr R) : Prop :=
  ∀ x y, eval (fun r => j (.inl r)) r x y ↔ j (symbol r) x y

theorem path_symbols_on (j : Sum R R → D → D → Prop)
    (rs : List (Expr R)) (h : ∀ r ∈ rs, realizes j r) (x y : D) :
    path (eval (fun r => j (.inl r))) rs x y ↔
      path j (rs.map symbol) x y := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    simp only [path, List.map_cons]
    exact exists_congr fun z => and_congr
      (h r (by simp) x z)
      (ih (fun q hq => h q (by simp [hq])) z)

theorem inclusion_symbols_on (j : Sum R R → D → D → Prop)
    (rs : List (Expr R)) (sup : Expr R)
    (h : ∀ r ∈ sup :: rs, realizes j r) :
    inclusion (eval (fun r => j (.inl r))) rs sup ↔
      inclusion j (rs.map symbol) (symbol sup) := by
  unfold inclusion
  exact forall_congr' fun x => forall_congr' fun y =>
    imp_congr (path_symbols_on j rs (fun q hq => h q (by simp [hq])) x y)
      (h sup (by simp) x y)

/-- Every original interpretation has an exact expansion, and every normalized
model projects back. `base` carries every other source axiom and `consequence`
any property of the original interpretation. Thus no source consequence is
invented or lost by adding the converse symbols and their defining bridges. -/
theorem consequences_preserved
    (base consequence : (R → D → D → Prop) → Prop)
    (rs : List (Expr R)) (sup : Expr R) :
    (∀ i, base i → inclusion (eval i) rs sup → consequence i) ↔
    (∀ j, base (fun r => j (.inl r)) → bridges j →
      inclusion j (rs.map symbol) (symbol sup) →
      consequence (fun r => j (.inl r))) := by
  constructor
  · intro source j hb hj hc
    exact source _ hb ((inclusion_symbols j hj rs sup).mpr hc)
  · intro normalized i hb hc
    exact normalized (expand i) hb (expand_bridges i)
      ((inclusion_symbols (expand i) (expand_bridges i) rs sup).mp hc)

/-- The simultaneous statement covers shared inverse proxies across all source
chains. Realization is required only for symbols occurring in those chains. -/
theorem theory_consequences_preserved
    (base consequence : (R → D → D → Prop) → Prop)
    (chains : List (List (Expr R) × Expr R)) :
    (∀ i, base i → (∀ c ∈ chains, inclusion (eval i) c.1 c.2) → consequence i) ↔
    (∀ j, base (fun r => j (.inl r)) →
      (∀ c ∈ chains, ∀ r ∈ c.2 :: c.1, realizes j r) →
      (∀ c ∈ chains, inclusion j (c.1.map symbol) (symbol c.2)) →
      consequence (fun r => j (.inl r))) := by
  constructor
  · intro source j hb hj hc
    exact source _ hb (fun c hm => (inclusion_symbols_on j c.1 c.2 (hj c hm)).mpr (hc c hm))
  · intro normalized i hb hc
    apply normalized (expand i) hb
    · intro c hm r hr x y
      exact eval_symbol (expand i) (expand_bridges i) r x y
    · intro c hm
      exact (inclusion_symbols (expand i) (expand_bridges i) c.1 c.2).mp (hc c hm)

/-- Lifting the fixed source endpoint into the central variable preserves the
negative assertion, including interpretations in which individual names alias. -/
theorem negative_role_guard (relation : D → D → Prop) (a b : D) :
    (¬ relation a b) ↔ (∀ x, relation x b → x ≠ a) := by
  constructor
  · intro negative x edge equal
    subst x
    exact negative edge
  · intro guarded edge
    exact guarded a edge rfl

/-- Centering a binary chain on its shared endpoint is only a permutation of
universally quantified variables; no role edge or orientation is changed. -/
theorem centered_binary_chain (r s t : D → D → Prop) :
    (∀ a b c, r a b → s b c → t a c) ↔
      (∀ x y z, r y x → s x z → t y z) := by
  constructor
  · intro chain x y z
    exact chain y x z
  · intro chain a b c
    exact chain b a c

#print axioms negative_role_guard
#print axioms centered_binary_chain
#print axioms consequences_preserved
#print axioms theory_consequences_preserved
end ContextCalculus.InverseRoleChainNormalization
