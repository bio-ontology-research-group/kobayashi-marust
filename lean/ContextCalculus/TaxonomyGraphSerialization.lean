/-! A taxonomy consumer closes emitted subclass edges transitively. Replacing
expanded non-reflexive reachability pairs by the original non-reflexive graph
edges preserves that closure, also after mapping vertices to public names.
Consistency, unsatisfiability and dropped-axiom fields are unchanged by the
Rust encoder. This proves representation preservation, not a new reasoning
route or the correctness of the source graph itself. -/
namespace ContextCalculus.TaxonomyGraphSerialization

inductive Reach {A : Type} (edge : A → A → Prop) : A → A → Prop where
  | refl (a) : Reach edge a a
  | step {a b c} : edge a b → Reach edge b c → Reach edge a c

variable {A B : Type} {edge other : A → A → Prop}

theorem reach_trans {a b c : A} (ab : Reach edge a b) (bc : Reach edge b c) :
    Reach edge a c := by
  induction ab with
  | refl => exact bc
  | step first _ ih => exact .step first (ih bc)

theorem replace_edges (replacement : ∀ a b, edge a b → Reach other a b)
    {a b : A} (path : Reach edge a b) : Reach other a b := by
  induction path with
  | refl x => exact .refl x
  | step first _ ih => exact reach_trans (replacement _ _ first) ih

def NonReflexive (edge : A → A → Prop) (a b : A) : Prop := edge a b ∧ a ≠ b

theorem omit_self_edges {a b : A} :
    Reach (NonReflexive edge) a b ↔ Reach edge a b := by
  classical
  constructor
  · exact replace_edges (fun _ _ h => .step h.1 (.refl _))
  · intro path
    induction path with
    | refl x => exact .refl x
    | @step x y z first _ ih =>
      by_cases same : x = y
      · subst y
        exact ih
      · exact .step ⟨first, same⟩ ih

def Image (edge : A → A → Prop) (name : A → B) (x y : B) : Prop :=
  ∃ a b, edge a b ∧ name a = x ∧ name b = y

theorem map_reach (name : A → B) {a b : A} (path : Reach edge a b) :
    Reach (Image edge name) (name a) (name b) := by
  induction path with
  | refl x => exact .refl _
  | @step x y z first _ ih => exact .step ⟨x, y, first, rfl, rfl⟩ ih

/-- This includes arbitrary name aliases: both representations have the same
closure under the consumer's interpretation of the names. -/
theorem graph_encoding_same_closure (name : A → B) {x y : B} :
    Reach (Image (NonReflexive (Reach edge)) name) x y ↔
    Reach (Image (NonReflexive edge) name) x y := by
  constructor
  · apply replace_edges
    intro u v h
    obtain ⟨a, b, path, ha, hb⟩ := h
    subst u
    subst v
    exact map_reach name (omit_self_edges.mpr path.1)
  · apply replace_edges
    intro u v h
    obtain ⟨a, b, direct, ha, hb⟩ := h
    exact .step ⟨a, b, ⟨.step direct.1 (.refl _), direct.2⟩, ha, hb⟩ (.refl _)

#print axioms reach_trans
#print axioms replace_edges
#print axioms omit_self_edges
#print axioms map_reach
#print axioms graph_encoding_same_closure
end ContextCalculus.TaxonomyGraphSerialization
