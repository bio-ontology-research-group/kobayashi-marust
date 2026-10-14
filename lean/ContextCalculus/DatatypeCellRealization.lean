import Mathlib.Logic.Basic

/-! Realization of abstract datatype labels by concrete data values.

The native completion bridge treats each admitted datatype symbol as an atomic
concept. A completion graph labels a data node with a set `S` of such symbols;
the OWL model needs a concrete value instead. This file proves the semantic
step used by the bridge-TBox datatype certificate (`anyURI`, `xsd:double`
values and ranges, IEEE facet intervals, `rdfs:Literal`):

* if the chosen value lies in every symbol of `S`, and lies in no
  body-sensitive symbol outside `S`, then every datatype formula whose
  negative atoms are all body-sensitive keeps its truth value from the label
  to the value (`formula_transfer`);
* two sibling nodes that the graph keeps distinct can be realized by distinct
  values whenever the realizing cell has two elements (`two_distinct_realizers`).

Membership decisions for concrete datatypes (IEEE rank intervals, partition
disjointness, literal parsing) and the exact cell counts are computed by the
Rust datatype module and checked against its relation-clause evidence; they
are not certified here. -/
namespace ContextCalculus.DatatypeCellRealization
universe u v

/-- Datatype formulas in negation normal form over atomic symbols. -/
inductive Formula (D : Type u) where
  | pos : D → Formula D
  | neg : D → Formula D
  | conj : Formula D → Formula D → Formula D
  | disj : Formula D → Formula D → Formula D

def eval {D : Type u} (truth : D → Prop) : Formula D → Prop
  | .pos d => truth d
  | .neg d => ¬ truth d
  | .conj p q => eval truth p ∧ eval truth q
  | .disj p q => eval truth p ∨ eval truth q

/-- Every negative atom of the formula satisfies `sensitive`. -/
def NegativesIn {D : Type u} (sensitive : D → Prop) : Formula D → Prop
  | .pos _ => True
  | .neg d => sensitive d
  | .conj p q => NegativesIn sensitive p ∧ NegativesIn sensitive q
  | .disj p q => NegativesIn sensitive p ∧ NegativesIn sensitive q

/-- The certificate's per-value obligation: `value` realizes label `S`. -/
def Realizes {D : Type u} {V : Type v} (sem : D → V → Prop)
    (sensitive : D → Prop) (S : D → Prop) (value : V) : Prop :=
  (∀ d, S d → sem d value) ∧ (∀ d, sensitive d → sem d value → S d)

theorem formula_transfer {D : Type u} {V : Type v} (sem : D → V → Prop)
    (sensitive : D → Prop) (S : D → Prop) (value : V)
    (realizes : Realizes sem sensitive S value) :
    ∀ φ : Formula D, NegativesIn sensitive φ →
      eval S φ → eval (fun d => sem d value) φ := by
  intro φ
  induction φ with
  | pos d => intro _ h; exact realizes.1 d h
  | neg d => intro hs h hv; exact h (realizes.2 d hs hv)
  | conj p q ihp ihq =>
      intro hs h; exact ⟨ihp hs.1 h.1, ihq hs.2 h.2⟩
  | disj p q ihp ihq =>
      intro hs h
      rcases h with h | h
      · exact Or.inl (ihp hs.1 h)
      · exact Or.inr (ihq hs.2 h)

/-- A body-sensitive symbol keeps its exact truth value under realization. -/
theorem sensitive_exact {D : Type u} {V : Type v} (sem : D → V → Prop)
    (sensitive : D → Prop) (S : D → Prop) (value : V)
    (realizes : Realizes sem sensitive S value) (d : D) (hd : sensitive d) :
    sem d value ↔ S d :=
  ⟨realizes.2 d hd, realizes.1 d⟩

/-- A realizing value that avoids every literal symbol keeps each value
concept false on a node that the label does not mark with it. -/
theorem fresh_value_avoids_literals {V : Type v} (literals : List V) (value : V)
    (fresh : value ∉ literals) (w : V) (hw : w ∈ literals) : value ≠ w := by
  intro h; exact fresh (h ▸ hw)

/-- Two distinct realizers exist when the cell has two distinct elements;
the bridge admits at most two forced-distinct data siblings. -/
theorem two_distinct_realizers {V : Type v} (cell : V → Prop)
    (a b : V) (ha : cell a) (hb : cell b) (hab : a ≠ b) :
    ∃ f : Bool → V, (∀ i, cell (f i)) ∧ Function.Injective f := by
  refine ⟨fun i => if i then a else b, ?_, ?_⟩
  · intro i; cases i
    · exact hb
    · exact ha
  · intro i j hij
    cases i <;> cases j
    · rfl
    · exact absurd hij.symm hab
    · exact absurd hij hab
    · rfl

/-- `rdfs:Literal` holds of every data value, so a positive occurrence is
always realized and only a negative occurrence could change truth. -/
theorem top_positive {D : Type u} {V : Type v} (sem : D → V → Prop)
    (top : D) (htop : ∀ value, sem top value) (value : V) : sem top value :=
  htop value

/-- Cell realization. When every relevant range either contains the cell `C`
or is disjoint from it, a value of `C` decides every range exactly as the
inclusion closure of `C` does. This is the bridge's atomic-cell path. -/
theorem atomic_cell_decides {D : Type u} {V : Type v} (sem : D → V → Prop)
    (cell : V → Prop) (relevant : D → Prop)
    (atomic : ∀ d, relevant d → (∀ x, cell x → sem d x) ∨ (∀ x, cell x → ¬ sem d x))
    (value : V) (hv : cell value) (d : D) (hd : relevant d) :
    sem d value ↔ (∀ x, cell x → sem d x) := by
  constructor
  · intro h
    rcases atomic d hd with inc | dis
    · exact inc
    · exact absurd h (dis value hv)
  · intro inc; exact inc value hv

/-- A cover clause `A → C1 ∨ … ∨ Cm` is valid exactly when `A` is contained in
the union of its cells (the frontend emits each range's exact cell cover). -/
theorem cell_cover_valid {D : Type u} {V : Type v} (sem : D → V → Prop)
    (range : D) (cells : List D)
    (covered : ∀ x, sem range x → ∃ c ∈ cells, sem c x) (value : V) (h : sem range value) :
    ∃ c ∈ cells, sem c value := covered value h

end ContextCalculus.DatatypeCellRealization

#print axioms ContextCalculus.DatatypeCellRealization.formula_transfer
#print axioms ContextCalculus.DatatypeCellRealization.sensitive_exact
#print axioms ContextCalculus.DatatypeCellRealization.fresh_value_avoids_literals
#print axioms ContextCalculus.DatatypeCellRealization.two_distinct_realizers
#print axioms ContextCalculus.DatatypeCellRealization.top_positive
#print axioms ContextCalculus.DatatypeCellRealization.atomic_cell_decides
#print axioms ContextCalculus.DatatypeCellRealization.cell_cover_valid
