import ContextCalculus.TwoSortedDL

/-!
# Boolean data ranges (`docs/DATATYPES.md`, "Boolean data ranges and ordered cells")

The frontend names every complex data range (`__dt__c__<text>`). For a name
with Boolean structure (`DataIntersectionOf`, `DataUnionOf`,
`DataComplementOf`) `frontend/datatypes/vocabulary.rs` (`expand`) adds the
operand names to the vocabulary, closed transitively, and emits the
definitional clauses

* `I → Mᵢ` (for every member `Mᵢ ≠ rdfs:Literal`) and
  `M₁ ∧ … ∧ Mₖ → I` (the `rdfs:Literal` members left out of the body) for
  `I = DataIntersectionOf(M₁ … Mₖ)`;
* `Mᵢ → U` and the cover `U → M₁ ∨ … ∨ Mₖ` for `U = DataUnionOf(M₁ … Mₖ)`;
* `C ∧ A → ⊥` and the excluded middle `→ C ∨ A` for
  `C = DataComplementOf(A)`, and `C → ⊥` for `C = DataComplementOf(rdfs:Literal)`.

(Where the oracle already decides `Mᵢ ⊑ U` or `C ⊓ A = ∅`, `expand` leaves
that clause to the pairwise relation generator, which emits the same clause;
the clause set is the same.)

We work with the labels of one element: `L : DN → Prop` says which names
hold at a data node of a clause model (`J.dcon · n`) or at a value of the
OWL reading (`den · y`). The operands are atomic data ranges
(`TwoSortedDL.DRange`: `⊤` or a name).

* `defClauses_iff`: the definitional clauses of one name hold at an element
  iff the name holds there exactly when the Boolean combination of its
  operands does.
* `labels_agree` (the structural induction): two label sets that satisfy
  the definitions and agree on the names without Boolean structure agree
  on every name, provided the definitions are well founded (`Ranked`; the
  frontend's names are syntax trees, so an operand is a proper subterm).
  Hence a value realizes a label set iff it realizes its atomic part
  (`realizes_of_atomic`).
* `extend_defSat` / `extend_agrees` (the converse direction): every
  interpretation of the atomic names extends to one that satisfies the
  definitions (and with it the clauses); `owl_satisfies_clauses`: the OWL
  datatype map, which interprets each Boolean range as the corresponding
  combination of its operands (OWL 2 Direct Semantics, Table 4), satisfies
  the clauses at every value.

Core Lean only.
-/

namespace ContextCalculus.DataRangeBoolean
open ContextCalculus.TwoSortedDL

variable {DN : Type}

/-- The Boolean structure of a complex range name over its operands. -/
inductive BDef (DN : Type) where
  | inter (ms : List (DRange DN))
  | union (ms : List (DRange DN))
  | compl (m : DRange DN)

/-- Truth of an operand under the labels `L` (`⊤` holds everywhere). -/
def lab (L : DN → Prop) : DRange DN → Prop
  | .top => True
  | .name d => L d

/-- The Boolean combination of the operands under `L`. -/
def BDef.eval (L : DN → Prop) : BDef DN → Prop
  | .inter ms => ∀ m ∈ ms, lab L m
  | .union ms => ∃ m ∈ ms, lab L m
  | .compl m => ¬ lab L m

/-- The operand names. -/
def BDef.names : BDef DN → List DN
  | .inter ms => ms.filterMap (fun | .top => none | .name a => some a)
  | .union ms => ms.filterMap (fun | .top => none | .name a => some a)
  | .compl .top => []
  | .compl (.name a) => [a]

def isTop : DRange DN → Bool
  | .top => true
  | .name _ => false

/-- A clause over data concept names at one element: the conjunction of the
body implies the disjunction of the head. -/
structure LClause (DN : Type) where
  body : List (DRange DN)
  head : List (DRange DN)

def LClause.holds (L : DN → Prop) (c : LClause DN) : Prop :=
  (∀ m ∈ c.body, lab L m) → ∃ m ∈ c.head, lab L m

/-- The definitional clauses `expand` emits for the name `d` with structure
`b`. -/
def defClauses (d : DN) : BDef DN → List (LClause DN)
  | .inter ms =>
    (ms.filter (fun m => !isTop m)).map (fun m => ⟨[.name d], [m]⟩) ++
      [⟨ms.filter (fun m => !isTop m), [.name d]⟩]
  | .union ms => ms.map (fun m => ⟨[m], [.name d]⟩) ++ [⟨[.name d], ms⟩]
  | .compl .top => [⟨[.name d], []⟩]
  | .compl (.name a) => [⟨[.name d, .name a], []⟩, ⟨[], [.name d, .name a]⟩]

theorem forall_filter_notTop (L : DN → Prop) (ms : List (DRange DN)) :
    (∀ m ∈ ms.filter (fun m => !isTop m), lab L m) ↔ ∀ m ∈ ms, lab L m := by
  constructor
  · intro h m hm
    cases m with
    | top => exact trivial
    | name a => exact h _ (List.mem_filter.2 ⟨hm, rfl⟩)
  · intro h m hm
    exact h m (List.mem_filter.1 hm).1

/-- **The definitional clauses are the Boolean structure.** -/
theorem defClauses_iff (L : DN → Prop) (d : DN) (b : BDef DN) :
    (∀ c ∈ defClauses d b, c.holds L) ↔ (L d ↔ b.eval L) := by
  cases b with
  | inter ms =>
    simp only [defClauses, List.mem_append, List.mem_map, List.mem_singleton]
    constructor
    · intro h
      constructor
      · intro hd
        refine (forall_filter_notTop L ms).1 fun m hm => ?_
        obtain ⟨m', hm', hl⟩ := h ⟨[.name d], [m]⟩ (Or.inl ⟨m, hm, rfl⟩)
          (fun x hx => by simp at hx; subst hx; exact hd)
        simp at hm'; subst hm'; exact hl
      · intro he
        obtain ⟨m', hm', hl⟩ := h _ (Or.inr rfl) ((forall_filter_notTop L ms).2 he)
        simp at hm'; subst hm'; exact hl
    · intro h c hc
      rcases hc with ⟨m, hm, rfl⟩ | rfl
      · intro hb
        have hd : L d := hb (.name d) (by simp)
        exact ⟨m, by simp, (forall_filter_notTop L ms).2 (h.1 hd) m hm⟩
      · intro hb
        exact ⟨.name d, by simp, h.2 ((forall_filter_notTop L ms).1 hb)⟩
  | union ms =>
    simp only [defClauses, List.mem_append, List.mem_map, List.mem_singleton]
    constructor
    · intro h
      constructor
      · intro hd
        exact h ⟨[.name d], ms⟩ (Or.inr rfl) (fun x hx => by simp at hx; subst hx; exact hd)
      · intro ⟨m, hm, hl⟩
        obtain ⟨m', hm', hl'⟩ := h ⟨[m], [.name d]⟩ (Or.inl ⟨m, hm, rfl⟩)
          (fun x hx => by simp at hx; subst hx; exact hl)
        simp at hm'; subst hm'; exact hl'
    · intro h c hc
      rcases hc with ⟨m, hm, rfl⟩ | rfl
      · intro hb
        exact ⟨.name d, by simp, h.2 ⟨m, hm, hb m (by simp)⟩⟩
      · intro hb
        exact h.1 (hb (.name d) (by simp))
  | compl m =>
    cases m with
    | top =>
      simp only [defClauses, List.mem_singleton, BDef.eval, lab]
      constructor
      · intro h
        refine ⟨fun hd => ?_, fun hn => absurd trivial hn⟩
        obtain ⟨_, hm, _⟩ := h _ rfl (fun x hx => by simp at hx; subst hx; exact hd)
        simp at hm
      · intro h c hc
        subst hc
        intro hb
        exact absurd trivial (h.1 (hb (.name d) (by simp)))
    | name a =>
      simp only [defClauses, List.mem_cons, BDef.eval, lab]
      constructor
      · intro h
        constructor
        · intro hd ha
          obtain ⟨_, hm, _⟩ := h _ (Or.inl rfl) (fun x hx => by
            simp at hx; rcases hx with rfl | rfl
            · exact hd
            · exact ha)
          simp at hm
        · intro hna
          obtain ⟨x, hx, hl⟩ := h _ (Or.inr (Or.inl rfl)) (fun x hx => by simp at hx)
          simp at hx
          rcases hx with rfl | rfl
          · exact hl
          · exact absurd hl hna
      · intro h c hc
        rcases hc with rfl | rfl | hc
        · intro hb
          exact absurd (hb (.name a) (by simp)) (h.1 (hb (.name d) (by simp)))
        · intro _
          by_cases ha : L a
          · exact ⟨.name a, by simp, ha⟩
          · exact ⟨.name d, by simp, h.2 ha⟩
        · simp at hc

/-! ## Definitions and their well-foundedness -/

/-- `L` interprets every Boolean name as the combination of its operands.
`defs d = some b` when `d` has Boolean structure `b`. -/
def DefSatAt (defs : DN → Option (BDef DN)) (L : DN → Prop) : Prop :=
  ∀ d b, defs d = some b → (L d ↔ b.eval L)

/-- `L` satisfies every definitional clause. -/
def ClausesAt (defs : DN → Option (BDef DN)) (L : DN → Prop) : Prop :=
  ∀ d b, defs d = some b → ∀ c ∈ defClauses d b, c.holds L

theorem clausesAt_iff (defs : DN → Option (BDef DN)) (L : DN → Prop) :
    ClausesAt defs L ↔ DefSatAt defs L :=
  ⟨fun h d b hb => (defClauses_iff L d b).1 (h d b hb),
   fun h d b hb => (defClauses_iff L d b).2 (h d b hb)⟩

/-- Every operand of a Boolean name has a smaller rank. -/
def Ranked (defs : DN → Option (BDef DN)) (rank : DN → Nat) : Prop :=
  ∀ d b, defs d = some b → ∀ a ∈ b.names, rank a < rank d

theorem mem_names_inter {ms : List (DRange DN)} {a : DN} :
    a ∈ (BDef.inter ms).names ↔ DRange.name a ∈ ms := by
  simp only [BDef.names, List.mem_filterMap]
  constructor
  · intro ⟨m, hm, he⟩
    cases m with
    | top => simp at he
    | name a' => simp at he; subst he; exact hm
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_names_union {ms : List (DRange DN)} {a : DN} :
    a ∈ (BDef.union ms).names ↔ DRange.name a ∈ ms := by
  simp only [BDef.names, List.mem_filterMap]
  constructor
  · intro ⟨m, hm, he⟩
    cases m with
    | top => simp at he
    | name a' => simp at he; subst he; exact hm
  · intro h; exact ⟨_, h, rfl⟩

/-- The combination only depends on the labels of the operand names. -/
theorem BDef.eval_congr {L₁ L₂ : DN → Prop} (b : BDef DN)
    (h : ∀ a ∈ b.names, L₁ a ↔ L₂ a) : b.eval L₁ ↔ b.eval L₂ := by
  have hlab : ∀ m : DRange DN, (∀ a, m = .name a → (L₁ a ↔ L₂ a)) → (lab L₁ m ↔ lab L₂ m) := by
    intro m hm
    cases m with
    | top => exact Iff.rfl
    | name a => exact hm a rfl
  cases b with
  | inter ms =>
    exact forall_congr' fun m => imp_congr_right fun hm =>
      hlab m fun a he => h a (mem_names_inter.2 (he ▸ hm))
  | union ms =>
    exact exists_congr fun m => and_congr_right fun hm =>
      hlab m fun a he => h a (mem_names_union.2 (he ▸ hm))
  | compl m =>
    exact not_congr (hlab m fun a he => h a (by subst he; simp [BDef.names]))

/-- **Structural induction.** Two label sets that satisfy the definitions
and agree on the atomic names of a scope closed under operands agree on the
whole scope. -/
theorem labels_agree (defs : DN → Option (BDef DN)) (rank : DN → Nat)
    (hr : Ranked defs rank) (scope : DN → Prop)
    (hclosed : ∀ d b, scope d → defs d = some b → ∀ a ∈ b.names, scope a)
    {L₁ L₂ : DN → Prop} (h₁ : DefSatAt defs L₁) (h₂ : DefSatAt defs L₂)
    (hatom : ∀ d, scope d → defs d = none → (L₁ d ↔ L₂ d)) :
    ∀ d, scope d → (L₁ d ↔ L₂ d) := by
  suffices H : ∀ k d, rank d < k → scope d → (L₁ d ↔ L₂ d) from
    fun d hd => H (rank d + 1) d (Nat.lt_succ_self _) hd
  intro k
  induction k with
  | zero => intro d h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro d hk hd
    cases hb : defs d with
    | none => exact hatom d hd hb
    | some b =>
      rw [h₁ d b hb, h₂ d b hb]
      exact BDef.eval_congr b fun a ha =>
        ih a (Nat.lt_of_lt_of_le (hr d b hb a ha) (Nat.le_of_lt_succ hk)) (hclosed d b hd hb a ha)

/-- A value realizes the label set of a node iff it realizes its atomic
part: the node's labels satisfy the clauses, the value's labels the OWL
definitions. -/
theorem realizes_of_atomic {Val : Type} (defs : DN → Option (BDef DN)) (rank : DN → Nat)
    (hr : Ranked defs rank) (den : DN → Val → Prop) (hden : ∀ y, DefSatAt defs (fun d => den d y))
    (L : DN → Prop) (hL : ClausesAt defs L) (y : Val)
    (hatom : ∀ d, defs d = none → (L d ↔ den d y)) : ∀ d, L d ↔ den d y :=
  fun d => labels_agree defs rank hr (fun _ => True) (fun _ _ _ _ _ _ => trivial)
    ((clausesAt_iff defs L).1 hL) (hden y) (fun d _ hd => hatom d hd) d trivial

/-! ## The converse: every interpretation of the atomic names extends -/

section Extend
variable (defs : DN → Option (BDef DN)) (rank : DN → Nat) (A : DN → Prop)

/-- Unfolding the definitions `k` times over the atomic labels `A`. -/
def unfold : Nat → DN → Prop
  | 0 => A
  | k + 1 => fun d => match defs d with
    | none => A d
    | some b => b.eval (unfold k)

/-- The extension of `A`: each name unfolded once more than its rank. -/
def extend (d : DN) : Prop := unfold defs A (rank d + 1) d

variable {defs rank}

theorem unfold_stable (hr : Ranked defs rank) :
    ∀ k j d, rank d < k → rank d < j → (unfold defs A k d ↔ unfold defs A j d) := by
  intro k
  induction k with
  | zero => intro j d h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro j d hk hj
    cases j with
    | zero => exact absurd hj (Nat.not_lt_zero _)
    | succ j =>
      simp only [unfold]
      cases hb : defs d with
      | none => exact Iff.rfl
      | some b =>
        exact BDef.eval_congr b fun a ha =>
          ih j a (Nat.lt_of_lt_of_le (hr d b hb a ha) (Nat.le_of_lt_succ hk))
            (Nat.lt_of_lt_of_le (hr d b hb a ha) (Nat.le_of_lt_succ hj))

/-- The extension satisfies the definitions. -/
theorem extend_defSat (hr : Ranked defs rank) : DefSatAt defs (extend defs rank A) := by
  intro d b hb
  show unfold defs A (rank d + 1) d ↔ _
  simp only [unfold, hb]
  exact BDef.eval_congr b fun a ha =>
    unfold_stable A hr (rank d) (rank a + 1) a (hr d b hb a ha) (Nat.lt_succ_self _)

/-- The extension agrees with `A` on the atomic names. -/
theorem extend_agrees (d : DN) (hd : defs d = none) : extend defs rank A d ↔ A d := by
  show unfold defs A (rank d + 1) d ↔ _
  simp only [unfold, hd]

/-- **Converse.** Every interpretation `A` of the atomic names (at every
element of any data domain) extends to an interpretation that satisfies all
definitional clauses and agrees with `A` on the atomic names; by
`labels_agree` it is the only one. -/
theorem extends_to_clause_model {D : Type} (hr : Ranked defs rank) (A : DN → D → Prop) :
    ∃ dcon : DN → D → Prop, (∀ y, ClausesAt defs (fun d => dcon d y)) ∧
      ∀ d, defs d = none → ∀ y, (dcon d y ↔ A d y) :=
  ⟨fun d y => extend defs rank (fun a => A a y) d,
   fun y => (clausesAt_iff defs _).2 (extend_defSat (fun a => A a y) hr),
   fun d hd y => extend_agrees (fun a => A a y) d hd⟩

end Extend

/-- The OWL datatype map interprets every Boolean range as the combination of
its operands; such a map satisfies the definitional clauses at every value. -/
theorem owl_satisfies_clauses {Val : Type} (defs : DN → Option (BDef DN)) (den : DN → Val → Prop)
    (hden : ∀ y, DefSatAt defs (fun d => den d y)) : ∀ y, ClausesAt defs (fun d => den d y) :=
  fun y => (clausesAt_iff defs _).2 (hden y)

/-- In every clause model (`J.dcon` satisfying the clauses at every node) each
Boolean name holds at a node exactly when the combination of its operands
does. -/
theorem clause_model_boolean {D : Type} (defs : DN → Option (BDef DN)) (dcon : DN → D → Prop)
    (h : ∀ n, ClausesAt defs (fun d => dcon d n)) :
    ∀ d b, defs d = some b → ∀ n, dcon d n ↔ b.eval (fun a => dcon a n) :=
  fun d b hb n => (clausesAt_iff defs _).1 (h n) d b hb

end ContextCalculus.DataRangeBoolean
