import ContextCalculus.SRI.GoodTypes

/-!
# The v1.7.0 normal form: SHIQ clauses (stage C1, design section 1)

`docs/V1.7.0-C1-SHIQ-DESIGN.md`. The `SRI` normal form plus qualified
number restrictions `a ⊑ ≥n R.b` (`atLeast`) and `a ⊑ ≤n R.b`
(`atMost`). Role terms, interpretations, `Interp.rt` and `Interp.path`
come from `SRI`.

Counting follows the OWL model: `≥n R.b` holds at `x` when a
duplicate-free list of `n` elements are `R`-successors of `x` in `b`;
`≤n R.b` holds at `x` when every duplicate-free list of such successors
has length at most `n`.

`ofSRI` embeds the `SRI` clauses with the same meaning
(`entailsSub_ofSRI`). `sriPart` keeps the clauses without counting; the
role hierarchy `RoleLe` and the closed types `Closed` of an `SRIQ`
ontology are those of its `sriPart`, so the `SRI` lemmas about them
apply unchanged.
-/

namespace ContextCalculus.SRIQ

open ContextCalculus.SRI (RoleT Interp)

/-- Normalised SHIQ clauses over concept names `CName` and role names `Role`. -/
inductive Clause (CName Role : Type) where
  /-- `⊓ body ⊑ ⊔ head` (empty body: `⊤`, empty head: `⊥`). -/
  | gci (body head : List CName)
  /-- `a ⊑ ∃R.b`. -/
  | exRight (a : CName) (R : RoleT Role) (b : CName)
  /-- `a ⊑ ∀R.b`. -/
  | allRight (a : CName) (R : RoleT Role) (b : CName)
  /-- `a ⊑ ≥n R.b`. -/
  | atLeast (a : CName) (n : Nat) (R : RoleT Role) (b : CName)
  /-- `a ⊑ ≤n R.b`. -/
  | atMost (a : CName) (n : Nat) (R : RoleT Role) (b : CName)
  /-- `R₁ ∘ … ∘ Rₙ ⊑ S`. -/
  | chain (body : List (RoleT Role)) (sup : RoleT Role)
deriving DecidableEq, Repr

abbrev Ontology (CName Role : Type) := List (Clause CName Role)

variable {D CName Role : Type}

/-- Tarskian satisfaction of a clause. -/
def satClause (I : Interp D CName Role) : Clause CName Role → Prop
  | .gci body head => ∀ x, (∀ a ∈ body, I.c a x) → ∃ b ∈ head, I.c b x
  | .exRight a R b => ∀ x, I.c a x → ∃ y, I.rt R x y ∧ I.c b y
  | .allRight a R b => ∀ x, I.c a x → ∀ y, I.rt R x y → I.c b y
  | .atLeast a n R b => ∀ x, I.c a x →
      ∃ l : List D, l.Nodup ∧ l.length = n ∧ ∀ y ∈ l, I.rt R x y ∧ I.c b y
  | .atMost a n R b => ∀ x, I.c a x →
      ∀ l : List D, l.Nodup → (∀ y ∈ l, I.rt R x y ∧ I.c b y) → l.length ≤ n
  | .chain body S => ∀ x y, I.path body x y → I.rt S x y

/-- `I` models the ontology. -/
def models (I : Interp D CName Role) (O : Ontology CName Role) : Prop :=
  ∀ cl ∈ O, satClause I cl

/-- Subsumption between concept names, over nonempty domains as
`SRI.EntailsSub`. -/
def EntailsSub (O : Ontology CName Role) (a b : CName) : Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role),
    models I O → ∀ x, I.c a x → I.c b x

/-! ## The embedding of `SRI` -/

/-- An `SRI` clause as an `SRIQ` clause. -/
def ofSRI : SRI.Clause CName Role → Clause CName Role
  | .gci body head => .gci body head
  | .exRight a R b => .exRight a R b
  | .allRight a R b => .allRight a R b
  | .chain body S => .chain body S

/-- The `SRI` clause of an `SRIQ` clause without counting. -/
def toSRI : Clause CName Role → Option (SRI.Clause CName Role)
  | .gci body head => some (.gci body head)
  | .exRight a R b => some (.exRight a R b)
  | .allRight a R b => some (.allRight a R b)
  | .atLeast .. => none
  | .atMost .. => none
  | .chain body S => some (.chain body S)

/-- The clauses without counting. -/
def sriPart (O : Ontology CName Role) : SRI.Ontology CName Role :=
  O.filterMap toSRI

theorem toSRI_ofSRI (cl : SRI.Clause CName Role) : toSRI (ofSRI cl) = some cl := by
  cases cl <;> rfl

theorem satClause_ofSRI (I : Interp D CName Role) (cl : SRI.Clause CName Role) :
    satClause I (ofSRI cl) ↔ SRI.satClause I cl := by
  cases cl <;> exact Iff.rfl

theorem satClause_toSRI (I : Interp D CName Role) {cl : Clause CName Role}
    {cl' : SRI.Clause CName Role} (h : toSRI cl = some cl') :
    satClause I cl ↔ SRI.satClause I cl' := by
  cases cl <;> simp only [toSRI, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact Iff.rfl

theorem models_ofSRI (I : Interp D CName Role) (O : SRI.Ontology CName Role) :
    models I (O.map ofSRI) ↔ SRI.models I O := by
  simp only [models, SRI.models, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, satClause_ofSRI]

/-- **Embedding.** `SRI` subsumption is `SRIQ` subsumption of the embedded
clauses. -/
theorem entailsSub_ofSRI (O : SRI.Ontology CName Role) (a b : CName) :
    SRI.EntailsSub O a b ↔ EntailsSub (O.map ofSRI) a b := by
  unfold SRI.EntailsSub EntailsSub
  simp only [models_ofSRI]

theorem sriPart_ofSRI (O : SRI.Ontology CName Role) : sriPart (O.map ofSRI) = O := by
  simp only [sriPart, List.filterMap_map, Function.comp_def, toSRI_ofSRI, List.filterMap_some]

theorem mem_sriPart {O : Ontology CName Role} {cl' : SRI.Clause CName Role} :
    cl' ∈ sriPart O ↔ ofSRI cl' ∈ O := by
  simp only [sriPart, List.mem_filterMap]
  constructor
  · rintro ⟨cl, hcl, he⟩
    cases cl <;> simp only [toSRI, Option.some.injEq, reduceCtorEq] at he <;> subst he <;>
      exact hcl
  · intro h
    exact ⟨_, h, toSRI_ofSRI cl'⟩

theorem models_sriPart {I : Interp D CName Role} {O : Ontology CName Role} (h : models I O) :
    SRI.models I (sriPart O) := by
  intro cl' hcl'
  rw [← satClause_ofSRI]
  exact h _ (mem_sriPart.1 hcl')

/-! ## Role hierarchy and closed types -/

/-- `R ⊑* S` in the role hierarchy of `O`. -/
def RoleLe (O : Ontology CName Role) : RoleT Role → RoleT Role → Prop :=
  SRI.RoleLe (sriPart O)

/-- Every gci whose body holds has a head name that holds. -/
def Closed (O : Ontology CName Role) (t : Finset CName) : Prop :=
  SRI.Closed (sriPart O) t

/-- The ontology has role chains of length one only (no transitivity;
section 5 removes it first). -/
def IsALCHIQ (O : Ontology CName Role) : Prop :=
  ∀ body S, Clause.chain body S ∈ O → body.length = 1

theorem isALCHI_sriPart {O : Ontology CName Role} (h : IsALCHIQ O) :
    SRI.IsALCHI (sriPart O) :=
  fun body S hcl => h body S (mem_sriPart.1 hcl)

theorem isALCHIQ_ofSRI {O : SRI.Ontology CName Role} (h : SRI.IsALCHI O) :
    IsALCHIQ (O.map ofSRI) := by
  intro body S hcl
  obtain ⟨cl, hcl0, he⟩ := List.mem_map.1 hcl
  cases cl <;> simp only [ofSRI, reduceCtorEq, Clause.chain.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h _ _ hcl0

theorem roleLe_single {O : Ontology CName Role} {R S : RoleT Role}
    (h : Clause.chain [R] S ∈ O) : RoleLe O R S :=
  Relation.ReflTransGen.single (Or.inl (mem_sriPart.2 h))

theorem roleLe_flip {O : Ontology CName Role} {R S : RoleT Role} (h : RoleLe O R S) :
    RoleLe O R.flip S.flip :=
  SRI.roleLe_flip h

theorem RoleLe.trans {O : Ontology CName Role} {R S T : RoleT Role} (h1 : RoleLe O R S)
    (h2 : RoleLe O S T) : RoleLe O R T :=
  Relation.ReflTransGen.trans h1 h2

theorem roleLe_sound {I : Interp D CName Role} {O : Ontology CName Role} (hI : models I O)
    {R S : RoleT Role} (h : RoleLe O R S) (x y : D) : I.rt R x y → I.rt S x y := by
  induction h generalizing x y with
  | refl => exact id
  | tail _ hst ih =>
    intro hxy
    have hS := ih x y hxy
    rcases hst with h1 | h2
    · exact (models_sriPart hI) _ h1 x y ⟨y, hS, rfl⟩
    · have := (models_sriPart hI) _ h2 y x ⟨x, (Interp.rt_flip I _ y x).2 hS, rfl⟩
      exact (Interp.rt_flip I _ y x).1 this

theorem closed_iff {O : Ontology CName Role} {t : Finset CName} :
    Closed O t ↔ ∀ body head, Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ t) →
      ∃ b ∈ head, b ∈ t := by
  unfold Closed SRI.Closed
  exact forall_congr' fun body => forall_congr' fun head => by
    rw [mem_sriPart]; rfl

end ContextCalculus.SRIQ

#print axioms ContextCalculus.SRIQ.entailsSub_ofSRI
#print axioms ContextCalculus.SRIQ.roleLe_sound
