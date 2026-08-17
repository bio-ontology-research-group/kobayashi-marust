/-!
# The pure ELC completion calculus used by the Rust worker

This module gives semantics to all normal forms accepted by the cert-off ELC
worker: NF1 through NF7 and reflexive roles.  Its mutually inductive `Sub` and
`Edge` relations state the mathematical closure computed by the worklist in
`engine/src/elcomplete.rs`.

The soundness theorem covers explicit top and bottom, backward bottom
propagation, existential introduction and elimination, role hierarchy,
reflexivity, and role-chain composition.  Executable refinement still requires
proving that the indexed Rust worklist computes exactly these relations.
-/

namespace ContextCalculus.ELCompletion

variable {Concept Role : Type}

/-- Interned EL++ normal forms, corresponding one-for-one to Rust NF1–NF7. -/
inductive Clause (Concept Role : Type) where
  | nf1 (sub sup : Concept)
  | nf2 (left right sup : Concept)
  | nf3 (sub : Concept) (role : Role) (filler : Concept)
  | nf4 (role : Role) (filler sup : Concept)
  | nf5 (sub : Concept)
  | nf6 (sub sup : Role)
  | nf7 (first second sup : Role)
  | reflexive (role : Role)

abbrev Ontology (Concept Role : Type) := List (Clause Concept Role)

/-- A DL interpretation with distinguished top and bottom concepts. -/
structure Interp (Domain Concept Role : Type) (top bottom : Concept) where
  concept : Concept → Domain → Prop
  role : Role → Domain → Domain → Prop
  top_true : ∀ x, concept top x
  bottom_false : ∀ x, ¬ concept bottom x

def satClause {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom) : Clause Concept Role → Prop
  | .nf1 sub sup => ∀ x, I.concept sub x → I.concept sup x
  | .nf2 left right sup =>
      ∀ x, I.concept left x → I.concept right x → I.concept sup x
  | .nf3 sub role filler =>
      ∀ x, I.concept sub x →
        ∃ y, I.role role x y ∧ I.concept filler y
  | .nf4 role filler sup =>
      ∀ x, (∃ y, I.role role x y ∧ I.concept filler y) → I.concept sup x
  | .nf5 sub => ∀ x, I.concept sub x → False
  | .nf6 sub sup => ∀ x y, I.role sub x y → I.role sup x y
  | .nf7 first second sup =>
      ∀ x y z, I.role first x y → I.role second y z → I.role sup x z
  | .reflexive role => ∀ x, I.role role x x

def models {Domain : Type} {top bottom : Concept}
    (I : Interp Domain Concept Role top bottom)
    (O : Ontology Concept Role) : Prop :=
  ∀ clause ∈ O, satClause I clause

/-!
`Sub O A B` represents membership of `B` in the completed label of context
`A`; `Edge O A r B` represents a materialised edge from `A` to the canonical
filler context `B`.  The constructors match the rule blocks in Rust's `run`.
-/
mutual
  inductive Sub (top bottom : Concept) (O : Ontology Concept Role) :
      Concept → Concept → Prop where
    | refl (a : Concept) : Sub top bottom O a a
    | top (a : Concept) : Sub top bottom O a top
    | nf1 {a sub sup : Concept} :
        Sub top bottom O a sub → .nf1 sub sup ∈ O →
        Sub top bottom O a sup
    | nf2 {a left right sup : Concept} :
        Sub top bottom O a left → Sub top bottom O a right →
        .nf2 left right sup ∈ O → Sub top bottom O a sup
    | nf5 {a sub : Concept} :
        Sub top bottom O a sub → .nf5 sub ∈ O →
        Sub top bottom O a bottom
    | nf4 {a target filler sup : Concept} {role : Role} :
        Edge top bottom O a role target →
        Sub top bottom O target filler →
        .nf4 role filler sup ∈ O →
        Sub top bottom O a sup
    | bottomEdge {a target : Concept} {role : Role} :
        Edge top bottom O a role target →
        Sub top bottom O target bottom →
        Sub top bottom O a bottom

  inductive Edge (top bottom : Concept) (O : Ontology Concept Role) :
      Concept → Role → Concept → Prop where
    | nf3 {a sub filler : Concept} {role : Role} :
        Sub top bottom O a sub → .nf3 sub role filler ∈ O →
        Edge top bottom O a role filler
    | nf6 {a target : Concept} {sub sup : Role} :
        Edge top bottom O a sub target → .nf6 sub sup ∈ O →
        Edge top bottom O a sup target
    | nf7 {a middle target : Concept} {first second sup : Role} :
        Edge top bottom O a first middle →
        Edge top bottom O middle second target →
        .nf7 first second sup ∈ O →
        Edge top bottom O a sup target
    | reflexive (a : Concept) {role : Role} :
        .reflexive role ∈ O → Edge top bottom O a role a
end

/-- Every completed label and edge is valid in every model of the normal forms. -/
theorem sub_sound {top bottom : Concept} {O : Ontology Concept Role}
    {Domain : Type} {I : Interp Domain Concept Role top bottom}
    (hI : models I O) {a b : Concept} (h : Sub top bottom O a b) :
    ∀ x, I.concept a x → I.concept b x :=
  Sub.rec
    (motive_1 := fun a b _ => ∀ x, I.concept a x → I.concept b x)
    (motive_2 := fun a role b _ =>
      ∀ x, I.concept a x → ∃ y, I.role role x y ∧ I.concept b y)
    (fun _ _ ha => ha)
    (fun _ x _ => I.top_true x)
    (fun _ hcl ih x hx => (hI _ hcl) x (ih x hx))
    (fun _ _ hcl ihl ihr x hx => (hI _ hcl) x (ihl x hx) (ihr x hx))
    (fun _ hcl ih x hx => False.elim ((hI _ hcl) x (ih x hx)))
    (fun _ _ hcl ihe ihs x hx =>
      let ⟨y, hxy, hy⟩ := ihe x hx
      (hI _ hcl) x ⟨y, hxy, ihs y hy⟩)
    (fun _ _ ihe ihb x hx =>
      let ⟨y, _, hy⟩ := ihe x hx
      False.elim (I.bottom_false y (ihb y hy)))
    (fun _ hcl ihs x hx => (hI _ hcl) x (ihs x hx))
    (fun _ hcl ihe x hx =>
      let ⟨y, hxy, hy⟩ := ihe x hx
      ⟨y, (hI _ hcl) x y hxy, hy⟩)
    (fun _ _ hcl ihe₁ ihe₂ x hx =>
      let ⟨y, hxy, hy⟩ := ihe₁ x hx
      let ⟨z, hyz, hz⟩ := ihe₂ y hy
      ⟨z, (hI _ hcl) x y z hxy hyz, hz⟩)
    (fun _ _ hcl x hx => ⟨x, (hI _ hcl) x, hx⟩)
    h

/-- Edge soundness, exposed separately for executable-refinement lemmas. -/
theorem edge_sound {top bottom : Concept} {O : Ontology Concept Role}
    {Domain : Type} {I : Interp Domain Concept Role top bottom}
    (hI : models I O) {a target : Concept} {role : Role}
    (h : Edge top bottom O a role target) :
    ∀ x, I.concept a x →
      ∃ y, I.role role x y ∧ I.concept target y :=
  Edge.rec
    (motive_1 := fun a b _ => ∀ x, I.concept a x → I.concept b x)
    (motive_2 := fun a role b _ =>
      ∀ x, I.concept a x → ∃ y, I.role role x y ∧ I.concept b y)
    (fun _ _ ha => ha)
    (fun _ x _ => I.top_true x)
    (fun _ hcl ih x hx => (hI _ hcl) x (ih x hx))
    (fun _ _ hcl ihl ihr x hx => (hI _ hcl) x (ihl x hx) (ihr x hx))
    (fun _ hcl ih x hx => False.elim ((hI _ hcl) x (ih x hx)))
    (fun _ _ hcl ihe ihs x hx =>
      let ⟨y, hxy, hy⟩ := ihe x hx
      (hI _ hcl) x ⟨y, hxy, ihs y hy⟩)
    (fun _ _ ihe ihb x hx =>
      let ⟨y, _, hy⟩ := ihe x hx
      False.elim (I.bottom_false y (ihb y hy)))
    (fun _ hcl ihs x hx => (hI _ hcl) x (ihs x hx))
    (fun _ hcl ihe x hx =>
      let ⟨y, hxy, hy⟩ := ihe x hx
      ⟨y, (hI _ hcl) x y hxy, hy⟩)
    (fun _ _ hcl ihe₁ ihe₂ x hx =>
      let ⟨y, hxy, hy⟩ := ihe₁ x hx
      let ⟨z, hyz, hz⟩ := ihe₂ y hy
      ⟨z, (hI _ hcl) x y z hxy hyz, hz⟩)
    (fun _ _ hcl x hx => ⟨x, (hI _ hcl) x, hx⟩)
    h

/-- Contexts that survive bottom elimination. -/
abbrev Alive (top bottom : Concept) (O : Ontology Concept Role) :=
  { a : Concept // ¬ Sub top bottom O a bottom }

/-- The canonical model over exactly the contexts not labelled bottom. -/
def canon {top bottom : Concept} {O : Ontology Concept Role} :
    Interp (Alive top bottom O) Concept Role top bottom where
  concept := fun c x => Sub top bottom O x.1 c
  role := fun r x y => Edge top bottom O x.1 r y.1
  top_true := fun x => Sub.top x.1
  bottom_false := fun x => x.2

/-- The canonical alive-context interpretation satisfies every NF1–NF7 axiom. -/
theorem canon_models {top bottom : Concept} {O : Ontology Concept Role}
    : models (canon (top := top) (bottom := bottom) (O := O)) O := by
  intro clause hcl
  cases clause with
  | nf1 sub sup =>
      intro x hx
      exact Sub.nf1 hx hcl
  | nf2 left right sup =>
      intro x hl hr
      exact Sub.nf2 hl hr hcl
  | nf3 sub role filler =>
      intro x hx
      have hedge : Edge top bottom O x.1 role filler := Edge.nf3 hx hcl
      have alive : ¬ Sub top bottom O filler bottom := by
        intro hbottom
        exact x.2 (Sub.bottomEdge hedge hbottom)
      exact ⟨⟨filler, alive⟩, hedge, Sub.refl filler⟩
  | nf4 role filler sup =>
      intro x hex
      rcases hex with ⟨target, hedge, hfiller⟩
      exact Sub.nf4 hedge hfiller hcl
  | nf5 sub =>
      intro x hx
      exact x.2 (Sub.nf5 hx hcl)
  | nf6 sub sup =>
      intro x y hedge
      exact Edge.nf6 hedge hcl
  | nf7 first second sup =>
      intro x y z hxy hyz
      exact Edge.nf7 hxy hyz hcl
  | reflexive role =>
      intro x
      exact Edge.reflexive x.1 hcl

/-- Semantic named-concept subsumption over the ELC interpretation class. -/
def EntailsSub {top bottom : Concept} (O : Ontology Concept Role)
    (sub sup : Concept) : Prop :=
  ∀ {Domain : Type} (I : Interp Domain Concept Role top bottom),
    models I O → ∀ x, I.concept sub x → I.concept sup x

/-- Semantic inconsistency: no ELC interpretation models the ontology. -/
def Unsatisfiable {top bottom : Concept} (O : Ontology Concept Role) : Prop :=
  ∀ {Domain : Type} [Nonempty Domain] (I : Interp Domain Concept Role top bottom),
    models I O → False

/-- Rust's `TOP`-label bottom test is sound for ontology inconsistency. -/
theorem top_bottom_sound {top bottom : Concept} {O : Ontology Concept Role}
    (h : Sub top bottom O top bottom) :
    Unsatisfiable (top := top) (bottom := bottom) O := by
  intro Domain inhabited I hI
  exact inhabited.elim fun x =>
    I.bottom_false x (sub_sound hI h x (I.top_true x))

/-- A consistent ontology's canonical domain is nonempty, witnessed by `TOP`. -/
theorem alive_nonempty {top bottom : Concept} {O : Ontology Concept Role}
    (h : ¬ Sub top bottom O top bottom) : Nonempty (Alive top bottom O) :=
  ⟨⟨top, h⟩⟩

/-- Failure to derive `TOP ⊑ BOTTOM` constructs a nonempty canonical model. -/
theorem top_bottom_complete {top bottom : Concept} {O : Ontology Concept Role}
    (h : ¬ Sub top bottom O top bottom) :
    Nonempty (Alive top bottom O) ∧
      models (canon (top := top) (bottom := bottom) (O := O)) O :=
  ⟨alive_nonempty h, canon_models⟩

/--
Completeness of the pure ELC taxonomy on a consistent ontology.  An entailed
`A ⊑ B` is either represented by the stronger result `A ⊑ BOTTOM` (Rust reports
`A` unsatisfiable) or occurs directly in `A`'s completed label.
-/
theorem subsumption_complete {top bottom : Concept} {O : Ontology Concept Role}
    (a b : Concept)
    (hentails : EntailsSub (top := top) (bottom := bottom) O a b) :
    Sub top bottom O a bottom ∨ Sub top bottom O a b := by
  by_cases ha : Sub top bottom O a bottom
  · exact Or.inl ha
  · right
    let x : Alive top bottom O := ⟨a, ha⟩
    exact hentails canon canon_models x (Sub.refl a)

end ContextCalculus.ELCompletion
