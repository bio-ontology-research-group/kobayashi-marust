/-
  ContextCalculus/CompletenessEL.lean
  ===================================
  **First-order completeness of consequence-based reasoning for EL**, via a
  canonical model with genuine existential witnesses.

  The propositional theorem in `CompletenessProp.lean` settles the *disjunction*
  direction of completeness.  The orthogonal hard direction is *existentials*
  (the successor-context / Succ–Pred machinery of the calculus).  This file
  settles that direction for the EL fragment — the foundational consequence-based
  case (ELK) that the Tena-Cucala calculus generalises — by the canonical-model
  method the thesis uses.

  The closure rules `Sub`/`Edge` below are exactly the engine's Core / Hyper /
  Succ / Pred specialised to Horn EL clauses:
    * `Sub.conInc`  is Hyper on a concept-inclusion clause;
    * `Edge.base`   is the Succ rule (introduce an R-successor witness);
    * `Edge.sub`    propagates a subsumption to the successor;
    * `Sub.exLeft`  is the Pred rule (a `∃R.D ⊑ C` consequence pushed back);
    * `Edge.role`   is the role-hierarchy clause.

  The canonical interpretation interprets each existential by an actual domain
  element (an `Edge`), so this is genuinely first-order, not propositional.
  `completeness` is `sorry`-free and uses no axioms beyond Lean's kernel.

  (This is the EL slice; the full ALCHOIQ context-calculus completeness — the
  simultaneous interaction of disjunction, existentials, inverses, nominals and
  number restrictions — is the remaining open formalisation.)
-/

namespace ContextCalculus.EL

variable {CName Role : Type}

/-- A normalised EL query concept: an atom `A` or an existential `∃R.B`. -/
inductive NConcept (CName Role : Type) where
  | atom (a : CName)
  | ex (r : Role) (b : CName)

/-- Normalised EL clauses. -/
inductive Clause (CName Role : Type) where
  | conInc (body : List CName) (head : CName)   -- ⊓ body ⊑ head   (empty body = ⊤ ⊑ head)
  | exRight (a : CName) (r : Role) (b : CName)   -- a ⊑ ∃R.b
  | exLeft (r : Role) (d : CName) (c : CName)    -- ∃R.d ⊑ c
  | roleInc (r s : Role)                         -- R ⊑ S

abbrev Ontology (CName Role : Type) := List (Clause CName Role)

/-- An interpretation over a domain `D`. -/
structure Interp (D CName Role : Type) where
  c : CName → D → Prop
  r : Role → D → D → Prop

/-- Truth of a normalised concept at an element. -/
def evalN {D : Type} (I : Interp D CName Role) : NConcept CName Role → D → Prop
  | NConcept.atom a, x => I.c a x
  | NConcept.ex rr b, x => ∃ y, I.r rr x y ∧ I.c b y

/-- An interpretation satisfies a clause. -/
def satClause {D : Type} (I : Interp D CName Role) : Clause CName Role → Prop
  | Clause.conInc body head => ∀ x, (∀ a ∈ body, I.c a x) → I.c head x
  | Clause.exRight a rr b => ∀ x, I.c a x → ∃ y, I.r rr x y ∧ I.c b y
  | Clause.exLeft rr d cc => ∀ x, (∃ y, I.r rr x y ∧ I.c d y) → I.c cc x
  | Clause.roleInc rr ss => ∀ x y, I.r rr x y → I.r ss x y

/-- `I` models the ontology. -/
def models {D : Type} (I : Interp D CName Role) (O : Ontology CName Role) : Prop :=
  ∀ cl ∈ O, satClause I cl

/- The consequence-based closure: derived subsumptions `Sub` between concept
   names and existential edges `Edge`.  These are the EL completion rules
   (`Sub.conInc` = Hyper, `Edge.base` = Succ, `Sub.exLeft` = Pred). -/
mutual
inductive Sub (O : Ontology CName Role) : CName → CName → Prop where
  | refl (a : CName) : Sub O a a
  | conInc {body : List CName} {head a : CName} :
      (∀ b ∈ body, Sub O a b) → Clause.conInc body head ∈ O → Sub O a head
  | exLeft {a : CName} {r : Role} {d c b : CName} :
      Edge O a r b → Sub O b d → Clause.exLeft r d c ∈ O → Sub O a c
inductive Edge (O : Ontology CName Role) : CName → Role → CName → Prop where
  | base {a : CName} {r : Role} {b : CName} : Clause.exRight a r b ∈ O → Edge O a r b
  | sub {a a' : CName} {r : Role} {b : CName} : Sub O a a' → Edge O a' r b → Edge O a r b
  | role {a : CName} {r s : Role} {b : CName} : Edge O a r b → Clause.roleInc r s ∈ O → Edge O a s b
end

/-- **Soundness of the EL closure.**  Every derived subsumption holds in every
    model of the ontology; simultaneously every derived edge `a ⊑ ∃r.b` holds.
    Proved with the mutual recursor `Sub.rec` (the `conInc` rule quantifies over
    a list, so plain structural recursion does not apply). -/
theorem sub_sound {O : Ontology CName Role} {D : Type} {I : Interp D CName Role}
    (hI : models I O) {a b : CName} (h : Sub O a b) : ∀ x, I.c a x → I.c b x :=
  Sub.rec
    (motive_1 := fun a b _ => ∀ x, I.c a x → I.c b x)
    (motive_2 := fun a r b _ => ∀ x, I.c a x → ∃ y, I.r r x y ∧ I.c b y)
    (fun _ x hx => hx)
    (fun _ hcl ih x hx => (hI _ hcl) x (fun b hb => ih b hb x hx))
    (fun _ _ hcl ihe ihs x hx =>
      let ⟨y, hxy, hyd⟩ := ihe x hx; (hI _ hcl) x ⟨y, hxy, ihs y hyd⟩)
    (fun hcl x hx => (hI _ hcl) x hx)
    (fun _ _ ihs ihe x hx => ihe x (ihs x hx))
    (fun _ hcl ihe x hx => let ⟨y, hxy, hyb⟩ := ihe x hx; ⟨y, (hI _ hcl) x y hxy, hyb⟩)
    h

/-- The **canonical interpretation**: the domain is the set of concept names;
    `A` is an instance of `B` iff `Sub O A B`; there is an `R`-edge `A → B` iff
    `Edge O A R B`.  Existentials are witnessed by actual domain elements. -/
def canon (O : Ontology CName Role) : Interp CName CName Role where
  c := fun a x => Sub O x a
  r := fun rr x y => Edge O x rr y

/-- **The canonical interpretation models the ontology.**  This is where the
    completion rules are used: each clause shape is satisfied by construction. -/
theorem canon_models (O : Ontology CName Role) : models (canon O) O := by
  intro cl hcl
  cases cl with
  | conInc body head =>
    intro x hx
    exact Sub.conInc (by intro b hb; exact hx b hb) hcl
  | exRight a rr b =>
    intro x hx
    -- x ⊑ a and a ⊑ ∃R.b  ⟹  x has an R-edge to b, and b ⊑ b
    exact ⟨b, Edge.sub hx (Edge.base hcl), Sub.refl b⟩
  | exLeft rr d cc =>
    intro x hx
    obtain ⟨y, hxy, hyd⟩ := hx
    exact Sub.exLeft hxy hyd hcl
  | roleInc rr ss =>
    intro x y hxy
    exact Edge.role hxy hcl

/-- **First-order EL completeness.**  If the ontology entails the subsumption
    `a ⊑ C` (semantically, over every interpretation and domain), then the
    consequence-based closure derives it: `evalN (canon O) C a`, i.e.
    `Sub O a b` when `C = atom b`, or an `Edge`+`Sub` witness when `C = ∃R.b`.

    The entailment is discharged at the canonical model (a legitimate
    interpretation that models `O` by `canon_models`), instantiated at the
    element `a` itself (where `canon.c a a = Sub O a a = refl`). -/
theorem completeness (O : Ontology CName Role) (a : CName) (C : NConcept CName Role)
    (hent : ∀ {D : Type} (I : Interp D CName Role), models I O → ∀ x, I.c a x → evalN I C x) :
    evalN (canon O) C a :=
  hent (canon O) (canon_models O) a (Sub.refl a)

/-- Spelt out for an atomic query: `O ⊨ a ⊑ b` implies `Sub O a b`. -/
theorem completeness_atom (O : Ontology CName Role) (a b : CName)
    (hent : ∀ {D : Type} (I : Interp D CName Role), models I O → ∀ x, I.c a x → I.c b x) :
    Sub O a b :=
  completeness O a (NConcept.atom b) (fun I hI x hx => hent I hI x hx)

end ContextCalculus.EL
