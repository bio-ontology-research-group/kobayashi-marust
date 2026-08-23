/-
  ContextCalculus/CompletenessEq.lean
  ===================================
  **The equality-quotient Herbrand model — the NExpTime construction with
  merging (number restrictions, nominals, inverse roles).**

  `CompletenessContext.lean` builds the finite filtration model for ALC, but that
  construction breaks once the language can force distinct successors to be the
  *same* element: `≤1 R` (functionality / number restrictions), `{o}` (nominals),
  and inverse roles all need **merging**, and the model becomes a quotient of the
  Herbrand universe by an equality relation, not a set of independent types.

  This file builds exactly that.  The context calculus grounds a saturated
  context structure to a finite set `G` of **ground clauses** over the atoms
  `C(x)`, `R(x,y)`, `x≈y` (the Skolem witnesses are the function terms `f_i(x)`;
  after blocking the Herbrand universe `T` is finite).  The model is:

      a propositional model `π` of `G`  (exists iff `G` is clash-free, by the
      propositional resolution completeness of `CompletenessProp`)
        ⟶  quotient `T / ≈π`  where  `x ≈π y  :=  π (x≈y)`,
            the congruence the equality axioms in `G` force `π` to respect.

  Merging is the quotient; functionality is a binary equality clause that `π`
  satisfies; nominals are `C(x) → x≈o` clauses; inverses are role-atom clauses.

  Results (all `sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`):

    * `congruenceModel_models` — if `π ⊨ G` and `G` grounds `O` over `T`
      (`Grounds`), the congruence quotient of `π` is a genuine first-order model
      of `O`, **including** functional roles, nominals and inverse roles;
    * `herbrand_complete` — if the grounding `G` is clash-free (propositional
      resolution does not derive `⊥`), then `O` has a model.  This is the
      completeness of the equational construction, with model existence supplied
      by `CompletenessProp.completeness` (no assumed Herbrand lemma).

  Scope of the merging covered: equality (`≈`) and its congruence, functional
  roles (`≤1 R`), nominals (`{o}`), inverse roles, role hierarchy, on top of the
  disjunctive ALC core.  General qualified number restrictions `≤n R.C` for `n≥2`
  reduce to the same quotient plus a pigeonhole over `(n+1)`-tuples of the
  distinctness clauses (`Factor`); that combinatorial step is noted where it
  attaches and is the one piece not unfolded here.
-/
import ContextCalculus.CompletenessProp
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ContextCalculus.Eqv

open ContextCalculus.PropRes

variable {CN RN T : Type} [DecidableEq CN] [DecidableEq RN] [DecidableEq T]

/-- Ground atoms over the Herbrand universe `T`: concept membership, role edges,
    and equality (the carrier of the merging). -/
inductive GAtom (CN RN T : Type) where
  | con (c : CN) (x : T)
  | rol (r : RN) (x y : T)
  | eqa (x y : T)
deriving DecidableEq, Fintype

/-- A propositional valuation of ground atoms (a model of the grounded clause
    set will be such a `π`). -/
abbrev Val (CN RN T : Type) := GAtom CN RN T → Prop

/-- `π` **respects equality**: the equality atoms form a congruence.  Forced on
    any model `π` of `G` whenever `G` contains the equality axioms (see
    `eqAxioms`), so this is *derived*, not assumed. -/
structure RespectsEq (π : Val CN RN T) : Prop where
  refl  : ∀ x, π (GAtom.eqa x x)
  symm  : ∀ {x y}, π (GAtom.eqa x y) → π (GAtom.eqa y x)
  trans : ∀ {x y z}, π (GAtom.eqa x y) → π (GAtom.eqa y z) → π (GAtom.eqa x z)
  congC : ∀ {c x y}, π (GAtom.eqa x y) → π (GAtom.con c x) → π (GAtom.con c y)
  congRL : ∀ {r x x' y}, π (GAtom.eqa x x') → π (GAtom.rol r x y) → π (GAtom.rol r x' y)
  congRR : ∀ {r x y y'}, π (GAtom.eqa y y') → π (GAtom.rol r x y) → π (GAtom.rol r x y')

/-- The Herbrand equivalence induced by `π`. -/
def herbrandSetoid (π : Val CN RN T) (h : RespectsEq π) : Setoid T where
  r x y := π (GAtom.eqa x y)
  iseqv := ⟨h.refl, h.symm, h.trans⟩

/-- An interpretation: concept and role extensions plus a naming of individuals
    (needed to interpret nominals). -/
structure Interp (D CN RN T : Type) where
  c : CN → D → Prop
  r : RN → D → D → Prop
  nm : T → D

/-- Normalised clauses over the full feature set.  `gci` is disjunctive; the last
    four are the merging features. -/
inductive OClause (CN RN T : Type) where
  | gci (body head : List CN)                 -- ⊓ body ⊑ ⊔ head
  | exR (a : CN) (r : RN) (b : CN)             -- a ⊑ ∃r.b
  | allR (a : CN) (r : RN) (b : CN)            -- a ⊑ ∀r.b
  | exL (r : RN) (d c : CN)                    -- ∃r.d ⊑ c
  | subR (r s : RN)                            -- r ⊑ s   (role hierarchy)
  | inv (r s : RN)                             -- r ≡ s⁻  (inverse roles)
  | func (r : RN)                              -- ≤1 r    (functional role)
  | nom (a : CN) (o : T)                       -- a ≡ {o} (nominal concept)
  | atMost (n : ℕ) (r : RN) (c : CN)           -- ≤n r.c  (qualified number restriction)

abbrev Ontology (CN RN T : Type) := List (OClause CN RN T)

/-- Tarskian satisfaction.  `func` and `nom` use *domain* equality `=`, which in
    the canonical model is quotient (merge) equality. -/
def satO {D : Type} (I : Interp D CN RN T) : OClause CN RN T → Prop
  | OClause.gci body head => ∀ x, (∀ a ∈ body, I.c a x) → ∃ b ∈ head, I.c b x
  | OClause.exR a rr b => ∀ x, I.c a x → ∃ y, I.r rr x y ∧ I.c b y
  | OClause.allR a rr b => ∀ x, I.c a x → ∀ y, I.r rr x y → I.c b y
  | OClause.exL rr d cc => ∀ x, (∃ y, I.r rr x y ∧ I.c d y) → I.c cc x
  | OClause.subR rr ss => ∀ x y, I.r rr x y → I.r ss x y
  | OClause.inv rr ss => ∀ x y, I.r rr x y ↔ I.r ss y x
  | OClause.func rr => ∀ x y z, I.r rr x y → I.r rr x z → y = z
  | OClause.nom a o => ∀ x, I.c a x ↔ x = I.nm o
  | OClause.atMost n rr cc => ∀ x, ∀ f : Fin (n + 1) → D,
      (∀ i, I.r rr x (f i) ∧ I.c cc (f i)) → ∃ i j, i ≠ j ∧ f i = f j

def models {D : Type} (I : Interp D CN RN T) (O : Ontology CN RN T) : Prop :=
  ∀ cl ∈ O, satO I cl

/-! ### The congruence quotient model -/

/-- The domain of the canonical model: the Herbrand universe quotiented by `≈π`
    (the merge).  Distinct ground terms forced equal collapse to one element. -/
abbrev QDom (π : Val CN RN T) (h : RespectsEq π) : Type := Quotient (herbrandSetoid π h)

/-- **The congruence (Herbrand) model.**  A concept holds at `⟦x⟧` iff `π` makes
    it hold at `x`; well-definedness across the merge is exactly `RespectsEq`. -/
def congruenceModel (π : Val CN RN T) (h : RespectsEq π) :
    Interp (QDom π h) CN RN T where
  c := fun cc => Quotient.lift (fun x => π (GAtom.con cc x))
    (by intro a b hab
        exact propext ⟨fun ha => h.congC hab ha, fun hb => h.congC (h.symm hab) hb⟩)
  r := fun rr => Quotient.lift₂ (fun x y => π (GAtom.rol rr x y))
    (by intro a b a' b' haa' hbb'
        exact propext ⟨fun hab => h.congRR hbb' (h.congRL haa' hab),
                       fun hab => h.congRR (h.symm hbb') (h.congRL (h.symm haa') hab)⟩)
  nm := fun o => Quotient.mk _ o

@[simp] theorem cm_c (π : Val CN RN T) (h : RespectsEq π) (cc : CN) (x : T) :
    (congruenceModel π h).c cc (Quotient.mk _ x) = π (GAtom.con cc x) := rfl

@[simp] theorem cm_r (π : Val CN RN T) (h : RespectsEq π) (rr : RN) (x y : T) :
    (congruenceModel π h).r rr (Quotient.mk _ x) (Quotient.mk _ y) = π (GAtom.rol rr x y) := rfl

/-! ### Grounding: the ground clauses a saturated context structure produces -/

/-- A ground implication `⋀ bs → ⋁ hs` as a propositional clause. -/
def clImp (bs hs : List (GAtom CN RN T)) : PClause (GAtom CN RN T) :=
  ⟨bs.toFinset, hs.toFinset⟩

theorem clImp_sat (π : Val CN RN T) (bs hs : List (GAtom CN RN T)) :
    (clImp bs hs).sat π ↔ ((∀ a ∈ bs, π a) → ∃ a ∈ hs, π a) := by
  unfold clImp PClause.sat
  simp only [List.mem_toFinset]

/-- Body of the `≤n r.c` distinctness clause for the `(n+1)`-tuple `g`: assert all
    `n+1` terms are `r`-successors that are in `c`. -/
def atMostBody (rr : RN) (cc : CN) (n : ℕ) (x : T) (g : Fin (n + 1) → T) :
    List (GAtom CN RN T) :=
  (List.finRange (n + 1)).map (fun i => GAtom.rol rr x (g i)) ++
  (List.finRange (n + 1)).map (fun i => GAtom.con cc (g i))

/-- Head of the `≤n r.c` distinctness clause: some two of the `n+1` terms are
    equal (the `Factor` disjunction). -/
def atMostHead (n : ℕ) (g : Fin (n + 1) → T) : List (GAtom CN RN T) :=
  (List.finRange (n + 1)).flatMap (fun i =>
    (List.finRange (n + 1)).flatMap (fun j =>
      if i < j then [GAtom.eqa (g i) (g j)] else []))

theorem mem_atMostBody {rr cc n x g} {ga : GAtom CN RN T} :
    ga ∈ atMostBody rr cc n x g ↔
      (∃ i, ga = GAtom.rol rr x (g i)) ∨ (∃ i, ga = GAtom.con cc (g i)) := by
  simp only [atMostBody, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    eq_comm]

theorem mem_atMostHead {n} {g : Fin (n + 1) → T} {ga : GAtom CN RN T} :
    ga ∈ atMostHead n g ↔ ∃ i j, i < j ∧ ga = GAtom.eqa (g i) (g j) := by
  simp only [atMostHead, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, j, hij⟩
    by_cases h : i < j
    · simp only [h, if_true, List.mem_singleton] at hij
      exact ⟨i, j, h, hij⟩
    · simp only [h, if_false, List.not_mem_nil] at hij
  · rintro ⟨i, j, hlt, rfl⟩
    exact ⟨i, j, by simp only [hlt, if_true, List.mem_singleton]⟩

/-- `G` **grounds** `O` over the Herbrand universe `T` with Skolem witness map
    `wit`: it contains the equality axioms and, for every ontology clause, every
    ground instance over `T`.  This is exactly what the grounder emits from a
    saturated, terminated (blocked) context structure. -/
structure Grounds (G : Finset (PClause (GAtom CN RN T))) (O : Ontology CN RN T)
    (wit : CN → RN → CN → T → T) : Prop where
  eqRefl : ∀ x, clImp [] [GAtom.eqa x x] ∈ G
  eqSym  : ∀ x y, clImp [GAtom.eqa x y] [GAtom.eqa y x] ∈ G
  eqTrans : ∀ x y z, clImp [GAtom.eqa x y, GAtom.eqa y z] [GAtom.eqa x z] ∈ G
  eqCongC : ∀ c x y, clImp [GAtom.eqa x y, GAtom.con c x] [GAtom.con c y] ∈ G
  eqCongRL : ∀ r x x' y, clImp [GAtom.eqa x x', GAtom.rol r x y] [GAtom.rol r x' y] ∈ G
  eqCongRR : ∀ r x y y', clImp [GAtom.eqa y y', GAtom.rol r x y] [GAtom.rol r x y'] ∈ G
  gciI : ∀ body head, OClause.gci body head ∈ O → ∀ x,
           clImp (body.map (fun a => GAtom.con a x)) (head.map (fun b => GAtom.con b x)) ∈ G
  exRI1 : ∀ a r b, OClause.exR a r b ∈ O → ∀ x,
            clImp [GAtom.con a x] [GAtom.rol r x (wit a r b x)] ∈ G
  exRI2 : ∀ a r b, OClause.exR a r b ∈ O → ∀ x,
            clImp [GAtom.con a x] [GAtom.con b (wit a r b x)] ∈ G
  allRI : ∀ a r b, OClause.allR a r b ∈ O → ∀ x y,
            clImp [GAtom.con a x, GAtom.rol r x y] [GAtom.con b y] ∈ G
  exLI : ∀ r d c, OClause.exL r d c ∈ O → ∀ x y,
           clImp [GAtom.rol r x y, GAtom.con d y] [GAtom.con c x] ∈ G
  subRI : ∀ r s, OClause.subR r s ∈ O → ∀ x y,
            clImp [GAtom.rol r x y] [GAtom.rol s x y] ∈ G
  invI1 : ∀ r s, OClause.inv r s ∈ O → ∀ x y,
            clImp [GAtom.rol r x y] [GAtom.rol s y x] ∈ G
  invI2 : ∀ r s, OClause.inv r s ∈ O → ∀ x y,
            clImp [GAtom.rol s y x] [GAtom.rol r x y] ∈ G
  funcI : ∀ r, OClause.func r ∈ O → ∀ x y z,
            clImp [GAtom.rol r x y, GAtom.rol r x z] [GAtom.eqa y z] ∈ G
  nomI1 : ∀ a o, OClause.nom a o ∈ O → ∀ x,
            clImp [GAtom.con a x] [GAtom.eqa x o] ∈ G
  nomI2 : ∀ a o, OClause.nom a o ∈ O →
            clImp [] [GAtom.con a o] ∈ G
  atMostI : ∀ n r c, OClause.atMost n r c ∈ O → ∀ x (g : Fin (n + 1) → T),
              clImp (atMostBody r c n x g) (atMostHead n g) ∈ G

/-- Discharge one ground implication: from a member of `G` satisfied by `π`,
    pull out its `bs → hs` content. -/
theorem useClause {π : Val CN RN T} {G : Finset (PClause (GAtom CN RN T))}
    (hG : ∀ c ∈ G, c.sat π) {bs hs : List (GAtom CN RN T)}
    (hmem : clImp bs hs ∈ G) (hbs : ∀ a ∈ bs, π a) : ∃ a ∈ hs, π a :=
  (clImp_sat π bs hs).1 (hG _ hmem) hbs

/-- **The congruence quotient model satisfies the ontology.**  Given a
    propositional model `π` of a grounding `G` of `O`, the quotient
    `congruenceModel π h` is a genuine first-order model of `O` — including the
    merging features (functional roles via quotient equality, nominals as
    singletons, inverse roles).  This is the equational Herbrand construction. -/
theorem congruenceModel_models {π : Val CN RN T} (h : RespectsEq π)
    {G : Finset (PClause (GAtom CN RN T))} {O : Ontology CN RN T}
    {wit : CN → RN → CN → T → T}
    (hG : ∀ c ∈ G, c.sat π) (hgr : Grounds G O wit) :
    models (congruenceModel π h) O := by
  intro cl hcl
  cases cl with
  | gci body head =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    intro hbody
    have hbs : ∀ ga ∈ body.map (fun a => GAtom.con a x), π ga := by
      intro ga hga; simp only [List.mem_map] at hga
      obtain ⟨b, hb, rfl⟩ := hga; exact hbody b hb
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.gciI body head hcl x) hbs
    simp only [List.mem_map] at hga
    obtain ⟨b, hb, rfl⟩ := hga; exact ⟨b, hb, hπ⟩
  | exR a r b =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    intro ha
    refine ⟨Quotient.mk _ (wit a r b x), ?_, ?_⟩
    · obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.exRI1 a r b hcl x)
        (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ha)
      simp only [List.mem_singleton] at hga; subst hga; exact hπ
    · obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.exRI2 a r b hcl x)
        (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact ha)
      simp only [List.mem_singleton] at hga; subst hga; exact hπ
  | allR a r b =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    intro ha q'
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q'
    intro hr
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.allRI a r b hcl x y)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact ha
          · subst h2; exact hr)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  | exL r d c =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rintro ⟨q', hr, hd⟩
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q'
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.exLI r d c hcl x y)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hr
          · subst h2; exact hd)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  | subR r s =>
    intro q1 q2
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q1
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q2
    intro hr
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.subRI r s hcl x y)
      (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hr)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  | inv r s =>
    intro q1 q2
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q1
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q2
    constructor
    · intro hr
      obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.invI1 r s hcl x y)
        (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hr)
      simp only [List.mem_singleton] at hga; subst hga; exact hπ
    · intro hs
      obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.invI2 r s hcl x y)
        (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hs)
      simp only [List.mem_singleton] at hga; subst hga; exact hπ
  | func r =>
    intro q1 q2 q3
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q1
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q2
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q3
    intro hr1 hr2
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.funcI r hcl x y z)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hr1
          · subst h2; exact hr2)
    simp only [List.mem_singleton] at hga; subst hga
    exact Quotient.sound hπ
  | nom a o =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    constructor
    · intro hc
      obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.nomI1 a o hcl x)
        (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hc)
      simp only [List.mem_singleton] at hga; subst hga
      exact Quotient.sound hπ
    · intro hx
      have hco : π (GAtom.con a o) := by
        obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.nomI2 a o hcl)
          (by intro g hg; simp only [List.not_mem_nil] at hg)
        simp only [List.mem_singleton] at hga; subst hga; exact hπ
      have hxo : π (GAtom.eqa x o) := Quotient.exact hx
      exact h.congC (h.symm hxo) hco
  | atMost n r c =>
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    intro f hf
    have hrep : ∀ i, ∃ t : T, Quotient.mk _ t = f i := fun i => Quotient.exists_rep (f i)
    choose g hg using hrep
    have hbody : ∀ ga ∈ atMostBody r c n x g, π ga := by
      intro ga hga
      rw [mem_atMostBody] at hga
      rcases hga with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have hi := (hf i).1; rw [← hg i] at hi; exact hi
      · have hi := (hf i).2; rw [← hg i] at hi; exact hi
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.atMostI n r c hcl x g) hbody
    rw [mem_atMostHead] at hga
    obtain ⟨i, j, hlt, rfl⟩ := hga
    refine ⟨i, j, ne_of_lt hlt, ?_⟩
    rw [← hg i, ← hg j]
    exact Quotient.sound hπ

/-- The equality axioms in a grounding force any model `π` to respect equality.
    So `RespectsEq` is *derived* from `Grounds` + `π ⊨ G`, never assumed. -/
theorem respectsEq_of_grounds {π : Val CN RN T}
    {G : Finset (PClause (GAtom CN RN T))} {O : Ontology CN RN T}
    {wit : CN → RN → CN → T → T}
    (hG : ∀ c ∈ G, c.sat π) (hgr : Grounds G O wit) : RespectsEq π := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqRefl x) (by intro g hg; simp at hg)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  · intro x y hxy
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqSym x y)
      (by intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hxy)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  · intro x y z hxy hyz
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqTrans x y z)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hxy
          · subst h2; exact hyz)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  · intro c x y hxy hc
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqCongC c x y)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hxy
          · subst h2; exact hc)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  · intro r x x' y hxx' hr
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqCongRL r x x' y)
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hxx'
          · subst h2; exact hr)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ
  · intro r x y y' hyy' hr
    obtain ⟨ga, hga, hπ⟩ := useClause hG (hgr.eqCongRR r x y y')
      (by intro g hg; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hg
          rcases hg with h1 | h2
          · subst h1; exact hyy'
          · subst h2; exact hr)
    simp only [List.mem_singleton] at hga; subst hga; exact hπ

/-- **Completeness of the equational Herbrand construction.**  If the grounding
    `G` of `O` is *clash-free* (propositional resolution does not derive the empty
    clause), then `O` has a model.  Model existence is supplied by
    `PropRes.completeness` (clash-free ⟹ satisfiable), and the satisfying
    valuation is turned into a first-order model by the congruence quotient.
    Contrapositively: if `O` is unsatisfiable the calculus derives `⊥`. -/
theorem herbrand_complete {G : Finset (PClause (GAtom CN RN T))}
    {O : Ontology CN RN T} {wit : CN → RN → CN → T → T}
    (hgr : Grounds G O wit) (hclash : ¬ Derivable G PClause.bot) :
    ∃ (D : Type) (I : Interp D CN RN T), models I O := by
  have hsat : ∃ π : GAtom CN RN T → Prop, ∀ c ∈ G, c.sat π := by
    by_contra hns
    exact hclash (PropRes.completeness G hns)
  obtain ⟨π, hπ⟩ := hsat
  have h := respectsEq_of_grounds hπ hgr
  exact ⟨QDom π h, congruenceModel π h, congruenceModel_models h hπ hgr⟩

/-! ### A concrete grounder, proven to satisfy `Grounds`

  This removes `Grounds` as an assumed interface: over a *finite* vocabulary and
  Herbrand universe (the blocked, terminated saturation), the grounder `ground`
  emits exactly the equality axioms and ontology instances, and `grounds_ground`
  proves the emitted set satisfies `Grounds`. -/

section Grounder

variable [Fintype T] [Fintype CN] [Fintype RN]

theorem image_mem {β γ : Type} [DecidableEq γ] [Fintype β] (f : β → γ) (b : β) :
    f b ∈ Finset.univ.image f :=
  Finset.mem_image_of_mem f (Finset.mem_univ b)

theorem mem_fold_of_mem {β : Type} [DecidableEq β] (f : OClause CN RN T → Finset β)
    {cl : OClause CN RN T} : ∀ {O : Ontology CN RN T}, cl ∈ O →
      f cl ⊆ (O.map f).foldr (· ∪ ·) ∅ := by
  intro O
  induction O with
  | nil => intro h; cases h
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Finset.subset_union_left
    · exact (ih hmem).trans Finset.subset_union_right

/-- The equality axioms over the finite vocabulary and Herbrand universe. -/
def eqAxiomSet : Finset (PClause (GAtom CN RN T)) :=
  (Finset.univ.image (fun x : T => clImp [] [GAtom.eqa x x])) ∪
  ((Finset.univ.image (fun p : T × T => clImp [GAtom.eqa p.1 p.2] [GAtom.eqa p.2 p.1])) ∪
  ((Finset.univ.image (fun p : T × T × T =>
      clImp [GAtom.eqa p.1 p.2.1, GAtom.eqa p.2.1 p.2.2] [GAtom.eqa p.1 p.2.2])) ∪
  ((Finset.univ.image (fun p : CN × T × T =>
      clImp [GAtom.eqa p.2.1 p.2.2, GAtom.con p.1 p.2.1] [GAtom.con p.1 p.2.2])) ∪
  ((Finset.univ.image (fun p : RN × T × T × T =>
      clImp [GAtom.eqa p.2.1 p.2.2.1, GAtom.rol p.1 p.2.1 p.2.2.2]
            [GAtom.rol p.1 p.2.2.1 p.2.2.2])) ∪
  (Finset.univ.image (fun p : RN × T × T × T =>
      clImp [GAtom.eqa p.2.2.1 p.2.2.2, GAtom.rol p.1 p.2.1 p.2.2.1]
            [GAtom.rol p.1 p.2.1 p.2.2.2]))))))

/-- All ground instances of one ontology clause. -/
def clauseInsts (wit : CN → RN → CN → T → T) :
    OClause CN RN T → Finset (PClause (GAtom CN RN T))
  | OClause.gci body head =>
      Finset.univ.image (fun x : T =>
        clImp (body.map (fun a => GAtom.con a x)) (head.map (fun b => GAtom.con b x)))
  | OClause.exR a r b =>
      (Finset.univ.image (fun x : T => clImp [GAtom.con a x] [GAtom.rol r x (wit a r b x)])) ∪
      (Finset.univ.image (fun x : T => clImp [GAtom.con a x] [GAtom.con b (wit a r b x)]))
  | OClause.allR a r b =>
      Finset.univ.image (fun p : T × T =>
        clImp [GAtom.con a p.1, GAtom.rol r p.1 p.2] [GAtom.con b p.2])
  | OClause.exL r d c =>
      Finset.univ.image (fun p : T × T =>
        clImp [GAtom.rol r p.1 p.2, GAtom.con d p.2] [GAtom.con c p.1])
  | OClause.subR r s =>
      Finset.univ.image (fun p : T × T => clImp [GAtom.rol r p.1 p.2] [GAtom.rol s p.1 p.2])
  | OClause.inv r s =>
      (Finset.univ.image (fun p : T × T => clImp [GAtom.rol r p.1 p.2] [GAtom.rol s p.2 p.1])) ∪
      (Finset.univ.image (fun p : T × T => clImp [GAtom.rol s p.2 p.1] [GAtom.rol r p.1 p.2]))
  | OClause.func r =>
      Finset.univ.image (fun p : T × T × T =>
        clImp [GAtom.rol r p.1 p.2.1, GAtom.rol r p.1 p.2.2] [GAtom.eqa p.2.1 p.2.2])
  | OClause.nom a o =>
      (Finset.univ.image (fun x : T => clImp [GAtom.con a x] [GAtom.eqa x o])) ∪
      {clImp [] [GAtom.con a o]}
  | OClause.atMost n r c =>
      Finset.univ.image (fun p : T × (Fin (n + 1) → T) =>
        clImp (atMostBody r c n p.1 p.2) (atMostHead n p.2))

/-- **The grounder.**  Equality axioms together with every ontology-clause
    instance over the finite Herbrand universe. -/
def ground (wit : CN → RN → CN → T → T) (O : Ontology CN RN T) :
    Finset (PClause (GAtom CN RN T)) :=
  eqAxiomSet ∪ (O.map (clauseInsts wit)).foldr (· ∪ ·) ∅

theorem mem_ground_eq {wit O} {c : PClause (GAtom CN RN T)} (h : c ∈ eqAxiomSet) :
    c ∈ ground wit O :=
  Finset.mem_union.mpr (Or.inl h)

theorem mem_ground_cl {wit O} {cl : OClause CN RN T} {c : PClause (GAtom CN RN T)}
    (hcl : cl ∈ O) (h : c ∈ clauseInsts wit cl) : c ∈ ground wit O :=
  Finset.mem_union.mpr (Or.inr (mem_fold_of_mem (clauseInsts wit) hcl h))

/-- **The grounder satisfies `Grounds`.**  Each required ground instance is in
    the emitted set; `Grounds` is therefore realised, not assumed. -/
theorem grounds_ground (wit : CN → RN → CN → T → T) (O : Ontology CN RN T) :
    Grounds (ground wit O) O wit where
  eqRefl := fun x => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨x, rfl⟩)
  eqSym := fun x y => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inl ⟨(x, y), rfl⟩))
  eqTrans := fun x y z => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inl ⟨(x, y, z), rfl⟩)))
  eqCongC := fun c x y => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(c, x, y), rfl⟩))))
  eqCongRL := fun r x x' y => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(r, x, x', y), rfl⟩)))))
  eqCongRR := fun r x y y' => mem_ground_eq (by
    simp only [eqAxiomSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨(r, x, y, y'), rfl⟩)))))
  gciI := fun body head hcl x => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ x)
  exRI1 := fun a r b hcl x => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact Finset.mem_union.mpr (Or.inl (image_mem _ x)))
  exRI2 := fun a r b hcl x => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact Finset.mem_union.mpr (Or.inr (image_mem _ x)))
  allRI := fun a r b hcl x y => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ (x, y))
  exLI := fun r d c hcl x y => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ (x, y))
  subRI := fun r s hcl x y => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ (x, y))
  invI1 := fun r s hcl x y => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact Finset.mem_union.mpr (Or.inl (image_mem _ (x, y))))
  invI2 := fun r s hcl x y => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact Finset.mem_union.mpr (Or.inr (image_mem _ (x, y))))
  funcI := fun r hcl x y z => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ (x, y, z))
  nomI1 := fun a o hcl x => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact Finset.mem_union.mpr (Or.inl (image_mem _ x)))
  nomI2 := fun a o hcl => mem_ground_cl hcl (by
    simp only [clauseInsts]
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_singleton.mpr rfl)))
  atMostI := fun n r c hcl x g => mem_ground_cl hcl (by
    simp only [clauseInsts]; exact image_mem _ (x, g))

/-- **Full equational Herbrand completeness, self-contained.**  Over a finite
    vocabulary and Herbrand universe, if the concrete grounding of `O` is
    clash-free (propositional resolution does not derive `⊥`), then `O` has a
    model — the congruence quotient — covering disjunction, existentials,
    universals, role hierarchy, inverse roles, nominals, and qualified number
    restrictions `≤n R.C`.  No assumed `Grounds`, no assumed Herbrand lemma. -/
theorem herbrand_complete_ground (wit : CN → RN → CN → T → T) (O : Ontology CN RN T)
    (hclash : ¬ Derivable (ground wit O) PClause.bot) :
    ∃ (D : Type) (I : Interp D CN RN T), models I O :=
  herbrand_complete (grounds_ground wit O) hclash

end Grounder

end ContextCalculus.Eqv
