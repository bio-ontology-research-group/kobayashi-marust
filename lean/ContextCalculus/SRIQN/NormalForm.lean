import ContextCalculus.SRIQ.Procedure

/-!
# Nominals: the normal form (stage C2, design section 1)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. The `SRIQ` clauses plus nominal
clauses `nom a`: the name `a` holds at exactly one element. The base
clauses keep their `SRIQ` meaning; the role hierarchy, closed types and
stars of an `SRIQN` ontology are those of its base part `basePart O`, so
every `SRIQ` lemma about them applies unchanged.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)

/-- Normalised clauses with nominals. -/
inductive Clause (CName Role : Type) where
  /-- An `SRIQ` clause. -/
  | base (cl : SRIQ.Clause CName Role)
  /-- `a` holds at exactly one element. -/
  | nom (a : CName)
deriving DecidableEq, Repr

abbrev Ontology (CName Role : Type) := List (Clause CName Role)

variable {D CName Role : Type}

/-- Tarskian satisfaction of a clause. -/
def satClause (I : Interp D CName Role) : Clause CName Role → Prop
  | .base cl => SRIQ.satClause I cl
  | .nom a => ∃ x, ∀ y, I.c a y ↔ y = x

/-- `I` models the ontology. -/
def models (I : Interp D CName Role) (O : Ontology CName Role) : Prop :=
  ∀ cl ∈ O, satClause I cl

/-- The ontology has a model over a nonempty domain. -/
def ConsistentN (O : Ontology CName Role) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (I : Interp D CName Role), models I O

/-- Subsumption between concept names, over nonempty domains. -/
def EntailsSubN (O : Ontology CName Role) (a b : CName) : Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role), models I O → ∀ x, I.c a x → I.c b x

/-- The base clauses. -/
def basePart (O : Ontology CName Role) : SRIQ.Ontology CName Role :=
  O.filterMap fun
    | .base cl => some cl
    | .nom _ => none

/-- The nominal names. -/
def noms (O : Ontology CName Role) : List CName :=
  O.filterMap fun
    | .nom a => some a
    | .base _ => none

theorem mem_basePart {O : Ontology CName Role} {cl : SRIQ.Clause CName Role} :
    cl ∈ basePart O ↔ Clause.base cl ∈ O := by
  simp only [basePart, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, he⟩
    cases c <;> simp only [Option.some.injEq, reduceCtorEq] at he
    exact he ▸ hc
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_noms {O : Ontology CName Role} {a : CName} : a ∈ noms O ↔ Clause.nom a ∈ O := by
  simp only [noms, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, he⟩
    cases c <;> simp only [Option.some.injEq, reduceCtorEq] at he
    exact he ▸ hc
  · intro h
    exact ⟨_, h, rfl⟩

/-- A name holds at exactly one element. -/
def NomAt (I : Interp D CName Role) (a : CName) : Prop := ∃ x, ∀ y, I.c a y ↔ y = x

theorem models_iff {I : Interp D CName Role} {O : Ontology CName Role} :
    models I O ↔ SRIQ.models I (basePart O) ∧ ∀ a ∈ noms O, NomAt I a := by
  constructor
  · intro h
    exact ⟨fun cl hcl => h _ (mem_basePart.1 hcl), fun a ha => h _ (mem_noms.1 ha)⟩
  · rintro ⟨h1, h2⟩ cl hcl
    cases cl with
    | base cl => exact h1 cl (mem_basePart.2 hcl)
    | nom a => exact h2 a (mem_noms.2 hcl)

/-- The base part is ALCHIQ: role chains have length one (section 8
removes transitivity first). -/
def IsALCHOIQ (O : Ontology CName Role) : Prop := SRIQ.IsALCHIQ (basePart O)

/-- `SRIQ` clauses as nominal clauses. -/
def ofSRIQ (O : SRIQ.Ontology CName Role) : Ontology CName Role := O.map .base

theorem basePart_ofSRIQ (O : SRIQ.Ontology CName Role) : basePart (ofSRIQ O) = O := by
  simp [basePart, ofSRIQ, List.filterMap_map]

theorem noms_ofSRIQ (O : SRIQ.Ontology CName Role) : noms (ofSRIQ O) = [] := by
  simp [noms, ofSRIQ, List.filterMap_map]

theorem models_ofSRIQ {I : Interp D CName Role} {O : SRIQ.Ontology CName Role} :
    models I (ofSRIQ O) ↔ SRIQ.models I O := by
  rw [models_iff, basePart_ofSRIQ, noms_ofSRIQ]
  simp

/-- **Embedding.** Without nominals, `SRIQN` subsumption is `SRIQ`
subsumption. -/
theorem entailsSubN_ofSRIQ (O : SRIQ.Ontology CName Role) (a b : CName) :
    EntailsSubN (ofSRIQ O) a b ↔ SRIQ.EntailsSub O a b := by
  unfold EntailsSubN SRIQ.EntailsSub
  simp only [models_ofSRIQ]

theorem basePart_append (O O' : Ontology CName Role) :
    basePart (O ++ O') = basePart O ++ basePart O' := by
  simp [basePart, List.filterMap_append]

theorem noms_append (O O' : Ontology CName Role) : noms (O ++ O') = noms O ++ noms O' := by
  simp [noms, List.filterMap_append]


/-! ## Renaming concept names -/

section Rename

variable {C' : Type}

/-- Rename the concept names of an `SRIQ` clause. -/
def mapC (f : CName → C') : SRIQ.Clause CName Role → SRIQ.Clause C' Role
  | .gci body head => .gci (body.map f) (head.map f)
  | .exRight a R b => .exRight (f a) R (f b)
  | .allRight a R b => .allRight (f a) R (f b)
  | .atLeast a k R b => .atLeast (f a) k R (f b)
  | .atMost a k R b => .atMost (f a) k R (f b)
  | .chain body S => .chain body S

/-- Rename the concept names of a clause. -/
def mapN (f : CName → C') : Clause CName Role → Clause C' Role
  | .base cl => .base (mapC f cl)
  | .nom a => .nom (f a)

/-- Read an interpretation of `C'` through `f`. -/
def pull (J : Interp D C' Role) (f : CName → C') : Interp D CName Role :=
  ⟨fun a => J.c (f a), J.r⟩

theorem pull_rt (J : Interp D C' Role) (f : CName → C') (R : RoleT Role) (x y : D) :
    (pull J f).rt R x y ↔ J.rt R x y := by
  cases R <;> exact Iff.rfl

theorem pull_path (J : Interp D C' Role) (f : CName → C') :
    ∀ (body : List (RoleT Role)) (x y : D), (pull J f).path body x y ↔ J.path body x y
  | [], x, y => Iff.rfl
  | R :: Rs, x, z => by
    simp only [Interp.path, pull_rt, pull_path J f Rs]

theorem satClause_mapC (J : Interp D C' Role) (f : CName → C') (cl : SRIQ.Clause CName Role) :
    SRIQ.satClause J (mapC f cl) ↔ SRIQ.satClause (pull J f) cl := by
  cases cl with
  | gci body head =>
    simp only [SRIQ.satClause, mapC, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, exists_exists_and_eq_and]
    rfl
  | exRight a R b => simp only [SRIQ.satClause, mapC, pull_rt]; rfl
  | allRight a R b => simp only [SRIQ.satClause, mapC, pull_rt]; rfl
  | atLeast a k R b => simp only [SRIQ.satClause, mapC, pull_rt]; rfl
  | atMost a k R b => simp only [SRIQ.satClause, mapC, pull_rt]; rfl
  | chain body S => simp only [SRIQ.satClause, mapC, pull_rt, pull_path]

theorem satClause_mapN (J : Interp D C' Role) (f : CName → C') (cl : Clause CName Role) :
    satClause J (mapN f cl) ↔ satClause (pull J f) cl := by
  cases cl with
  | base cl => exact satClause_mapC J f cl
  | nom a => exact Iff.rfl

theorem models_mapN (J : Interp D C' Role) (f : CName → C') (O : Ontology CName Role) :
    models J (O.map (mapN f)) ↔ models (pull J f) O := by
  simp only [models, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satClause_mapN]

end Rename

/-! ## The C2a condition (design section 7) -/

/-- **C2a.** No existential or at-least clause on a subject that is not
a nominal name has a role below the inverse of the role of an at-most
clause. -/
def IsC2a (O : Ontology CName Role) : Prop :=
  ∀ q ∈ SRIQ.lowerL (basePart O), q.1 ∉ noms O →
    ∀ q' ∈ SRIQ.upperL (basePart O), ¬ SRIQ.RoleLe (basePart O) q.2.2.1 q'.2.2.1.flip

end ContextCalculus.SRIQN
