/-!
# A two-sorted description-logic language for data values

The data-value encodings of `docs/DATATYPES.md` ("Exact data values without a
literal cap", v1.5.5) are stated over OWL 2 Direct Semantics with an object
domain and a data domain (`docs/NOMINALS-CB.md` section 6): classes and object
properties live on the object sort, data properties relate objects to data
elements, and data ranges (`__dt__` concepts: datatypes, facet restrictions,
value concepts) are unary predicates on the data sort.

This file fixes that language once for the two theorems that use it:

* `ContextCalculus.DataValueProjection` (object-level projection of data
  assertions, `engine/src/frontend/value_projection.rs`);
* `ContextCalculus.DataValueSingletonElision` (value-singleton elision,
  `literal_profiles::distinct_data_successors_forced`).

An interpretation has an arbitrary object type `Obj` and an arbitrary data type
`Dat`, and interprets the data concept names freely (`dcon`). The OWL reading
fixes `Dat` to a value space and `dcon` to the datatype map; the clause reading
(the frontend's clause set, whose data nodes are abstract terms carrying
`__dt__` labels) leaves both free. Both theorems are statements about these two
readings of one syntax.

Data ranges are atomic (`⊤` or a `__dt__` name): the frontend names every
complex data range (`__dt__c__<text>`), and `DatatypeDefinition` is inlined
before the gates run. Counting is over distinct successors (`AtLeast`).

Core Lean only.
-/

namespace ContextCalculus.TwoSortedDL

/-- A data range: `⊤` (`rdfs:Literal`, the unqualified filler) or a `__dt__`
concept name. -/
inductive DRange (DN : Type) where
  | top
  | name (d : DN)
  deriving DecidableEq

/-- Class expressions over class names `Cls`, object roles `OR`, data roles
`DR`, individuals `Ind` and data concept names `DN`. -/
inductive Concept (Cls OR DR Ind DN : Type) where
  | top
  | bot
  | atom (a : Cls)
  | nominal (i : Ind)
  | not (c : Concept Cls OR DR Ind DN)
  | and (c d : Concept Cls OR DR Ind DN)
  | or (c d : Concept Cls OR DR Ind DN)
  | oex (r : OR) (c : Concept Cls OR DR Ind DN)
  | oall (r : OR) (c : Concept Cls OR DR Ind DN)
  | oge (n : Nat) (r : OR) (c : Concept Cls OR DR Ind DN)
  | ole (n : Nat) (r : OR) (c : Concept Cls OR DR Ind DN)
  | oself (r : OR)
  | dex (u : DR) (R : DRange DN)
  | dall (u : DR) (R : DRange DN)
  | dge (n : Nat) (u : DR) (R : DRange DN)
  | dle (n : Nat) (u : DR) (R : DRange DN)
  deriving DecidableEq

/-- Axioms. Functionality of a data property is `⊤ ⊑ ≤ 1 u.⊤`, its domain
`∃u.⊤ ⊑ C`, its range `⊤ ⊑ ∀u.R`; a negative data assertion is the class
assertion `¬∃u.{v}`. `HasKey` and DL-safe rules are not in the language. -/
inductive Axiom (Cls OR DR Ind DN : Type) where
  | sub (c d : Concept Cls OR DR Ind DN)
  | cassert (c : Concept Cls OR DR Ind DN) (a : Ind)
  | oassert (r : OR) (a b : Ind)
  | dassert (u : DR) (a : Ind) (v : DN)
  | osub (r s : OR)
  | dsub (u w : DR)
  | ddisj (u w : DR)
  | same (a b : Ind)
  | diff (a b : Ind)
  deriving DecidableEq

variable {Cls OR DR Ind DN : Type}

/-- A two-sorted interpretation. -/
structure Interp (Cls OR DR Ind DN : Type) (Obj Dat : Type) where
  cls : Cls → Obj → Prop
  orole : OR → Obj → Obj → Prop
  drole : DR → Obj → Dat → Prop
  ind : Ind → Obj
  dcon : DN → Dat → Prop

/-- `n` pairwise distinct elements satisfy `P`. -/
def AtLeast {α : Type} (n : Nat) (P : α → Prop) : Prop :=
  ∃ f : Fin n → α, (∀ i j, f i = f j → i = j) ∧ ∀ i, P (f i)

theorem AtLeast.mono {α : Type} {n : Nat} {P Q : α → Prop} (h : ∀ y, P y → Q y) :
    AtLeast n P → AtLeast n Q := by
  intro ⟨f, inj, hp⟩
  exact ⟨f, inj, fun i => h _ (hp i)⟩

theorem AtLeast.zero {α : Type} (P : α → Prop) : AtLeast 0 P :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem AtLeast.one_iff {α : Type} (P : α → Prop) : AtLeast 1 P ↔ ∃ y, P y := by
  constructor
  · intro ⟨f, _, hp⟩
    exact ⟨f ⟨0, by decide⟩, hp _⟩
  · intro ⟨y, hy⟩
    refine ⟨fun _ => y, ?_, fun _ => hy⟩
    intro i j _
    apply Fin.ext
    have := i.isLt; have := j.isLt; omega

/-- Two distinct elements satisfy `P`. -/
theorem AtLeast.two_iff {α : Type} (P : α → Prop) :
    AtLeast 2 P ↔ ∃ y z, y ≠ z ∧ P y ∧ P z := by
  constructor
  · intro ⟨f, inj, hp⟩
    refine ⟨f ⟨0, by decide⟩, f ⟨1, by decide⟩, ?_, hp _, hp _⟩
    intro h
    have := inj _ _ h
    simp at this
  · intro ⟨y, z, hne, hy, hz⟩
    refine ⟨fun i => if i.val = 0 then y else z, ?_, ?_⟩
    · intro i j h
      apply Fin.ext
      have hi := i.isLt; have hj := j.isLt
      by_cases a : i.val = 0 <;> by_cases b : j.val = 0 <;> simp [a, b] at h
      · omega
      · exact absurd h hne
      · exact absurd h.symm hne
      · omega
    · intro i
      by_cases a : i.val = 0 <;> simp [a, hy, hz]

/-- Pulling `n` distinct images back along a map gives `n` distinct
preimages. -/
theorem AtLeast.of_image {α β : Type} {n : Nat} (g : α → β) {P : α → Prop} {Q : β → Prop}
    (h : ∀ y, Q y → ∃ x, P x ∧ g x = y) : AtLeast n Q → AtLeast n P := by
  intro ⟨f, inj, hq⟩
  refine ⟨fun i => Classical.choose (h (f i) (hq i)), ?_, ?_⟩
  · intro i j hij
    apply inj
    have hi := (Classical.choose_spec (h (f i) (hq i))).2
    have hj := (Classical.choose_spec (h (f j) (hq j))).2
    rw [← hi, ← hj]
    exact congrArg g hij
  · intro i
    exact (Classical.choose_spec (h (f i) (hq i))).1

section Semantics
variable {Obj Dat : Type} (I : Interp Cls OR DR Ind DN Obj Dat)

def evalR : DRange DN → Dat → Prop
  | .top, _ => True
  | .name d, y => I.dcon d y

def eval : Concept Cls OR DR Ind DN → Obj → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom a, x => I.cls a x
  | .nominal i, x => x = I.ind i
  | .not c, x => ¬ eval c x
  | .and c d, x => eval c x ∧ eval d x
  | .or c d, x => eval c x ∨ eval d x
  | .oex r c, x => ∃ y, I.orole r x y ∧ eval c y
  | .oall r c, x => ∀ y, I.orole r x y → eval c y
  | .oge n r c, x => AtLeast n (fun y => I.orole r x y ∧ eval c y)
  | .ole n r c, x => ¬ AtLeast (n + 1) (fun y => I.orole r x y ∧ eval c y)
  | .oself r, x => I.orole r x x
  | .dex u R, x => ∃ y, I.drole u x y ∧ evalR I R y
  | .dall u R, x => ∀ y, I.drole u x y → evalR I R y
  | .dge n u R, x => AtLeast n (fun y => I.drole u x y ∧ evalR I R y)
  | .dle n u R, x => ¬ AtLeast (n + 1) (fun y => I.drole u x y ∧ evalR I R y)

def sat : Axiom Cls OR DR Ind DN → Prop
  | .sub c d => ∀ x, eval I c x → eval I d x
  | .cassert c a => eval I c (I.ind a)
  | .oassert r a b => I.orole r (I.ind a) (I.ind b)
  | .dassert u a v => ∃ y, I.drole u (I.ind a) y ∧ I.dcon v y
  | .osub r s => ∀ x y, I.orole r x y → I.orole s x y
  | .dsub u w => ∀ x y, I.drole u x y → I.drole w x y
  | .ddisj u w => ∀ x y, I.drole u x y → I.drole w x y → False
  | .same a b => I.ind a = I.ind b
  | .diff a b => I.ind a ≠ I.ind b

/-- `I` is a model of the axiom list `O`. -/
def Models (O : List (Axiom Cls OR DR Ind DN)) : Prop := ∀ ax ∈ O, sat I ax

end Semantics

/-- The OWL reading: the data sort is the value space `Val` and every data
concept name has its datatype-map denotation `den`. -/
def Interp.IsReal {Obj Val : Type} (den : DN → Val → Prop)
    (I : Interp Cls OR DR Ind DN Obj Val) : Prop :=
  I.dcon = den

/-- Two interpretations with one object part: same classes, object roles and
individuals (data roles and data labels may differ). -/
def SameObjectPart {Obj D₁ D₂ : Type} (I : Interp Cls OR DR Ind DN Obj D₁)
    (J : Interp Cls OR DR Ind DN Obj D₂) : Prop :=
  I.cls = J.cls ∧ I.orole = J.orole ∧ I.ind = J.ind

/-! ## Renaming class names

The projection adds fresh index classes; we model freshness by moving the
source class names into the left summand of `Cls ⊕ X`. -/

def Concept.mapCls {Cls' : Type} (f : Cls → Cls') :
    Concept Cls OR DR Ind DN → Concept Cls' OR DR Ind DN
  | .top => .top
  | .bot => .bot
  | .atom a => .atom (f a)
  | .nominal i => .nominal i
  | .not c => .not (c.mapCls f)
  | .and c d => .and (c.mapCls f) (d.mapCls f)
  | .or c d => .or (c.mapCls f) (d.mapCls f)
  | .oex r c => .oex r (c.mapCls f)
  | .oall r c => .oall r (c.mapCls f)
  | .oge n r c => .oge n r (c.mapCls f)
  | .ole n r c => .ole n r (c.mapCls f)
  | .oself r => .oself r
  | .dex u R => .dex u R
  | .dall u R => .dall u R
  | .dge n u R => .dge n u R
  | .dle n u R => .dle n u R

def Axiom.mapCls {Cls' : Type} (f : Cls → Cls') :
    Axiom Cls OR DR Ind DN → Axiom Cls' OR DR Ind DN
  | .sub c d => .sub (c.mapCls f) (d.mapCls f)
  | .cassert c a => .cassert (c.mapCls f) a
  | .oassert r a b => .oassert r a b
  | .dassert u a v => .dassert u a v
  | .osub r s => .osub r s
  | .dsub u w => .dsub u w
  | .ddisj u w => .ddisj u w
  | .same a b => .same a b
  | .diff a b => .diff a b

/-- Pull an interpretation back along a class renaming. -/
def Interp.comapCls {Cls' Obj Dat : Type} (f : Cls → Cls')
    (I : Interp Cls' OR DR Ind DN Obj Dat) : Interp Cls OR DR Ind DN Obj Dat :=
  { I with cls := fun a => I.cls (f a) }

theorem eval_mapCls {Cls' Obj Dat : Type} (f : Cls → Cls')
    (I : Interp Cls' OR DR Ind DN Obj Dat) :
    ∀ (c : Concept Cls OR DR Ind DN) x, eval I (c.mapCls f) x ↔ eval (I.comapCls f) c x := by
  intro c
  induction c with
  | top => intro x; exact Iff.rfl
  | bot => intro x; exact Iff.rfl
  | atom a => intro x; exact Iff.rfl
  | nominal i => intro x; exact Iff.rfl
  | not c ih => intro x; exact not_congr (ih x)
  | and c d ihc ihd => intro x; exact and_congr (ihc x) (ihd x)
  | or c d ihc ihd => intro x; exact or_congr (ihc x) (ihd x)
  | oex r c ih =>
    intro x
    exact exists_congr fun y => and_congr Iff.rfl (ih y)
  | oall r c ih =>
    intro x
    exact forall_congr' fun y => imp_congr Iff.rfl (ih y)
  | oge n r c ih =>
    intro x
    exact ⟨AtLeast.mono (fun y h => ⟨h.1, (ih y).1 h.2⟩),
      AtLeast.mono (fun y h => ⟨h.1, (ih y).2 h.2⟩)⟩
  | ole n r c ih =>
    intro x
    exact not_congr ⟨AtLeast.mono (fun y h => ⟨h.1, (ih y).1 h.2⟩),
      AtLeast.mono (fun y h => ⟨h.1, (ih y).2 h.2⟩)⟩
  | oself r => intro x; exact Iff.rfl
  | dex u R =>
    intro x
    cases R <;> exact Iff.rfl
  | dall u R =>
    intro x
    cases R <;> exact Iff.rfl
  | dge n u R =>
    intro x
    cases R <;> exact Iff.rfl
  | dle n u R =>
    intro x
    cases R <;> exact Iff.rfl

theorem sat_mapCls {Cls' Obj Dat : Type} (f : Cls → Cls')
    (I : Interp Cls' OR DR Ind DN Obj Dat) (ax : Axiom Cls OR DR Ind DN) :
    sat I (ax.mapCls f) ↔ sat (I.comapCls f) ax := by
  cases ax with
  | sub c d =>
    exact forall_congr' fun x => imp_congr (eval_mapCls f I c x) (eval_mapCls f I d x)
  | cassert c a => exact eval_mapCls f I c _
  | _ => exact Iff.rfl

end ContextCalculus.TwoSortedDL
