/-! Semantic core of the sorted data-node abstraction.

A two-sorted OWL interpretation has object individuals `O` and data values `V`.
The abstraction reasons over one domain `U` in which data values are ordinary
nodes, data properties are ordinary roles, and every data range is a unary
predicate. A private predicate `obj` marks the object sort and every translated
class expression is relativised to it, so `owl:Thing`, complements, universal
and at-most restrictions never constrain a data node.

`abstract_exact` shows that any one-sorted interpretation with an adequate
value labelling induces a two-sorted interpretation with the same truth value
for every expression at every object. `canonical_exact` shows the converse for
the canonical one-sorted image of a two-sorted interpretation.

This module does not certify literal decoding, the datatype oracle that
justifies an adequate labelling, clause normalisation, or routing. -/
namespace ContextCalculus.SortedDataAbstraction

inductive SExpr (C R P G N : Type) where
  | atom : C → SExpr C R P G N
  | top : SExpr C R P G N
  | bottom : SExpr C R P G N
  | neg : SExpr C R P G N → SExpr C R P G N
  | conj : SExpr C R P G N → SExpr C R P G N → SExpr C R P G N
  | disj : SExpr C R P G N → SExpr C R P G N → SExpr C R P G N
  | some : R → SExpr C R P G N → SExpr C R P G N
  | all : R → SExpr C R P G N → SExpr C R P G N
  | min : Nat → R → SExpr C R P G N → SExpr C R P G N
  | max : Nat → R → SExpr C R P G N → SExpr C R P G N
  | nominal : N → SExpr C R P G N
  | self : R → SExpr C R P G N
  | dsome : P → G → SExpr C R P G N
  | dall : P → G → SExpr C R P G N
  | dmin : Nat → P → G → SExpr C R P G N
  | dmax : Nat → P → G → SExpr C R P G N

inductive TClass (C G : Type) where
  | cls : C → TClass C G
  | rng : G → TClass C G
  | obj : TClass C G

inductive TExpr (K S N : Type) where
  | atom : K → TExpr K S N
  | top : TExpr K S N
  | bottom : TExpr K S N
  | neg : TExpr K S N → TExpr K S N
  | conj : TExpr K S N → TExpr K S N → TExpr K S N
  | disj : TExpr K S N → TExpr K S N → TExpr K S N
  | some : S → TExpr K S N → TExpr K S N
  | all : S → TExpr K S N → TExpr K S N
  | min : Nat → S → TExpr K S N → TExpr K S N
  | max : Nat → S → TExpr K S N → TExpr K S N
  | nominal : N → TExpr K S N
  | self : S → TExpr K S N

variable {C R P G N O V U K S : Type}

def atLeast {α : Type} (n : Nat) (s : α → Prop) : Prop :=
  ∃ f : Fin n → α, (∀ i j, f i = f j → i = j) ∧ ∀ i, s (f i)

/-- Counting transfers along an injection that is onto the counted set. -/
theorem atLeast_transfer {α β : Type} (g : α → β)
    (ginj : ∀ a b, g a = g b → a = b) (s : α → Prop) (t : β → Prop)
    (hst : ∀ a, s a ↔ t (g a)) (onto : ∀ b, t b → ∃ a, g a = b) (n : Nat) :
    atLeast n s ↔ atLeast n t := by
  constructor
  · rintro ⟨f, finj, fs⟩
    exact ⟨fun i => g (f i), fun i j h => finj i j (ginj _ _ h), fun i => (hst _).1 (fs i)⟩
  · rintro ⟨f, finj, ft⟩
    have pick : ∀ i, ∃ a, g a = f i := fun i => onto _ (ft i)
    refine ⟨fun i => Classical.choose (pick i), ?_, ?_⟩
    · intro i j h
      apply finj
      have same : Classical.choose (pick i) = Classical.choose (pick j) := h
      calc f i = g (Classical.choose (pick i)) := (Classical.choose_spec (pick i)).symm
        _ = g (Classical.choose (pick j)) := congrArg g same
        _ = f j := Classical.choose_spec (pick j)
    · intro i
      apply (hst _).2
      rw [Classical.choose_spec (pick i)]
      exact ft i

theorem atLeast_congr {α : Type} (s t : α → Prop) (h : ∀ a, s a ↔ t a) (n : Nat) :
    atLeast n s ↔ atLeast n t :=
  atLeast_transfer id (fun _ _ e => e) s t h (fun b _ => ⟨b, rfl⟩) n

def sEval (classes : C → O → Prop) (roles : R → O → O → Prop)
    (data : P → O → V → Prop) (ranges : G → V → Prop) (names : N → O) :
    SExpr C R P G N → O → Prop
  | .atom c, x => classes c x
  | .top, _ => True
  | .bottom, _ => False
  | .neg e, x => ¬ sEval classes roles data ranges names e x
  | .conj a b, x => sEval classes roles data ranges names a x ∧
      sEval classes roles data ranges names b x
  | .disj a b, x => sEval classes roles data ranges names a x ∨
      sEval classes roles data ranges names b x
  | .some r e, x => ∃ y, roles r x y ∧ sEval classes roles data ranges names e y
  | .all r e, x => ∀ y, roles r x y → sEval classes roles data ranges names e y
  | .min n r e, x => atLeast n (fun y => roles r x y ∧ sEval classes roles data ranges names e y)
  | .max n r e, x =>
      ¬ atLeast (n+1) (fun y => roles r x y ∧ sEval classes roles data ranges names e y)
  | .nominal i, x => x = names i
  | .self r, x => roles r x x
  | .dsome p g, x => ∃ v, data p x v ∧ ranges g v
  | .dall p g, x => ∀ v, data p x v → ranges g v
  | .dmin n p g, x => atLeast n (fun v => data p x v ∧ ranges g v)
  | .dmax n p g, x => ¬ atLeast (n+1) (fun v => data p x v ∧ ranges g v)

def tEval (classes : K → U → Prop) (roles : S → U → U → Prop) (names : N → U) :
    TExpr K S N → U → Prop
  | .atom c, x => classes c x
  | .top, _ => True
  | .bottom, _ => False
  | .neg e, x => ¬ tEval classes roles names e x
  | .conj a b, x => tEval classes roles names a x ∧ tEval classes roles names b x
  | .disj a b, x => tEval classes roles names a x ∨ tEval classes roles names b x
  | .some r e, x => ∃ y, roles r x y ∧ tEval classes roles names e y
  | .all r e, x => ∀ y, roles r x y → tEval classes roles names e y
  | .min n r e, x => atLeast n (fun y => roles r x y ∧ tEval classes roles names e y)
  | .max n r e, x => ¬ atLeast (n+1) (fun y => roles r x y ∧ tEval classes roles names e y)
  | .nominal i, x => x = names i
  | .self r, x => roles r x x

def guard (e : TExpr (TClass C G) (Sum R P) N) : TExpr (TClass C G) (Sum R P) N :=
  .conj (.atom .obj) e

/-- Fully relativised translation. Every image implies `obj`. -/
def translate : SExpr C R P G N → TExpr (TClass C G) (Sum R P) N
  | .atom c => guard (.atom (.cls c))
  | .top => .atom .obj
  | .bottom => .bottom
  | .neg e => guard (.neg (translate e))
  | .conj a b => .conj (translate a) (translate b)
  | .disj a b => .disj (translate a) (translate b)
  | .some r e => guard (.some (.inl r) (translate e))
  | .all r e => guard (.all (.inl r) (.disj (.neg (.atom .obj)) (translate e)))
  | .min n r e => guard (.min n (.inl r) (translate e))
  | .max n r e => guard (.max n (.inl r) (translate e))
  | .nominal i => guard (.nominal i)
  | .self r => guard (.self (.inl r))
  | .dsome p g => guard (.some (.inr p) (.atom (.rng g)))
  | .dall p g => guard (.all (.inr p) (.atom (.rng g)))
  | .dmin n p g => guard (.min n (.inr p) (.atom (.rng g)))
  | .dmax n p g => guard (.max n (.inr p) (.atom (.rng g)))

theorem translate_obj (classes : TClass C G → U → Prop) (roles : Sum R P → U → U → Prop)
    (names : N → U) (e : SExpr C R P G N) (u : U)
    (h : tEval classes roles names (translate e) u) : classes .obj u := by
  induction e generalizing u with
  | top => exact h
  | bottom => exact h.elim
  | conj a b ia _ => exact ia u h.1
  | disj a b ia ib => exact h.elim (ia u) (ib u)
  | atom c => exact h.1
  | neg e _ => exact h.1
  | some r e _ => exact h.1
  | all r e _ => exact h.1
  | min n r e _ => exact h.1
  | max n r e _ => exact h.1
  | nominal i => exact h.1
  | self r => exact h.1
  | dsome p g => exact h.1
  | dall p g => exact h.1
  | dmin n p g => exact h.1
  | dmax n p g => exact h.1

section Abstract

variable (classes : TClass C G → U → Prop) (roles : Sum R P → U → U → Prop) (names : N → U)
variable (ranges : G → V → Prop) (label : U → V)

/-- A node reached from an object through a data property. -/
def DataSucc (u : U) : Prop := ∃ x p, classes .obj x ∧ roles (.inr p) x u

/-- The value labelling respects every data range and separates data nodes. -/
structure Adequate : Prop where
  named : ∀ i, classes .obj (names i)
  typed : ∀ g u, DataSucc classes roles u → (ranges g (label u) ↔ classes (.rng g) u)
  separated : ∀ u w, DataSucc classes roles u → DataSucc classes roles w →
    label u = label w → u = w

abbrev Obj := { u : U // classes .obj u }

def srcClasses (c : C) (x : Obj classes) : Prop := classes (.cls c) x.1
def srcRoles (r : R) (x y : Obj classes) : Prop := roles (.inl r) x.1 y.1
def srcData (p : P) (x : Obj classes) (v : V) : Prop := ∃ u, roles (.inr p) x.1 u ∧ label u = v
def srcNames (ok : Adequate classes roles names ranges label) (i : N) : Obj classes :=
  ⟨names i, ok.named i⟩

theorem data_count (ok : Adequate classes roles names ranges label)
    (p : P) (g : G) (x : Obj classes) (n : Nat) :
    atLeast n (fun v => srcData classes roles label p x v ∧ ranges g v) ↔
      atLeast n (fun u => roles (.inr p) x.1 u ∧ classes (.rng g) u) := by
  let D := { u : U // DataSucc classes roles u }
  have left : atLeast n (fun a : D => roles (.inr p) x.1 a.1 ∧ classes (.rng g) a.1) ↔
      atLeast n (fun v => srcData classes roles label p x v ∧ ranges g v) := by
    apply atLeast_transfer (fun a : D => label a.1)
    · intro a b h
      exact Subtype.ext (ok.separated a.1 b.1 a.2 b.2 h)
    · intro a
      constructor
      · rintro ⟨edge, inRange⟩
        exact ⟨⟨a.1, edge, rfl⟩, (ok.typed g a.1 a.2).2 inRange⟩
      · rintro ⟨⟨u, edge, same⟩, inRange⟩
        have isData : DataSucc classes roles u := ⟨x.1, p, x.2, edge⟩
        have eq : u = a.1 := ok.separated u a.1 isData a.2 same
        exact ⟨eq ▸ edge, (ok.typed g a.1 a.2).1 inRange⟩
    · rintro v ⟨⟨u, edge, same⟩, _⟩
      exact ⟨⟨u, x.1, p, x.2, edge⟩, same⟩
  have right : atLeast n (fun a : D => roles (.inr p) x.1 a.1 ∧ classes (.rng g) a.1) ↔
      atLeast n (fun u => roles (.inr p) x.1 u ∧ classes (.rng g) u) := by
    apply atLeast_transfer (fun a : D => a.1)
    · intro a b h
      exact Subtype.ext h
    · intro a
      exact Iff.rfl
    · rintro u ⟨edge, _⟩
      exact ⟨⟨u, x.1, p, x.2, edge⟩, rfl⟩
  exact left.symm.trans right

theorem object_count (e : SExpr C R P G N) (r : R) (x : Obj classes) (n : Nat)
    (s : Obj classes → Prop)
    (ih : ∀ y : Obj classes, s y ↔ tEval classes roles names (translate e) y.1) :
    atLeast n (fun y => srcRoles classes roles r x y ∧ s y) ↔
      atLeast n (fun u => roles (.inl r) x.1 u ∧ tEval classes roles names (translate e) u) := by
  apply atLeast_transfer (fun y : Obj classes => y.1)
  · intro a b h
    exact Subtype.ext h
  · intro y
    exact and_congr Iff.rfl (ih y)
  · rintro u ⟨_, holds⟩
    exact ⟨⟨u, translate_obj classes roles names e u holds⟩, rfl⟩

/-- An adequately labelled one-sorted interpretation and its induced two-sorted
interpretation agree on every expression at every object. -/
theorem abstract_exact (ok : Adequate classes roles names ranges label)
    (e : SExpr C R P G N) (x : Obj classes) :
    sEval (srcClasses classes) (srcRoles classes roles) (srcData classes roles label) ranges
        (srcNames classes roles names ranges label ok) e x ↔
      tEval classes roles names (translate e) x.1 := by
  induction e generalizing x with
  | atom c => exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  | top => exact ⟨fun _ => x.2, fun _ => trivial⟩
  | bottom => exact Iff.rfl
  | neg e ih => exact ⟨fun h => ⟨x.2, fun t => h ((ih x).2 t)⟩, fun h s => h.2 ((ih x).1 s)⟩
  | conj a b ia ib => exact and_congr (ia x) (ib x)
  | disj a b ia ib => exact or_congr (ia x) (ib x)
  | some r e ih =>
    constructor
    · rintro ⟨y, edge, holds⟩
      exact ⟨x.2, y.1, edge, (ih y).1 holds⟩
    · rintro ⟨_, u, edge, holds⟩
      exact ⟨⟨u, translate_obj classes roles names e u holds⟩, edge, (ih _).2 holds⟩
  | all r e ih =>
    constructor
    · intro h
      refine ⟨x.2, fun u edge => ?_⟩
      by_cases isObj : classes .obj u
      · exact Or.inr ((ih ⟨u, isObj⟩).1 (h ⟨u, isObj⟩ edge))
      · exact Or.inl isObj
    · rintro ⟨_, h⟩ y edge
      exact (h y.1 edge).elim (fun no => (no y.2).elim) (ih y).2
  | min n r e ih =>
    exact ⟨fun h => ⟨x.2, (object_count classes roles names e r x n _ ih).1 h⟩,
      fun h => (object_count classes roles names e r x n _ ih).2 h.2⟩
  | max n r e ih =>
    exact ⟨fun h => ⟨x.2, fun t => h ((object_count classes roles names e r x (n+1) _ ih).2 t)⟩,
      fun h s => h.2 ((object_count classes roles names e r x (n+1) _ ih).1 s)⟩
  | nominal i =>
    exact ⟨fun h => ⟨x.2, congrArg Subtype.val h⟩, fun h => Subtype.ext h.2⟩
  | self r => exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  | dsome p g =>
    constructor
    · rintro ⟨v, ⟨u, edge, same⟩, inRange⟩
      exact ⟨x.2, u, edge, (ok.typed g u ⟨x.1, p, x.2, edge⟩).1 (same ▸ inRange)⟩
    · rintro ⟨_, u, edge, inRange⟩
      exact ⟨label u, ⟨u, edge, rfl⟩, (ok.typed g u ⟨x.1, p, x.2, edge⟩).2 inRange⟩
  | dall p g =>
    constructor
    · intro h
      exact ⟨x.2, fun u edge => (ok.typed g u ⟨x.1, p, x.2, edge⟩).1 (h (label u) ⟨u, edge, rfl⟩)⟩
    · rintro ⟨_, h⟩ v ⟨u, edge, same⟩
      exact same ▸ (ok.typed g u ⟨x.1, p, x.2, edge⟩).2 (h u edge)
  | dmin n p g =>
    exact ⟨fun h => ⟨x.2, (data_count classes roles names ranges label ok p g x n).1 h⟩,
      fun h => (data_count classes roles names ranges label ok p g x n).2 h.2⟩
  | dmax n p g =>
    exact ⟨fun h => ⟨x.2, fun t => h ((data_count classes roles names ranges label ok p g x (n+1)).2 t)⟩,
      fun h s => h.2 ((data_count classes roles names ranges label ok p g x (n+1)).1 s)⟩

end Abstract

section Canonical

variable (classes : C → O → Prop) (roles : R → O → O → Prop) (data : P → O → V → Prop)
variable (ranges : G → V → Prop) (names : N → O)

/-- Canonical one-sorted image: objects and values side by side. -/
def canClasses : TClass C G → Sum O V → Prop
  | .cls c, .inl x => classes c x
  | .cls _, .inr _ => False
  | .rng _, .inl _ => False
  | .rng g, .inr v => ranges g v
  | .obj, .inl _ => True
  | .obj, .inr _ => False

def canRoles : Sum R P → Sum O V → Sum O V → Prop
  | .inl r, .inl x, .inl y => roles r x y
  | .inr p, .inl x, .inr v => data p x v
  | _, _, _ => False

def canNames (i : N) : Sum O V := .inl (names i)

theorem canonical_object_count (e : SExpr C R P G N) (r : R) (x : O) (n : Nat)
    (s : O → Prop)
    (ih : ∀ y, s y ↔ tEval (canClasses classes ranges) (canRoles roles data)
      (canNames (V := V) names) (translate e) (.inl y)) :
    atLeast n (fun y => roles r x y ∧ s y) ↔
      atLeast n (fun u => canRoles roles data (.inl r) (.inl x) u ∧
        tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
          (translate e) u) := by
  apply atLeast_transfer (fun y : O => (Sum.inl y : Sum O V))
  · intro a b h
    exact Sum.inl.inj h
  · intro y
    exact and_congr Iff.rfl (ih y)
  · rintro (y | v) ⟨edge, _⟩
    · exact ⟨y, rfl⟩
    · exact edge.elim

theorem canonical_data_count (p : P) (g : G) (x : O) (n : Nat) :
    atLeast n (fun v => data p x v ∧ ranges g v) ↔
      atLeast n (fun u => canRoles roles data (.inr p) (.inl x) u ∧
        canClasses classes ranges (.rng g) u) := by
  apply atLeast_transfer (fun v : V => (Sum.inr v : Sum O V))
  · intro a b h
    exact Sum.inr.inj h
  · intro v
    exact Iff.rfl
  · rintro (y | v) ⟨edge, _⟩
    · exact edge.elim
    · exact ⟨v, rfl⟩

/-- A two-sorted interpretation and its canonical image agree on every
expression at every object. -/
theorem canonical_exact (e : SExpr C R P G N) (x : O) :
    sEval classes roles data ranges names e x ↔
      tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
        (translate e) (.inl x) := by
  induction e generalizing x with
  | atom c => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | top => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | bottom => exact Iff.rfl
  | neg e ih => exact ⟨fun h => ⟨trivial, fun t => h ((ih x).2 t)⟩, fun h s => h.2 ((ih x).1 s)⟩
  | conj a b ia ib => exact and_congr (ia x) (ib x)
  | disj a b ia ib => exact or_congr (ia x) (ib x)
  | some r e ih =>
    constructor
    · rintro ⟨y, edge, holds⟩
      exact ⟨trivial, .inl y, edge, (ih y).1 holds⟩
    · rintro ⟨_, (y | v), edge, holds⟩
      · exact ⟨y, edge, (ih y).2 holds⟩
      · exact edge.elim
  | all r e ih =>
    constructor
    · intro h
      refine ⟨trivial, ?_⟩
      rintro (y | v) edge
      · exact Or.inr ((ih y).1 (h y edge))
      · exact edge.elim
    · rintro ⟨_, h⟩ y edge
      exact (h (.inl y) edge).elim (fun no => (no trivial).elim) (ih y).2
  | min n r e ih =>
    exact ⟨fun h => ⟨trivial, (canonical_object_count classes roles data ranges names e r x n _ ih).1 h⟩,
      fun h => (canonical_object_count classes roles data ranges names e r x n _ ih).2 h.2⟩
  | max n r e ih =>
    exact ⟨fun h => ⟨trivial, fun t =>
        h ((canonical_object_count classes roles data ranges names e r x (n+1) _ ih).2 t)⟩,
      fun h s => h.2 ((canonical_object_count classes roles data ranges names e r x (n+1) _ ih).1 s)⟩
  | nominal i => exact ⟨fun h => ⟨trivial, congrArg Sum.inl h⟩, fun h => Sum.inl.inj h.2⟩
  | self r => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | dsome p g =>
    constructor
    · rintro ⟨v, edge, inRange⟩
      exact ⟨trivial, .inr v, edge, inRange⟩
    · rintro ⟨_, (y | v), edge, inRange⟩
      · exact edge.elim
      · exact ⟨v, edge, inRange⟩
  | dall p g =>
    constructor
    · intro h
      refine ⟨trivial, ?_⟩
      rintro (y | v) edge
      · exact edge.elim
      · exact h v edge
    · rintro ⟨_, h⟩ v edge
      exact h (.inr v) edge
  | dmin n p g =>
    exact ⟨fun h => ⟨trivial, (canonical_data_count classes roles data ranges p g x n).1 h⟩,
      fun h => (canonical_data_count classes roles data ranges p g x n).2 h.2⟩
  | dmax n p g =>
    exact ⟨fun h => ⟨trivial, fun t => h ((canonical_data_count classes roles data ranges p g x (n+1)).2 t)⟩,
      fun h s => h.2 ((canonical_data_count classes roles data ranges p g x (n+1)).1 s)⟩

/-- The canonical image is adequately labelled whenever a default value exists. -/
theorem canonical_adequate (default : V) :
    Adequate (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names) ranges
      (fun u : Sum O V => match u with | .inl _ => default | .inr v => v) := by
  refine ⟨fun _ => trivial, ?_, ?_⟩
  · rintro g (y | v) ⟨x, p, _, edge⟩
    · cases x <;> exact edge.elim
    · exact Iff.rfl
  · rintro (y | v) (z | w) ⟨x, p, _, edge⟩ ⟨x', p', _, edge'⟩ same
    · cases x <;> exact edge.elim
    · cases x <;> exact edge.elim
    · cases x' <;> exact edge'.elim
    · exact congrArg Sum.inr same

end Canonical


/-! ## Plain translation with selective guards

The implementation does not relativise every subexpression. It keeps the source
expression shape (`plain`), adds `obj` only in front of an axiom whose left side
a data node could satisfy, and adds typing axioms that keep object-role
successors and named individuals inside `obj`. The statements below justify
that scheme. -/

/-- Shape-preserving translation: no guard anywhere. -/
def plain : SExpr C R P G N → TExpr (TClass C G) (Sum R P) N
  | .atom c => .atom (.cls c)
  | .top => .top
  | .bottom => .bottom
  | .neg e => .neg (plain e)
  | .conj a b => .conj (plain a) (plain b)
  | .disj a b => .disj (plain a) (plain b)
  | .some r e => .some (.inl r) (plain e)
  | .all r e => .all (.inl r) (plain e)
  | .min n r e => .min n (.inl r) (plain e)
  | .max n r e => .max n (.inl r) (plain e)
  | .nominal i => .nominal i
  | .self r => .self (.inl r)
  | .dsome p g => .some (.inr p) (.atom (.rng g))
  | .dall p g => .all (.inr p) (.atom (.rng g))
  | .dmin n p g => .min n (.inr p) (.atom (.rng g))
  | .dmax n p g => .max n (.inr p) (.atom (.rng g))

/-- Shape analysis at a canonical data node. The first component says the plain
image is false at every data node (the expression anchors its subject in the
object sort); the second says it is true at every data node. -/
def sortShape : SExpr C R P G N → Bool × Bool
  | .atom _ => (true, false)
  | .top => (false, true)
  | .bottom => (true, false)
  | .neg e => ((sortShape e).2, (sortShape e).1)
  | .conj a b => ((sortShape a).1 || (sortShape b).1, (sortShape a).2 && (sortShape b).2)
  | .disj a b => ((sortShape a).1 && (sortShape b).1, (sortShape a).2 || (sortShape b).2)
  | .some _ _ => (true, false)
  | .all _ _ => (false, true)
  | .min n _ _ => (n != 0, n == 0)
  | .max _ _ _ => (false, true)
  | .nominal _ => (true, false)
  | .self _ => (true, false)
  | .dsome _ _ => (true, false)
  | .dall _ _ => (false, true)
  | .dmin n _ _ => (n != 0, n == 0)
  | .dmax _ _ _ => (false, true)

theorem or_true_cases (a b : Bool) (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

theorem and_true_both (a b : Bool) (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem atLeast_zero {α : Type} (s : α → Prop) : atLeast 0 s :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem atLeast_witness {α : Type} {n : Nat} {s : α → Prop} (pos : n ≠ 0)
    (h : atLeast n s) : ∃ a, s a := by
  obtain ⟨f, _, fs⟩ := h
  exact ⟨f ⟨0, Nat.pos_of_ne_zero pos⟩, fs _⟩

section CanonicalPlain

variable (classes : C → O → Prop) (roles : R → O → O → Prop) (data : P → O → V → Prop)
variable (ranges : G → V → Prop) (names : N → O)

theorem canonical_no_edge (s : Sum R P) (v : V) (u : Sum O V) :
    ¬ canRoles roles data s (.inr v) u := by
  intro edge
  cases s <;> cases u <;> exact edge.elim

theorem canonical_no_count (s : Sum R P) (v : V) (n : Nat) (pos : n ≠ 0)
    (t : Sum O V → Prop) :
    ¬ atLeast n (fun u => canRoles roles data s (.inr v) u ∧ t u) := by
  intro h
  obtain ⟨u, edge, _⟩ := atLeast_witness pos h
  exact canonical_no_edge roles data s v u edge

/-- The shape analysis is sound at every canonical data node. -/
theorem sortShape_sound (e : SExpr C R P G N) (v : V) :
    ((sortShape e).1 = true →
      ¬ tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
        (plain e) (.inr v)) ∧
    ((sortShape e).2 = true →
      tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
        (plain e) (.inr v)) := by
  induction e with
  | atom c => exact ⟨fun _ h => h, fun h => Bool.noConfusion h⟩
  | top => exact ⟨fun h => Bool.noConfusion h, fun _ => trivial⟩
  | bottom => exact ⟨fun _ h => h, fun h => Bool.noConfusion h⟩
  | neg e ih => exact ⟨fun h no => no (ih.2 h), fun h => ih.1 h⟩
  | conj a b ia ib =>
    constructor
    · intro h holds
      rcases or_true_cases _ _ h with ha | hb
      · exact ia.1 ha holds.1
      · exact ib.1 hb holds.2
    · intro h
      have both := and_true_both _ _ h
      exact ⟨ia.2 both.1, ib.2 both.2⟩
  | disj a b ia ib =>
    constructor
    · intro h holds
      have both := and_true_both _ _ h
      exact holds.elim (ia.1 both.1) (ib.1 both.2)
    · intro h
      rcases or_true_cases _ _ h with ha | hb
      · exact Or.inl (ia.2 ha)
      · exact Or.inr (ib.2 hb)
  | some r e _ =>
    exact ⟨fun _ ⟨u, edge, _⟩ => canonical_no_edge roles data _ v u edge,
      fun h => Bool.noConfusion h⟩
  | all r e _ =>
    exact ⟨fun h => Bool.noConfusion h,
      fun _ u edge => (canonical_no_edge roles data _ v u edge).elim⟩
  | min n r e _ =>
    constructor
    · intro h
      have pos : n ≠ 0 := by simpa [sortShape] using h
      exact canonical_no_count roles data _ v n pos _
    · intro h
      have zero : n = 0 := by simpa [sortShape] using h
      subst zero
      exact atLeast_zero _
  | max n r e _ =>
    exact ⟨fun h => Bool.noConfusion h,
      fun _ => canonical_no_count roles data _ v (n+1) (Nat.succ_ne_zero n) _⟩
  | nominal i =>
    refine ⟨fun _ h => ?_, fun h => Bool.noConfusion h⟩
    change (Sum.inr v : Sum O V) = Sum.inl (names i) at h
    cases h
  | self r => exact ⟨fun _ h => h, fun h => Bool.noConfusion h⟩
  | dsome p g =>
    exact ⟨fun _ ⟨u, edge, _⟩ => canonical_no_edge roles data _ v u edge,
      fun h => Bool.noConfusion h⟩
  | dall p g =>
    exact ⟨fun h => Bool.noConfusion h,
      fun _ u edge => (canonical_no_edge roles data _ v u edge).elim⟩
  | dmin n p g =>
    constructor
    · intro h
      have pos : n ≠ 0 := by simpa [sortShape] using h
      exact canonical_no_count roles data _ v n pos _
    · intro h
      have zero : n = 0 := by simpa [sortShape] using h
      subst zero
      exact atLeast_zero _
  | dmax n p g =>
    exact ⟨fun h => Bool.noConfusion h,
      fun _ => canonical_no_count roles data _ v (n+1) (Nat.succ_ne_zero n) _⟩

end CanonicalPlain


section PlainExact

variable (classes : C → O → Prop) (roles : R → O → O → Prop) (data : P → O → V → Prop)
variable (ranges : G → V → Prop) (names : N → O)

theorem canonical_plain_count (r : R) (x : O) (n : Nat) (s : O → Prop) (t : Sum O V → Prop)
    (ih : ∀ y, s y ↔ t (.inl y)) :
    atLeast n (fun y => roles r x y ∧ s y) ↔
      atLeast n (fun u => canRoles roles data (.inl r) (.inl x) u ∧ t u) := by
  apply atLeast_transfer (fun y : O => (Sum.inl y : Sum O V))
  · intro a b h
    exact Sum.inl.inj h
  · intro y
    exact and_congr Iff.rfl (ih y)
  · rintro (y | v) ⟨edge, _⟩
    · exact ⟨y, rfl⟩
    · exact edge.elim

/-- In the canonical image the unguarded translation is exact at every object. -/
theorem canonical_plain_exact (e : SExpr C R P G N) (x : O) :
    sEval classes roles data ranges names e x ↔
      tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
        (plain e) (.inl x) := by
  induction e generalizing x with
  | atom c => exact Iff.rfl
  | top => exact Iff.rfl
  | bottom => exact Iff.rfl
  | neg e ih => exact not_congr (ih x)
  | conj a b ia ib => exact and_congr (ia x) (ib x)
  | disj a b ia ib => exact or_congr (ia x) (ib x)
  | some r e ih =>
    constructor
    · rintro ⟨y, edge, holds⟩
      exact ⟨.inl y, edge, (ih y).1 holds⟩
    · rintro ⟨(y | v), edge, holds⟩
      · exact ⟨y, edge, (ih y).2 holds⟩
      · exact edge.elim
  | all r e ih =>
    constructor
    · intro h
      rintro (y | v) edge
      · exact (ih y).1 (h y edge)
      · exact edge.elim
    · intro h y edge
      exact (ih y).2 (h (.inl y) edge)
  | min n r e ih => exact canonical_plain_count roles data r x n _ _ ih
  | max n r e ih => exact not_congr (canonical_plain_count roles data r x (n+1) _ _ ih)
  | nominal i => exact ⟨fun h => congrArg Sum.inl h, fun h => Sum.inl.inj h⟩
  | self r => exact Iff.rfl
  | dsome p g =>
    constructor
    · rintro ⟨v, edge, inRange⟩
      exact ⟨.inr v, edge, inRange⟩
    · rintro ⟨(y | v), edge, inRange⟩
      · exact edge.elim
      · exact ⟨v, edge, inRange⟩
  | dall p g =>
    constructor
    · intro h
      rintro (y | v) edge
      · exact edge.elim
      · exact h v edge
    · intro h v edge
      exact h (.inr v) edge
  | dmin n p g => exact canonical_data_count classes roles data ranges p g x n
  | dmax n p g => exact not_congr (canonical_data_count classes roles data ranges p g x (n+1))

/-- A source axiom `sub ⊑ sup`, emitted unguarded when its shape makes it true at
every data node and guarded by `obj` otherwise, holds throughout the canonical
image of any two-sorted model of that axiom. -/
theorem canonical_axiom (sub sup : SExpr C R P G N)
    (source : ∀ x, sEval classes roles data ranges names sub x →
      sEval classes roles data ranges names sup x)
    (guarded : Bool)
    (shape : guarded = false → (sortShape sub).1 = true ∨ (sortShape sup).2 = true)
    (u : Sum O V)
    (isObj : guarded = true → canClasses classes ranges .obj u)
    (holds : tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
      (plain sub) u) :
    tEval (canClasses classes ranges) (canRoles roles data) (canNames (V := V) names)
      (plain sup) u := by
  cases u with
  | inl x =>
    exact (canonical_plain_exact classes roles data ranges names sup x).1
      (source x ((canonical_plain_exact classes roles data ranges names sub x).2 holds))
  | inr v =>
    cases guarded with
    | true => exact (isObj rfl).elim
    | false =>
      rcases shape rfl with anchored | vacuous
      · exact ((sortShape_sound classes roles data ranges names sub v).1 anchored holds).elim
      · exact (sortShape_sound classes roles data ranges names sup v).2 vacuous

end PlainExact

section TypedPlain

variable (classes : TClass C G → U → Prop) (roles : Sum R P → U → U → Prop) (names : N → U)
variable (ranges : G → V → Prop) (label : U → V)

theorem typed_plain_count (typed : ∀ r x y, classes .obj x → roles (.inl r) x y → classes .obj y)
    (r : R) (x : Obj classes) (n : Nat) (s : Obj classes → Prop) (t : U → Prop)
    (ih : ∀ y : Obj classes, s y ↔ t y.1) :
    atLeast n (fun y => srcRoles classes roles r x y ∧ s y) ↔
      atLeast n (fun u => roles (.inl r) x.1 u ∧ t u) := by
  apply atLeast_transfer (fun y : Obj classes => y.1)
  · intro a b h
    exact Subtype.ext h
  · intro y
    exact and_congr Iff.rfl (ih y)
  · rintro u ⟨edge, _⟩
    exact ⟨⟨u, typed r x.1 u x.2 edge⟩, rfl⟩

/-- If object-role successors of objects are objects, the unguarded translation
is exact at every object of an adequately labelled interpretation. -/
theorem typed_plain_exact (ok : Adequate classes roles names ranges label)
    (typed : ∀ r x y, classes .obj x → roles (.inl r) x y → classes .obj y)
    (e : SExpr C R P G N) (x : Obj classes) :
    sEval (srcClasses classes) (srcRoles classes roles) (srcData classes roles label) ranges
        (srcNames classes roles names ranges label ok) e x ↔
      tEval classes roles names (plain e) x.1 := by
  induction e generalizing x with
  | atom c => exact Iff.rfl
  | top => exact Iff.rfl
  | bottom => exact Iff.rfl
  | neg e ih => exact not_congr (ih x)
  | conj a b ia ib => exact and_congr (ia x) (ib x)
  | disj a b ia ib => exact or_congr (ia x) (ib x)
  | some r e ih =>
    constructor
    · rintro ⟨y, edge, holds⟩
      exact ⟨y.1, edge, (ih y).1 holds⟩
    · rintro ⟨u, edge, holds⟩
      exact ⟨⟨u, typed r x.1 u x.2 edge⟩, edge, (ih _).2 holds⟩
  | all r e ih =>
    constructor
    · intro h u edge
      exact (ih ⟨u, typed r x.1 u x.2 edge⟩).1 (h ⟨u, typed r x.1 u x.2 edge⟩ edge)
    · intro h y edge
      exact (ih y).2 (h y.1 edge)
  | min n r e ih => exact typed_plain_count classes roles typed r x n _ _ ih
  | max n r e ih => exact not_congr (typed_plain_count classes roles typed r x (n+1) _ _ ih)
  | nominal i => exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  | self r => exact Iff.rfl
  | dsome p g =>
    constructor
    · rintro ⟨v, ⟨u, edge, same⟩, inRange⟩
      exact ⟨u, edge, (ok.typed g u ⟨x.1, p, x.2, edge⟩).1 (same ▸ inRange)⟩
    · rintro ⟨u, edge, inRange⟩
      exact ⟨label u, ⟨u, edge, rfl⟩, (ok.typed g u ⟨x.1, p, x.2, edge⟩).2 inRange⟩
  | dall p g =>
    constructor
    · intro h u edge
      exact (ok.typed g u ⟨x.1, p, x.2, edge⟩).1 (h (label u) ⟨u, edge, rfl⟩)
    · rintro h v ⟨u, edge, same⟩
      exact same ▸ (ok.typed g u ⟨x.1, p, x.2, edge⟩).2 (h u edge)
  | dmin n p g => exact data_count classes roles names ranges label ok p g x n
  | dmax n p g => exact not_congr (data_count classes roles names ranges label ok p g x (n+1))

/-- Any emitted axiom, guarded or not, yields the source axiom in the induced
two-sorted interpretation. -/
theorem abstract_axiom (ok : Adequate classes roles names ranges label)
    (typed : ∀ r x y, classes .obj x → roles (.inl r) x y → classes .obj y)
    (sub sup : SExpr C R P G N)
    (emitted : ∀ u, classes .obj u → tEval classes roles names (plain sub) u →
      tEval classes roles names (plain sup) u)
    (x : Obj classes)
    (holds : sEval (srcClasses classes) (srcRoles classes roles) (srcData classes roles label)
      ranges (srcNames classes roles names ranges label ok) sub x) :
    sEval (srcClasses classes) (srcRoles classes roles) (srcData classes roles label) ranges
      (srcNames classes roles names ranges label ok) sup x :=
  (typed_plain_exact classes roles names ranges label ok typed sup x).2
    (emitted x.1 x.2 ((typed_plain_exact classes roles names ranges label ok typed sub x).1 holds))

end TypedPlain

#print axioms canonical_plain_exact
#print axioms canonical_axiom
#print axioms typed_plain_exact
#print axioms abstract_axiom

#print axioms sortShape_sound

#print axioms abstract_exact
#print axioms canonical_exact
#print axioms canonical_adequate
end ContextCalculus.SortedDataAbstraction
