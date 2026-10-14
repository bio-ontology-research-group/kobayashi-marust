import ContextCalculus.IsolatedObjectModelExtension

/-! Countermodel refutation used by the native bridge's possible-subsumer
verification. A complete clash-free completion model of the subject (the
satisfiability read-off or a satisfiable `s and not c` pair probe) is a model of
the ontology in which the root satisfies the subject. Three facts make a single
such model answer further candidate pairs without another probe:

* `countermodel_refutes`: a model of the ontology whose element satisfies `s`
  and not `d` refutes `s <= d`.
* `known_super_refutes`: if `c <= d` holds in every model, a countermodel of
  `s <= d` is also one of `s <= c`.
* `marker_refutes_host`: for a defined host `A == D` and a concept `T` with
  `D <= T`, a model that interprets a marker `M` so that `T <= M` and whose
  element lacks `M` has that element outside `A`.

`marker_extension_conservative` and `marker_extension_implies` justify adding
the partial-equivalence marker: interpreting a fresh class `M` as `T` changes
no concept that does not mention `M` and satisfies `T <= M`. -/
namespace ContextCalculus.CandidateModelRefutation

open ContextCalculus.IsolatedObjectModelExtension

/-- `s <= d` in every model accepted by `Sat`. -/
def Entails {Class Role Object : Type} (Sat : Model Class Role Object → Prop)
    (s d : Concept Class Role) : Prop :=
  ∀ model, Sat model → ∀ x, holds model s x → holds model d x

theorem countermodel_refutes {Class Role Object : Type}
    (Sat : Model Class Role Object → Prop) (s d : Concept Class Role)
    (model : Model Class Role Object) (sat : Sat model) (x : Object)
    (hs : holds model s x) (hd : ¬holds model d x) : ¬Entails Sat s d :=
  fun entails => hd (entails model sat x hs)

theorem known_super_refutes {Class Role Object : Type}
    (Sat : Model Class Role Object → Prop) (s c d : Concept Class Role)
    (known : Entails Sat c d) (model : Model Class Role Object) (sat : Sat model)
    (x : Object) (hs : holds model s x) (hd : ¬holds model d x) :
    ¬Entails Sat s c := by
  intro entails
  exact hd (known model sat x (entails model sat x hs))

/-- Conjuncts of a definition are necessary conditions of it. -/
theorem and_left_necessary {Class Role Object : Type} (model : Model Class Role Object)
    (left right : Concept Class Role) (x : Object) :
    holds model (.and left right) x → holds model left x := fun h => h.1

theorem and_right_necessary {Class Role Object : Type} (model : Model Class Role Object)
    (left right : Concept Class Role) (x : Object) :
    holds model (.and left right) x → holds model right x := fun h => h.2

theorem marker_refutes_host {Class Role Object : Type} (model : Model Class Role Object)
    (host marker : Class) (definition trigger : Concept Class Role)
    (defined : ∀ x, model.concept host x ↔ holds model definition x)
    (necessary : ∀ x, holds model definition x → holds model trigger x)
    (implied : ∀ x, holds model trigger x → model.concept marker x)
    (x : Object) (lacks : ¬model.concept marker x) : ¬model.concept host x :=
  fun h => lacks (implied x (necessary x ((defined x).mp h)))

/-- `concept` does not mention the class `marker`. -/
def Avoids {Class Role : Type} (marker : Class) : Concept Class Role → Prop
  | .top | .bottom | .self _ => True
  | .atom name => name ≠ marker
  | .neg inner => Avoids marker inner
  | .and left right | .or left right => Avoids marker left ∧ Avoids marker right
  | .some _ filler | .all _ filler | .min _ _ filler | .max _ _ filler => Avoids marker filler

/-- Interpret the fresh `marker` as `trigger`; everything else is unchanged. -/
def withMarker {Class Role Object : Type} [DecidableEq Class]
    (model : Model Class Role Object) (marker : Class) (trigger : Concept Class Role) :
    Model Class Role Object where
  concept := fun name x => if name = marker then holds model trigger x else model.concept name x
  role := model.role

theorem marker_extension_conservative {Class Role Object : Type} [DecidableEq Class]
    (model : Model Class Role Object) (marker : Class) (trigger : Concept Class Role)
    (concept : Concept Class Role) (avoids : Avoids marker concept) (x : Object) :
    holds (withMarker model marker trigger) concept x ↔ holds model concept x := by
  induction concept generalizing x with
  | top | bottom | self => rfl
  | atom name =>
    show (if name = marker then holds model trigger x else model.concept name x) ↔ _
    rw [if_neg avoids]
    rfl
  | neg inner ih => exact not_congr (ih avoids x)
  | and left right ihLeft ihRight =>
    exact and_congr (ihLeft avoids.1 x) (ihRight avoids.2 x)
  | or left right ihLeft ihRight =>
    exact or_congr (ihLeft avoids.1 x) (ihRight avoids.2 x)
  | some role filler ih =>
    exact exists_congr fun y => and_congr Iff.rfl (ih avoids y)
  | all role filler ih =>
    exact forall_congr' fun y => imp_congr Iff.rfl (ih avoids y)
  | min n role filler ih =>
    show count _ n ↔ count _ n
    have same : (fun y => (withMarker model marker trigger).role role x y ∧
        holds (withMarker model marker trigger) filler y) =
        (fun y => model.role role x y ∧ holds model filler y) :=
      funext fun y => propext (and_congr Iff.rfl (ih avoids y))
    rw [same]
  | max n role filler ih =>
    show ¬count _ (n + 1) ↔ ¬count _ (n + 1)
    have same : (fun y => (withMarker model marker trigger).role role x y ∧
        holds (withMarker model marker trigger) filler y) =
        (fun y => model.role role x y ∧ holds model filler y) :=
      funext fun y => propext (and_congr Iff.rfl (ih avoids y))
    rw [same]

theorem marker_extension_implies {Class Role Object : Type} [DecidableEq Class]
    (model : Model Class Role Object) (marker : Class) (trigger : Concept Class Role)
    (avoids : Avoids marker trigger) (x : Object)
    (h : holds (withMarker model marker trigger) trigger x) :
    (withMarker model marker trigger).concept marker x := by
  show (if marker = marker then holds model trigger x else model.concept marker x)
  rw [if_pos rfl]
  exact (marker_extension_conservative model marker trigger trigger avoids x).mp h

end ContextCalculus.CandidateModelRefutation
