import ContextCalculus.DataValueProjection

/-!
# Omission of data assertions with one value per bounded slot (`docs/DATATYPES.md`)

`DataAbox::positive_assertions_redundant` (`engine/src/frontend/data_abox.rs`)
drops the positive data assertions of a group `G` of data properties without
any replacement. Since 2026-10-31 it accepts a `≤ 1`-bounded property only
when the whole ABox asserts at most one literal for it ("Forced nominal
routes: the omission certificate and the bridge pigeonhole").

This file proves the omission exact as the zero-digit instance of the
object-level projection (`DataValueProjection`): when every slot indexes at
most one identity key, the projection needs no index position, so it adds no
digit class and no clash axiom, and its only additions are the domain
assertions; when those are already in the ontology, the projected ontology is
the source without the assertions of `G`.

* `omission_sound`: every model of `O` is a model of the omitted ontology.
* `omission_complete`: every model of the omitted ontology yields, by the
  edge surgery of `projection_complete`, a model of `O` with the same objects,
  classes, object properties, individuals and non-`G` data properties.

The correspondence between the Rust condition (one asserted lexical literal
per bounded property, every range decided, every domain told, no data
constructor on the group) and `projGate` with one key per slot is not proved
here, as for the projection gate itself.
-/

set_option linter.unusedSectionVars false

namespace ContextCalculus.DataAboxOmission
open ContextCalculus.TwoSortedDL ContextCalculus.DataValueProjection

variable {Cls OR DR Ind DN K : Type}
variable [DecidableEq Cls] [DecidableEq OR] [DecidableEq DR] [DecidableEq Ind] [DecidableEq DN]
variable {Obj Dat : Type}

/-- The source without the assertions of `G`. -/
def withoutG (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN)) : List (Axiom Cls OR DR Ind DN) :=
  O.filter fun ax => !isGAssertion inG ax

/-- A source interpretation read over `Cls ⊕ Digit`: no element is in a digit class. -/
def lift (J : Interp Cls OR DR Ind DN Obj Dat) :
    Interp (Cls ⊕ Digit Cls OR DR Ind DN) OR DR Ind DN Obj Dat :=
  { J with cls := fun | .inl c => J.cls c | .inr _ => fun _ => False }

theorem comap_lift (J : Interp Cls OR DR Ind DN Obj Dat) :
    (lift J).comapCls (Sum.inl : Cls → Cls ⊕ Digit Cls OR DR Ind DN) = J := rfl

/-- With at most one relevant key per slot, zero positions separate the keys
(there is nothing to separate). -/
theorem one_key_separates (idx : Slot Cls OR DR Ind DN → K → Nat)
    (relevant : Slot Cls OR DR Ind DN → K → Prop)
    (hone : ∀ s k l, relevant s k → relevant s l → k = l) :
    IndexSeparates idx (fun _ => 0) relevant := by
  intro s k l hk hl hne
  exact absurd (hone s k l hk hl) hne

/-- **Omission, `O ⇒ withoutG O`.** -/
theorem omission_sound (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN))
    (I : Interp Cls OR DR Ind DN Obj Dat) (hI : Models I O) : Models I (withoutG inG O) := by
  intro ax hax
  exact hI ax (List.mem_filter.1 hax).1

/-- **Omission, `withoutG O ⇒ O`.** Under the projection gate, with one identity
key per slot and every domain assertion of an asserted subject already in the
omitted ontology, every model of the omitted ontology gives a model of `O`
that agrees with it on everything but the `G` edges. -/
theorem omission_complete (inG : DR → Bool) (O : List (Axiom Cls OR DR Ind DN))
    (sup : DR → List DR) (memb : DN → DN → Option Bool) (key : DN → Option K)
    (lit : DN → Dat)
    (hg : projGate inG O sup memb key = true)
    (hone : ∀ s k l, Relevant inG O sup memb key s k → Relevant inG O sup memb key s l → k = l)
    (hdom : ∀ u a v q D ax, (u, a, v) ∈ gAssertions inG O → q ∈ sup u → ax ∈ O →
      isDomain ax = some (q, D) → Axiom.cassert D a ∈ withoutG inG O)
    (J : Interp Cls OR DR Ind DN Obj Dat)
    (hvals : ValuesSingleton J.dcon lit (fun v => ∃ u a, (u, a, v) ∈ gAssertions inG O))
    (hmemb : MembSound J.dcon lit memb) (hkey : KeySound lit key)
    (hJ : Models J (withoutG inG O)) :
    Models (surgery inG O sup lit (lift J)) O ∧
    (surgery inG O sup lit (lift J)).cls = J.cls ∧
    (surgery inG O sup lit (lift J)).orole = J.orole ∧
    (surgery inG O sup lit (lift J)).ind = J.ind ∧
    (∀ r, inG r = false → (surgery inG O sup lit (lift J)).drole r = J.drole r) := by
  let idx : Slot Cls OR DR Ind DN → K → Nat := fun _ _ => 0
  have hsep := one_key_separates idx (Relevant inG O sup memb key) hone
  have hProj : ∀ ax, Proj inG O sup memb key idx (fun _ => 0) ax → sat (lift J) ax := by
    intro ax hax
    cases hax with
    | kept ax0 hmem hng =>
      refine (sat_mapCls Sum.inl (lift J) ax0).2 ?_
      rw [comap_lift]
      exact hJ ax0 (List.mem_filter.2 ⟨hmem, by simp [hng]⟩)
    | domain u a v q D ax0 hm hq hmem hd =>
      exact (sat_mapCls Sum.inl (lift J) (Axiom.cassert D a)).2
        (by rw [comap_lift]; exact hJ _ (hdom u a v q D ax0 hm hq hmem hd))
    | digit u a v s k p _ _ _ _ _ hp => exact absurd hp (Nat.not_lt_zero _)
    | clash s p _ hp => exact absurd hp (Nat.not_lt_zero _)
  exact projection_complete (inG := inG) (O := O) (sup := sup) (memb := memb) (key := key)
    (idx := idx) (npos := fun _ => 0) (lit := lit) hg hsep (lift J) hvals hmemb hkey hProj

end ContextCalculus.DataAboxOmission
