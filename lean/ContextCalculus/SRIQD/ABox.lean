import ContextCalculus.SRIQD.Stars
import ContextCalculus.SRIQ.ABox

/-!
# Knowledge bases with data assertions (stage C4, step 4)

`docs/V1.7.0-C4-DATATYPES-DESIGN.md`, section 5. Assertions are the
`SRIQ` assertions (`Assertion.obj`) plus

* `dPos a u L`: `DataPropertyAssertion(u a l)`, the literal `l` read as
  the atom `L` (`{l}`): `a` has a `u`-value in `L`;
* `dNeg a u L`: `NegativeDataPropertyAssertion(u a l)`: no `u`-value of
  `a` lies in `L`.

That `L` holds of one value only is the data theory's business (its
oracle gives `1` for the value type of the literal and `0` for the value
types that contain `L` and an atom that excludes the literal). No clause
relates the values of different elements, so the semantics needs no
more.

## Reduction to `SRIQ`

Data stars depend on the centre type only. The types without a data
star are excluded by one gci each (`forbidWith`: `⊓t ⊑ ⊔(univ \ t)`), so
an interpretation models the object part and the forbidding gcis iff it
models the object part and every element type has a data star
(`models_reduceWith_iff`). Under `OracleSpec`, a knowledge base whose
assertions are object assertions is consistent iff the `SRIQ` knowledge
base of the object part with the forbidding gcis is
(`consistentKB_reduceWith`).

## Realisations

A realisation (`DRealisation`) is an `SRIQ` realisation of the reduced
TBox (`reduce`, its children records are then good in the sense of
`DGood`) with a data star for each block that holds the positive data
assertions of its individuals and respects the negative ones.
`consistentKB_iff_realisation`: for an ALCHIQ object part, finitely many
individuals and an oracle, a knowledge base is consistent iff it has a
realisation over a finite nonempty type of blocks.
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Realisation blockSet realOfModel forestI forestI_models
  forestI_satABox blockSet_finite)

/-! ## Assertions -/

/-- An assertion over individuals `Ind`. -/
inductive Assertion (CName Role DProp DAtom Ind : Type) where
  /-- An `SRIQ` assertion. -/
  | obj (as : SRIQ.Assertion CName Role Ind)
  /-- `a` has a `u`-value in `L`. -/
  | dPos (a : Ind) (u : DProp) (L : DAtom)
  /-- `a` has no `u`-value in `L`. -/
  | dNeg (a : Ind) (u : DProp) (L : DAtom)
deriving DecidableEq, Repr

abbrev ABox (CName Role DProp DAtom Ind : Type) := List (Assertion CName Role DProp DAtom Ind)

variable {D V CName Role DProp DAtom Ind : Type}

/-- Satisfaction of an assertion. -/
def satAssert (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp) (ind : Ind → D) :
    Assertion CName Role DProp DAtom Ind → Prop
  | .obj as => SRIQ.satAssert I.toInterp ind as
  | .dPos a u L => ∃ v, I.d u (ind a) v ∧ atom L v
  | .dNeg a u L => ∀ v, I.d u (ind a) v → ¬ atom L v

def satABox (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp) (ind : Ind → D)
    (A : ABox CName Role DProp DAtom Ind) : Prop :=
  ∀ as ∈ A, satAssert atom I ind as

/-- The knowledge base has a model over a nonempty domain and an
admissible pair. -/
def ConsistentKB (Θ : DataTheory DAtom) (O : Ontology CName Role DProp DAtom)
    (A : ABox CName Role DProp DAtom Ind) : Prop :=
  ∃ (D V : Type) (_ : Nonempty D) (atom : DAtom → V → Prop), Θ V atom ∧
    ∃ (I : DInterp D V CName Role DProp) (ind : Ind → D), models atom I O ∧ satABox atom I ind A

/-- The object assertions. -/
def objABox (A : ABox CName Role DProp DAtom Ind) : SRIQ.ABox CName Role Ind :=
  A.filterMap fun
    | .obj a => some a
    | _ => none

theorem mem_objABox {A : ABox CName Role DProp DAtom Ind} {as : SRIQ.Assertion CName Role Ind} :
    as ∈ objABox A ↔ Assertion.obj as ∈ A := by
  simp only [objABox, List.mem_filterMap]
  constructor
  · rintro ⟨as', h, he⟩
    cases as' <;> simp only [Option.some.injEq, reduceCtorEq] at he
    subst he
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem satABox_objABox {atom : DAtom → V → Prop} {I : DInterp D V CName Role DProp}
    {ind : Ind → D} {A : ABox CName Role DProp DAtom Ind} (h : satABox atom I ind A) :
    SRIQ.satABox I.toInterp ind (objABox A) :=
  fun _ has => h _ (mem_objABox.1 has)

theorem satABox_map_obj {atom : DAtom → V → Prop} {I : DInterp D V CName Role DProp}
    {ind : Ind → D} {A : SRIQ.ABox CName Role Ind} :
    satABox atom I ind (A.map (Assertion.obj (DProp := DProp) (DAtom := DAtom))) ↔
      SRIQ.satABox I.toInterp ind A := by
  simp only [satABox, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    satAssert, SRIQ.satABox]

/-! ## Forbidding the types without a data star -/

section Forbid

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName]

/-- One gci per type in `bad`, satisfied exactly by the elements of other
types; `toL` lists the members of a set. -/
def forbidWith (toL : Finset CName → List CName) (bad : List (Finset CName)) :
    SRIQ.Ontology CName Role :=
  bad.map fun t => .gci (toL t) (toL (Finset.univ \ t))

theorem models_append {I : Interp D CName Role} {O1 O2 : SRIQ.Ontology CName Role} :
    SRIQ.models I (O1 ++ O2) ↔ SRIQ.models I O1 ∧ SRIQ.models I O2 := by
  simp only [SRIQ.models, List.mem_append]
  exact ⟨fun h => ⟨fun cl hcl => h cl (Or.inl hcl), fun cl hcl => h cl (Or.inr hcl)⟩,
    fun h cl hcl => hcl.elim (h.1 cl) (h.2 cl)⟩

theorem models_forbidWith_iff [Fintype Role] [DecidableEq Role] {toL : Finset CName → List CName}
    (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t) {bad : List (Finset CName)} {I : Interp D CName Role} :
    SRIQ.models I (forbidWith (Role := Role) toL bad) ↔ ∀ x, SRIQ.typeOf I x ∉ bad := by
  simp only [SRIQ.models, forbidWith, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, SRIQ.satClause]
  constructor
  · intro h x hx
    obtain ⟨b, hb, hbx⟩ := h _ hx x fun a ha => (SRIQ.mem_typeOf I).1 ((htoL _ a).1 ha)
    rw [htoL, Finset.mem_sdiff] at hb
    exact hb.2 ((SRIQ.mem_typeOf I).2 hbx)
  · intro h t ht x hbody
    have hsub : t ⊆ SRIQ.typeOf I x := fun a ha => (SRIQ.mem_typeOf I).2 (hbody a ((htoL t a).2 ha))
    have hne : SRIQ.typeOf I x ≠ t := fun he => h x (he ▸ ht)
    obtain ⟨b, hb, hbt⟩ : ∃ b ∈ SRIQ.typeOf I x, b ∉ t := by
      by_contra hno
      push Not at hno
      exact hne (Finset.Subset.antisymm hno hsub)
    exact ⟨b, (htoL _ b).2 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hbt⟩),
      (SRIQ.mem_typeOf I).1 hb⟩

variable [Fintype Role] [DecidableEq Role] [DecidableEq DProp] [DecidableEq DAtom]

/-- The object part with one forbidding gci per type of `bad`. -/
def reduceWith (O : Ontology CName Role DProp DAtom) (toL : Finset CName → List CName)
    (bad : List (Finset CName)) : SRIQ.Ontology CName Role :=
  objPart O ++ forbidWith toL bad

theorem models_reduceWith_iff {O : Ontology CName Role DProp DAtom}
    {card : Finset DAtom → Option Nat} {toL : Finset CName → List CName}
    (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t) {bad : List (Finset CName)}
    (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat O card t) {I : Interp D CName Role} :
    SRIQ.models I (reduceWith O toL bad) ↔
      SRIQ.models I (objPart O) ∧ ∀ x, DataSat O card (SRIQ.typeOf I x) := by
  rw [reduceWith, models_append, models_forbidWith_iff htoL]
  simp only [hbad, not_not]

theorem isALCHIQ_reduceWith {O : Ontology CName Role DProp DAtom} (hA : IsALCHIQ O)
    (toL : Finset CName → List CName) (bad : List (Finset CName)) :
    SRIQ.IsALCHIQ (reduceWith O toL bad) := by
  intro body S hcl
  rcases List.mem_append.1 hcl with h | h
  · exact hA body S h
  · obtain ⟨t, -, he⟩ := List.mem_map.1 h
    cases he

/-- The reduced TBox of the semantics (any names). -/
noncomputable def reduce (O : Ontology CName Role DProp DAtom) (card : Finset DAtom → Option Nat) :
    SRIQ.Ontology CName Role :=
  haveI := Classical.decPred fun t : Finset CName => ¬ DataSat O card t
  reduceWith O (fun t => t.toList) (Finset.univ.filter fun t => ¬ DataSat O card t).toList

theorem models_reduce_iff {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
    {I : Interp D CName Role} :
    SRIQ.models I (reduce O card) ↔
      SRIQ.models I (objPart O) ∧ ∀ x, DataSat O card (SRIQ.typeOf I x) := by
  unfold reduce
  exact models_reduceWith_iff (fun t a => Finset.mem_toList) fun t => by simp

theorem isALCHIQ_reduce {O : Ontology CName Role DProp DAtom} (hA : IsALCHIQ O)
    (card : Finset DAtom → Option Nat) : SRIQ.IsALCHIQ (reduce O card) := by
  unfold reduce
  exact isALCHIQ_reduceWith hA _ _

variable [Fintype DProp] [Fintype DAtom] {Θ : DataTheory DAtom}

/-- **Reduction.** Under the oracle specification, a knowledge base with
object assertions only is consistent iff the reduced `SRIQ` knowledge
base is. -/
theorem consistentKB_reduceWith (hspec : OracleSpec Θ card) {O : Ontology CName Role DProp DAtom}
    {toL : Finset CName → List CName} (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t)
    {bad : List (Finset CName)} (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat O card t)
    (A : SRIQ.ABox CName Role Ind) :
    SRIQ.ConsistentKB (reduceWith O toL bad) A ↔ ConsistentKB Θ O (A.map Assertion.obj) := by
  constructor
  · rintro ⟨D, hD, I, ind, hI, hA⟩
    obtain ⟨hIo, hds⟩ := (models_reduceWith_iff htoL hbad).1 hI
    obtain ⟨V, atom, hΘ, d, hm⟩ := exists_dmodel_types hspec.lower I hIo (SRIQ.typeOf I)
      (fun a x => (SRIQ.mem_typeOf I).symm) hds
    exact ⟨D, V, hD, atom, hΘ, _, ind, hm, satABox_map_obj.2 hA⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, ind, hI, hA⟩
    refine ⟨D, hD, I.toInterp, ind, (models_reduceWith_iff htoL hbad).2
      ⟨(models_iff.1 hI).1, dataSat_of_model hspec.upper hΘ hI⟩, satABox_map_obj.1 hA⟩

end Forbid

/-! ## Realisations -/

section Real

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]

/-- A realisation of `(O, A)` over the blocks `B`: an `SRIQ` realisation of
the reduced TBox and the object assertions, and a data star for each
block that carries the data assertions. -/
structure DRealisation (O : Ontology CName Role DProp DAtom) (card : Finset DAtom → Option Nat)
    (A : ABox CName Role DProp DAtom Ind) (B : Type) [Fintype B] where
  base : Realisation (reduce O card) (objABox A) B
  dn : B → List (DNbr DProp DAtom)
  dok : ∀ b, DOK O card (base.ty b) (dn b)
  dpos : ∀ a u L, Assertion.dPos a u L ∈ A → ∃ e ∈ dn (base.blk a), u ∈ e.1 ∧ L ∈ e.2
  dneg : ∀ a u L, Assertion.dNeg a u L ∈ A → ∀ e ∈ dn (base.blk a), u ∈ e.1 → L ∉ e.2

variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom}

/-- The witnesses of the positive data assertions at `x`. -/
noncomputable def assertWit (atom : DAtom → V → Prop) (I : DInterp D V CName Role DProp)
    (ind : Ind → D) (A : ABox CName Role DProp DAtom Ind) (x : D) : List V := by
  classical
  exact A.flatMap fun
    | .dPos a u L => if h : ind a = x ∧ ∃ v, I.d u x v ∧ atom L v then [h.2.choose] else []
    | _ => []

theorem assertWit_mem {atom : DAtom → V → Prop} {I : DInterp D V CName Role DProp}
    {ind : Ind → D} {A : ABox CName Role DProp DAtom Ind} {a : Ind} {u : DProp} {L : DAtom}
    (has : Assertion.dPos a u L ∈ A) (h : ∃ v, I.d u (ind a) v ∧ atom L v) :
    ∃ v ∈ assertWit atom I ind A (ind a), I.d u (ind a) v ∧ atom L v := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold assertWit
  refine List.mem_flatMap.2 ⟨_, has, ?_⟩
  simp only
  rw [dif_pos ⟨trivial, h⟩]
  exact List.mem_singleton_self _

/-- **Realisations.** For an ALCHIQ object part, finitely many
individuals and an oracle, a knowledge base with data assertions is
consistent iff it has a realisation over a finite nonempty type of
blocks. -/
theorem consistentKB_iff_realisation [Finite Ind] (hspec : OracleSpec Θ card)
    (O : Ontology CName Role DProp DAtom) (hA : IsALCHIQ O) (A : ABox CName Role DProp DAtom Ind) :
    ConsistentKB Θ O A ↔ ∃ (B : Type) (_ : Fintype B) (_ : Nonempty B),
      Nonempty (DRealisation O card A B) := by
  classical
  constructor
  · rintro ⟨D, V, ⟨x0⟩, atom, hΘ, I, ind, hI, hAs⟩
    have hred : SRIQ.models I.toInterp (reduce O card) :=
      models_reduce_iff.2 ⟨(models_iff.1 hI).1, dataSat_of_model hspec.upper hΘ hI⟩
    haveI : Finite (blockSet ind x0) := (blockSet_finite ind x0).to_subtype
    letI : Fintype (blockSet ind x0) := Fintype.ofFinite _
    let base := realOfModel I.toInterp ind x0 hred (satABox_objABox hAs)
    let W : blockSet ind x0 → List V := fun b =>
      (dwit O atom (fun u => I.d u b.1) ++ assertWit atom I ind A b.1).dedup
    refine ⟨blockSet ind x0, inferInstance, ⟨⟨x0, Or.inl rfl⟩⟩, ⟨{
      base := base
      dn := fun b => (W b).map (dentry atom fun u => I.d u b.1)
      dok := fun b => dok_of_local_dwit atom (hspec.upper V atom hΘ)
        (fun cl hcl => (models_iff.1 hI).2 cl hcl b.1) (fun a => SRIQ.mem_typeOf I.toInterp) _
      dpos := ?_
      dneg := ?_ }⟩⟩
    · intro a u L has
      obtain ⟨v, hv, hd, hL⟩ := assertWit_mem has (hAs _ has)
      refine ⟨dentry atom (fun u => I.d u (ind a)) v, List.mem_map_of_mem ?_,
        mem_labD.2 hd, mem_vt.2 hL⟩
      exact List.mem_dedup.2 (List.mem_append_right _ hv)
    · intro a u L has e he hu hL
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
      have h1 := (mem_labD (d := fun u => I.d u (ind a)) (v := v) (u := u)).1 hu
      exact hAs _ has v h1 (mem_vt.1 hL)
  · rintro ⟨B, _, ⟨b0⟩, ⟨ρ⟩⟩
    let F := forestI ρ.base
    have hF : SRIQ.models F (reduce O card) :=
      forestI_models ρ.base (isALCHIQ_reduce hA card)
    obtain ⟨hFo, hds⟩ := models_reduce_iff.1 hF
    let X := B ⊕ {t : Finset CName // DataSat O card t}
    letI : Fintype {t : Finset CName // DataSat O card t} := Fintype.ofFinite _
    let g : {x // SRIQ.validR ρ.base x} → X := fun x => match x with
      | ⟨.inl b, _⟩ => .inl b
      | ⟨.inr r, h⟩ => .inr ⟨SRIQ.typeOf F ⟨.inr r, h⟩, hds _⟩
    let ty : X → Finset CName := fun y => match y with
      | .inl b => ρ.base.ty b
      | .inr t => t.1
    let f : X → List (DNbr DProp DAtom) := fun y => match y with
      | .inl b => ρ.dn b
      | .inr t => t.2.choose
    obtain ⟨V, atom, hΘ, d, hm, hpos, hneg⟩ := exists_dmodel hspec.lower F hFo g ty
      (fun a x => by
        obtain ⟨x | r, hx⟩ := x
        · exact Iff.rfl
        · exact (SRIQ.mem_typeOf F).symm)
      f (fun y => by
        cases y with
        | inl b => exact ρ.dok b
        | inr t => exact t.2.choose_spec)
    refine ⟨_, V, ⟨⟨.inl b0, trivial⟩⟩, atom, hΘ, _, fun a => ⟨.inl (ρ.base.blk a), trivial⟩, hm,
      fun as has => ?_⟩
    cases as with
    | obj as => exact forestI_satABox ρ.base _ (mem_objABox.2 has)
    | dPos a u L =>
      obtain ⟨e, he, hu, hL⟩ := ρ.dpos a u L has
      obtain ⟨v, hv, hd⟩ := hpos ⟨.inl (ρ.base.blk a), trivial⟩ e he
      exact ⟨v, hd u hu, mem_vt.1 (hv ▸ hL)⟩
    | dNeg a u L =>
      intro v hd hL
      obtain ⟨e, he, hu, hv⟩ := hneg _ u v hd
      exact ρ.dneg a u L has e he hu (hv ▸ mem_vt.2 hL)

end Real

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.models_reduceWith_iff
#print axioms ContextCalculus.SRIQD.consistentKB_reduceWith
#print axioms ContextCalculus.SRIQD.consistentKB_iff_realisation
