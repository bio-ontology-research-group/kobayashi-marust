import ContextCalculus.SRIQD.NormalForm
import ContextCalculus.SRIQ.Stars
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.CompleteLattice.Finset

/-!
# Stars with data leaves (stage C4, step 2)

`docs/V1.7.0-C4-DATATYPES-DESIGN.md`, section 4. A data neighbour
(`DNbr`) is a pair `(Lu, τ)`: the data properties from the centre to one
value and the value type of that value. A data star of a centre type `t`
is a list `Dn` of data neighbours with `DOK`:

* every `Lu` is closed under `dSub`;
* for every `τ` with `card τ = some k`, at most `k` entries have value
  type `τ` (entries stand for distinct values);
* `dAll`, `dEx`, `dAtLeast`, `dAtMost` at the centre, read on the entries.

A star (`DStarOK`) is an `SRIQ` star of the object part with a data star.
Records, self-supporting sets and good records are those of `SRIQ` with
a data star at each record (`DSupports`, `DSelfSupp`, `DGood`); data
leaves need no records. Data stars depend on the centre type only, so a
set supports itself iff it supports itself in `SRIQ` and every record
type has a data star (`dselfSupp_iff`).

The two directions:

* from a model: the data neighbours of an element are the values chosen
  as witnesses of its data clauses (`dok_of_local`); (upper) bounds the
  entries of one value type. `dataSat_of_model`, `dgood_of_model`.
* to a model: each element gets distinct values for its entries of one
  value type (`exists_assign`); values are shared freely between
  elements, so one admissible pair with as many values of each value type
  as the largest star needs suffices, which (lower) provides
  (`exists_dmodel`).

`entailsSub_iff_dstar` and `unsat_iff_no_dstar` follow for ALCHIQ object
parts, reusing the unravelling of `SRIQ/Stars.lean`.
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Rec Nbr childRec)

variable {D V CName Role DProp DAtom : Type}

/-- A data neighbour: the data properties to one value and its value type. -/
abbrev DNbr (DProp DAtom : Type) := Finset DProp × Finset DAtom

section Defs

variable [DecidableEq DAtom]

/-- `τ` contains `pos` and avoids `neg`. -/
def rngOK (pos neg : List DAtom) (τ : Finset DAtom) : Prop :=
  (∀ p ∈ pos, p ∈ τ) ∧ ∀ q ∈ neg, q ∉ τ

instance (pos neg : List DAtom) (τ : Finset DAtom) : Decidable (rngOK pos neg τ) := by
  unfold rngOK; infer_instance

/-- The literal holds on `τ`. -/
def litOK (l : DAtom × Bool) (τ : Finset DAtom) : Prop :=
  l.1 ∈ τ ↔ l.2 = true

instance (l : DAtom × Bool) (τ : Finset DAtom) : Decidable (litOK l τ) := by
  unfold litOK; infer_instance

variable [DecidableEq DProp]

/-- The entries with `u` in the label and the range on the value type. -/
def dcnt (Dn : List (DNbr DProp DAtom)) (u : DProp) (pos neg : List DAtom) : Nat :=
  Dn.countP fun e => decide (u ∈ e.1 ∧ rngOK pos neg e.2)

/-- The entries of value type `τ`. -/
def tcnt (Dn : List (DNbr DProp DAtom)) (τ : Finset DAtom) : Nat :=
  Dn.countP fun e => decide (e.2 = τ)

variable (O : Ontology CName Role DProp DAtom) (card : Finset DAtom → Option Nat)

/-- The label is closed under `dSub`. -/
def DUpClosed (L : Finset DProp) : Prop :=
  ∀ u w, Clause.dSub u w ∈ O → u ∈ L → w ∈ L

/-- A data star of the centre type `t`. -/
structure DOK (t : Finset CName) (Dn : List (DNbr DProp DAtom)) : Prop where
  up : ∀ e ∈ Dn, DUpClosed O e.1
  card : ∀ τ k, card τ = some k → tcnt Dn τ ≤ k
  all : ∀ a u head, Clause.dAll a u head ∈ O → a ∈ t → ∀ e ∈ Dn, u ∈ e.1 →
    ∃ l ∈ head, litOK l e.2
  ex : ∀ a u pos neg, Clause.dEx a u pos neg ∈ O → a ∈ t → 1 ≤ dcnt Dn u pos neg
  atLeast : ∀ a n u pos neg, Clause.dAtLeast a n u pos neg ∈ O → a ∈ t →
    n ≤ dcnt Dn u pos neg
  atMost : ∀ a n u pos neg, Clause.dAtMost a n u pos neg ∈ O → a ∈ t →
    dcnt Dn u pos neg ≤ n

/-- The type `t` has a data star. -/
def DataSat (t : Finset CName) : Prop :=
  ∃ Dn, DOK O card t Dn

variable [DecidableEq CName] [DecidableEq Role]

/-- A star with data leaves: an `SRIQ` star of the object part and a data
star. -/
def DStarOK (t : Finset CName) (N : List (Nbr CName Role)) (Dn : List (DNbr DProp DAtom)) :
    Prop :=
  SRIQ.StarOK (objPart O) t N ∧ DOK O card t Dn

/-- `C` and `Dn` are children and data leaves for `ρ` inside `G`. -/
def DSupports (G : Set (Rec CName Role)) (ρ : Rec CName Role) (C : List (Nbr CName Role))
    (Dn : List (DNbr DProp DAtom)) : Prop :=
  DStarOK O card ρ.1 (ρ.2.toList ++ C) Dn ∧ ∀ e ∈ C, childRec ρ.1 e ∈ G

/-- Every record of `G` has children inside `G` and data leaves. -/
def DSelfSupp (G : Set (Rec CName Role)) : Prop :=
  ∀ ρ ∈ G, ∃ C Dn, DSupports O card G ρ C Dn

/-- A record is good if it lies in a self-supporting set. -/
def DGood (ρ : Rec CName Role) : Prop :=
  ∃ G : Set (Rec CName Role), ρ ∈ G ∧ DSelfSupp O card G

variable {O card}

theorem dselfSupp_iff {G : Set (Rec CName Role)} :
    DSelfSupp O card G ↔ SRIQ.SelfSupp (objPart O) G ∧ ∀ ρ ∈ G, DataSat O card ρ.1 := by
  constructor
  · intro h
    refine ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
    · obtain ⟨C, Dn, hok, hC⟩ := h ρ hρ
      exact ⟨C, hok.1, hC⟩
    · obtain ⟨C, Dn, hok, -⟩ := h ρ hρ
      exact ⟨Dn, hok.2⟩
  · rintro ⟨h1, h2⟩ ρ hρ
    obtain ⟨C, hok, hC⟩ := h1 ρ hρ
    obtain ⟨Dn, hDn⟩ := h2 ρ hρ
    exact ⟨C, Dn, ⟨hok, hDn⟩, hC⟩

end Defs

/-! ## Reading value types -/

section Read

set_option linter.unusedSectionVars false

variable [Fintype DAtom] [DecidableEq DAtom] {atom : DAtom → V → Prop}

theorem rngOK_vt {pos neg : List DAtom} {v : V} :
    rngOK pos neg (vt atom v) ↔ rngSem atom pos neg v := by
  simp only [rngOK, rngSem, mem_vt]

theorem litOK_vt {l : DAtom × Bool} {v : V} : litOK l (vt atom v) ↔ litSem atom l v := by
  simp only [litOK, litSem, mem_vt]

end Read

/-! ## From local satisfaction to a data star -/

section FromModel

set_option linter.unusedSectionVars false

variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
variable (atom : DAtom → V → Prop)

/-- The data properties from an element to `v`. -/
noncomputable def labD (d : DProp → V → Prop) (v : V) : Finset DProp :=
  by classical exact Finset.univ.filter fun u => d u v

theorem mem_labD {d : DProp → V → Prop} {v : V} {u : DProp} : u ∈ labD d v ↔ d u v := by
  classical
  simp [labD]

/-- The data neighbour of a value. -/
noncomputable def dentry (d : DProp → V → Prop) (v : V) : DNbr DProp DAtom :=
  (labD d v, vt atom v)

variable (O) in
/-- Witnesses of the data existential and at-least clauses, chosen once. -/
noncomputable def dwit (d : DProp → V → Prop) : List V := by
  classical
  exact O.flatMap fun cl => match cl with
    | .dEx _ u pos neg => if h : ∃ v, d u v ∧ rngSem atom pos neg v then [h.choose] else []
    | .dAtLeast _ n u pos neg =>
        if h : ∃ l : List V, l.Nodup ∧ l.length = n ∧ ∀ v ∈ l, d u v ∧ rngSem atom pos neg v
        then h.choose else []
    | _ => []

theorem dwit_ex {d : DProp → V → Prop} {a : CName} {u : DProp} {pos neg : List DAtom}
    (hcl : Clause.dEx a u pos neg ∈ O) (h : ∃ v, d u v ∧ rngSem atom pos neg v) :
    ∃ v ∈ dwit O atom d, d u v ∧ rngSem atom pos neg v := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold dwit
  refine List.mem_flatMap.2 ⟨_, hcl, ?_⟩
  simp only
  convert List.mem_singleton_self _
  rw [dif_pos h]

theorem dwit_atLeast {d : DProp → V → Prop} {a : CName} {n : Nat} {u : DProp}
    {pos neg : List DAtom} (hcl : Clause.dAtLeast a n u pos neg ∈ O)
    (h : ∃ l : List V, l.Nodup ∧ l.length = n ∧ ∀ v ∈ l, d u v ∧ rngSem atom pos neg v) :
    ∃ l : List V, l.Nodup ∧ l.length = n ∧ l ⊆ dwit O atom d ∧
      ∀ v ∈ l, d u v ∧ rngSem atom pos neg v := by
  classical
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, fun y hy => ?_, h.choose_spec.2.2⟩
  unfold dwit
  refine List.mem_flatMap.2 ⟨_, hcl, ?_⟩
  simp only
  convert hy
  rw [dif_pos h]

theorem dcnt_map_dentry (d : DProp → V → Prop) (W : List V) (u : DProp) (pos neg : List DAtom) :
    dcnt (W.map (dentry atom d)) u pos neg =
      W.countP fun v => decide (u ∈ labD d v ∧ rngOK pos neg (vt atom v)) := by
  unfold dcnt
  rw [List.countP_map]
  rfl

/-- **Model to data star.** At an element whose data clauses hold, the
entries of a duplicate-free list of values that holds the witnesses form
a data star, given (upper). -/
theorem dok_of_local
    (hup : ∀ τ k, card τ = some k → ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) →
      l.length ≤ k)
    {c : CName → Prop} {d : DProp → V → Prop} (hloc : ∀ cl ∈ O, dLocal atom c d cl)
    {t : Finset CName} (ht : ∀ a, a ∈ t ↔ c a) (W : List V) (hW : W.Nodup)
    (hex : ∀ a u pos neg, Clause.dEx a u pos neg ∈ O → c a →
      ∃ v ∈ W, d u v ∧ rngSem atom pos neg v)
    (hal : ∀ a n u pos neg, Clause.dAtLeast a n u pos neg ∈ O → c a →
      ∃ l : List V, l.Nodup ∧ l.length = n ∧ l ⊆ W ∧ ∀ v ∈ l, d u v ∧ rngSem atom pos neg v) :
    DOK O card t (W.map (dentry atom d)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he u w hcl hu
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
    exact mem_labD.2 (hloc _ hcl v (mem_labD.1 hu))
  · intro τ k hk
    unfold tcnt
    rw [List.countP_map, List.countP_eq_length_filter]
    refine hup τ k hk _ (hW.filter _) fun v hv => ?_
    simpa [dentry] using (List.mem_filter.1 hv).2
  · intro a u head hcl ha e he hu
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
    obtain ⟨l, hl, hlv⟩ := hloc _ hcl ((ht a).1 ha) v (mem_labD.1 hu)
    exact ⟨l, hl, litOK_vt.2 hlv⟩
  · intro a u pos neg hcl ha
    rw [dcnt_map_dentry]
    obtain ⟨v, hv, hd, hr⟩ := hex a u pos neg hcl ((ht a).1 ha)
    exact List.countP_pos_iff.2 ⟨v, hv, decide_eq_true ⟨mem_labD.2 hd, rngOK_vt.2 hr⟩⟩
  · intro a n u pos neg hcl ha
    rw [dcnt_map_dentry]
    obtain ⟨l, hl, hlen, hsub, hP⟩ := hal a n u pos neg hcl ((ht a).1 ha)
    rw [← hlen]
    exact SRIQ.length_le_countP hl
      (fun v hv => decide_eq_true ⟨mem_labD.2 (hP v hv).1, rngOK_vt.2 (hP v hv).2⟩) hsub
  · intro a n u pos neg hcl ha
    rw [dcnt_map_dentry, List.countP_eq_length_filter]
    refine hloc _ hcl ((ht a).1 ha) _ (hW.filter _) fun v hv => ?_
    have := of_decide_eq_true (List.mem_filter.1 hv).2
    exact ⟨mem_labD.1 this.1, rngOK_vt.1 this.2⟩

/-- The witnesses and any further values give a data star. -/
theorem dok_of_local_dwit [DecidableEq V]
    (hup : ∀ τ k, card τ = some k → ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) →
      l.length ≤ k)
    {c : CName → Prop} {d : DProp → V → Prop} (hloc : ∀ cl ∈ O, dLocal atom c d cl)
    {t : Finset CName} (ht : ∀ a, a ∈ t ↔ c a) (extra : List V) :
    DOK O card t ((dwit O atom d ++ extra).dedup.map (dentry atom d)) := by
  refine dok_of_local atom hup hloc ht _ (List.nodup_dedup _) ?_ ?_
  · intro a u pos neg hcl ha
    obtain ⟨v, hv, hP⟩ := dwit_ex atom hcl (hloc _ hcl ha)
    exact ⟨v, List.mem_dedup.2 (List.mem_append_left _ hv), hP⟩
  · intro a n u pos neg hcl ha
    obtain ⟨l, hl, hlen, hsub, hP⟩ := dwit_atLeast atom hcl (hloc _ hcl ha)
    exact ⟨l, hl, hlen, fun v hv => List.mem_dedup.2 (List.mem_append_left _ (hsub hv)), hP⟩

end FromModel

/-! ## From a data star to local satisfaction -/

section ToModel

set_option linter.unusedSectionVars false

variable [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
variable {atom : DAtom → V → Prop}

/-- The data relation of a list of labelled values. -/
def dOf (P : List (Finset DProp × V)) (u : DProp) (v : V) : Prop :=
  ∃ p ∈ P, u ∈ p.1 ∧ p.2 = v

theorem dcnt_map_P (P : List (Finset DProp × V)) (u : DProp) (pos neg : List DAtom) :
    dcnt (P.map fun p => (p.1, vt atom p.2)) u pos neg =
      (P.filter fun p => decide (u ∈ p.1 ∧ rngOK pos neg (vt atom p.2))).length := by
  unfold dcnt
  rw [List.countP_map, List.countP_eq_length_filter]
  rfl

/-- **Data star to model.** Distinct values for the entries of a data star
satisfy every data clause at the centre. -/
theorem local_of_dok {P : List (Finset DProp × V)} (hP : (P.map Prod.snd).Nodup)
    {t : Finset CName} (h : DOK O card t (P.map fun p => (p.1, vt atom p.2))) :
    ∀ cl ∈ O, dLocal atom (· ∈ t) (dOf P) cl := by
  intro cl hcl
  cases cl with
  | obj _ => trivial
  | dEx a u pos neg =>
    intro ha
    have h1 := h.ex a u pos neg hcl ha
    rw [dcnt_map_P] at h1
    obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos h1
    obtain ⟨hpP, hq⟩ := List.mem_filter.1 hp
    obtain ⟨hu, hr⟩ := of_decide_eq_true hq
    exact ⟨p.2, ⟨p, hpP, hu, rfl⟩, rngOK_vt.1 hr⟩
  | dAll a u head =>
    rintro ha v ⟨p, hp, hu, rfl⟩
    obtain ⟨l, hl, hok⟩ := h.all a u head hcl ha _ (List.mem_map_of_mem hp) hu
    exact ⟨l, hl, litOK_vt.1 hok⟩
  | dAtLeast a n u pos neg =>
    intro ha
    have h1 := h.atLeast a n u pos neg hcl ha
    rw [dcnt_map_P] at h1
    set F := P.filter fun p => decide (u ∈ p.1 ∧ rngOK pos neg (vt atom p.2)) with hF
    have hnd : (F.map Prod.snd).Nodup := hP.sublist ((List.filter_sublist).map _)
    refine ⟨(F.map Prod.snd).take n, hnd.sublist (List.take_sublist _ _), ?_, fun v hv => ?_⟩
    · rw [List.length_take, List.length_map]
      omega
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hv)
      obtain ⟨hpP, hq⟩ := List.mem_filter.1 hp
      obtain ⟨hu, hr⟩ := of_decide_eq_true hq
      exact ⟨⟨p, hpP, hu, rfl⟩, rngOK_vt.1 hr⟩
  | dAtMost a n u pos neg =>
    intro ha l hl hlP
    have h1 := h.atMost a n u pos neg hcl ha
    rw [dcnt_map_P] at h1
    set F := P.filter fun p => decide (u ∈ p.1 ∧ rngOK pos neg (vt atom p.2)) with hF
    have hsub : l ⊆ F.map Prod.snd := by
      intro v hv
      obtain ⟨⟨p, hp, hu, rfl⟩, hr⟩ := hlP v hv
      exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, decide_eq_true ⟨hu, rngOK_vt.2 hr⟩⟩, rfl⟩
    have := (hl.subperm hsub).length_le
    rw [List.length_map] at this
    omega
  | dSub u w =>
    rintro v ⟨p, hp, hu, rfl⟩
    exact ⟨p, hp, h.up _ (List.mem_map_of_mem hp) u w hcl hu, rfl⟩

/-- **Assignment.** From a supply of distinct values of each value type,
long enough for the entries of each type, the entries get distinct
values of their types. -/
theorem exists_assign (S : Finset DAtom → List V) (hS : ∀ τ, (S τ).Nodup)
    (hSt : ∀ τ, ∀ v ∈ S τ, vt atom v = τ) :
    ∀ Dn : List (DNbr DProp DAtom), (∀ τ, tcnt Dn τ ≤ (S τ).length) →
      ∃ P : List (Finset DProp × V), P.map (fun p => (p.1, vt atom p.2)) = Dn ∧
        (P.map Prod.snd).Nodup ∧ ∀ p ∈ P, p.2 ∈ S (vt atom p.2) := by
  intro Dn
  induction Dn generalizing S with
  | nil => exact fun _ => ⟨[], rfl, List.nodup_nil, by simp⟩
  | cons e rest ih =>
    intro hc
    have h1 : 1 ≤ (S e.2).length := by
      have := hc e.2
      simp only [tcnt, List.countP_cons, decide_true, if_true] at this
      omega
    obtain ⟨v, vs, hv⟩ : ∃ v vs, S e.2 = v :: vs := by
      cases h : S e.2 with
      | nil => rw [h] at h1; simp at h1
      | cons v vs => exact ⟨v, vs, rfl⟩
    let S' : Finset DAtom → List V := fun τ => if τ = e.2 then vs else S τ
    have hS'sub : ∀ τ, ∀ w ∈ S' τ, w ∈ S τ := by
      intro τ w hw
      simp only [S'] at hw
      split_ifs at hw with hτ
      · subst hτ; rw [hv]; exact List.mem_cons_of_mem _ hw
      · exact hw
    have hvt : vt atom v = e.2 := hSt e.2 v (by rw [hv]; exact List.mem_cons_self)
    obtain ⟨P', hmap, hnd, hmem⟩ := ih S'
      (fun τ => by
        simp only [S']
        split_ifs with hτ
        · have := hS e.2; rw [hv] at this; exact (List.nodup_cons.1 this).2
        · exact hS τ)
      (fun τ w hw => hSt τ w (hS'sub τ w hw))
      (fun τ => by
        have := hc τ
        simp only [tcnt, List.countP_cons] at this ⊢
        simp only [S']
        split_ifs with hτ
        · subst hτ
          rw [hv] at this
          simp only [decide_true, if_true, List.length_cons] at this
          omega
        · have hne : ¬ (e.2 = τ) := fun h => hτ h.symm
          simp only [hne, decide_false, Bool.false_eq_true, if_false, Nat.add_zero] at this
          exact this)
    refine ⟨(e.1, v) :: P', ?_, ?_, ?_⟩
    · simp only [List.map_cons, hmap, hvt]
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hin => ?_, hnd⟩
      obtain ⟨p, hp, hpv⟩ := List.mem_map.1 hin
      have h2 := hmem p hp
      rw [hpv, hvt] at h2
      simp only [S', if_pos rfl] at h2
      have := hS e.2
      rw [hv] at this
      exact (List.nodup_cons.1 this).1 h2
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · simp only [hvt, hv]
        exact List.mem_cons_self
      · exact hS'sub _ _ (hmem p hp)

end ToModel

/-! ## Adding data to an interpretation -/

section AddData

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom}

/-- **Adding data.** If the elements of an interpretation of the object
part have data stars that factor through a finite type `X`, then (lower)
gives an admissible pair and data properties that make it a model. The
data of each element realise exactly its data star. -/
theorem exists_dmodel
    (hlow : ∀ need : Finset DAtom → Nat, (∀ τ k, card τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ)
    (I : Interp D CName Role) (hI : SRIQ.models I (objPart O)) {X : Type} [Fintype X]
    (g : D → X) (ty : X → Finset CName) (hty : ∀ a x, I.c a x ↔ a ∈ ty (g x))
    (f : X → List (DNbr DProp DAtom)) (hok : ∀ y, DOK O card (ty y) (f y)) :
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧ ∃ d : DProp → D → V → Prop,
      models atom { toInterp := I, d := d } O ∧
      (∀ x, ∀ e ∈ f (g x), ∃ v, vt atom v = e.2 ∧ ∀ u ∈ e.1, d u x v) ∧
      (∀ x u v, d u x v → ∃ e ∈ f (g x), u ∈ e.1 ∧ vt atom v = e.2) := by
  classical
  let need : Finset DAtom → Nat := fun τ => Finset.univ.sup fun y => tcnt (f y) τ
  have hneed : ∀ τ k, card τ = some k → need τ ≤ k := fun τ k hk =>
    Finset.sup_le fun y _ => (hok y).card τ k hk
  obtain ⟨V, atom, hΘ, hS⟩ := hlow need hneed
  choose S hSnd hSlen hSt using hS
  have hP : ∀ y, ∃ P : List (Finset DProp × V), P.map (fun p => (p.1, vt atom p.2)) = f y ∧
      (P.map Prod.snd).Nodup ∧ ∀ p ∈ P, p.2 ∈ S (vt atom p.2) := fun y =>
    exists_assign S hSnd hSt (f y) fun τ => by
      rw [hSlen]
      exact Finset.le_sup (f := fun y => tcnt (f y) τ) (Finset.mem_univ y)
  choose P hPmap hPnd _ using hP
  refine ⟨V, atom, hΘ, fun u x v => dOf (P (g x)) u v, ?_, ?_, ?_⟩
  · refine models_iff.2 ⟨hI, fun cl hcl x => ?_⟩
    have := local_of_dok (hPnd (g x)) ((hPmap (g x)).symm ▸ hok (g x)) cl hcl
    have hc : (fun a => I.c a x) = (· ∈ ty (g x)) := funext fun a => propext (hty a x)
    simp only
    rw [hc]
    exact this
  · intro x e he
    rw [← hPmap (g x)] at he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
    exact ⟨p.2, rfl, fun u hu => ⟨p, hp, hu, rfl⟩⟩
  · rintro x u v ⟨p, hp, hu, rfl⟩
    refine ⟨(p.1, vt atom p.2), ?_, hu, rfl⟩
    rw [← hPmap (g x)]
    exact List.mem_map_of_mem hp

/-- Every element has a data star of its type: then the interpretation
extends to a model. -/
theorem exists_dmodel_types
    (hlow : ∀ need : Finset DAtom → Nat, (∀ τ k, card τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ)
    (I : Interp D CName Role) (hI : SRIQ.models I (objPart O)) (ty : D → Finset CName)
    (hty : ∀ a x, I.c a x ↔ a ∈ ty x) (hds : ∀ x, DataSat O card (ty x)) :
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧ ∃ d : DProp → D → V → Prop,
      models atom { toInterp := I, d := d } O := by
  letI : Fintype {t : Finset CName // DataSat O card t} := Fintype.ofFinite _
  obtain ⟨V, atom, hΘ, d, hm, -⟩ := exists_dmodel hlow I hI
    (fun x => (⟨ty x, hds x⟩ : {t : Finset CName // DataSat O card t})) Subtype.val hty
    (fun y => y.2.choose) (fun y => y.2.choose_spec)
  exact ⟨V, atom, hΘ, d, hm⟩

end AddData

/-! ## The characterisation -/

section Characterisation

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom}

/-- In a model, every element's type has a data star, given (upper). -/
theorem dataSat_of_model
    (hup : ∀ (V : Type) (atom : DAtom → V → Prop), Θ V atom → ∀ τ k, card τ = some k →
      ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k)
    {atom : DAtom → V → Prop} (hΘ : Θ V atom) {I : DInterp D V CName Role DProp}
    (hI : models atom I O) (x : D) : DataSat O card (SRIQ.typeOf I.toInterp x) := by
  classical
  exact ⟨_, dok_of_local_dwit atom (hup V atom hΘ) (fun cl hcl => (models_iff.1 hI).2 cl hcl x)
    (fun a => SRIQ.mem_typeOf I.toInterp) []⟩

/-- **Model to stars.** The root record of an element of a model is good,
given (upper). -/
theorem dgood_of_model
    (hup : ∀ (V : Type) (atom : DAtom → V → Prop), Θ V atom → ∀ τ k, card τ = some k →
      ∀ l : List V, l.Nodup → (∀ v ∈ l, vt atom v = τ) → l.length ≤ k)
    {atom : DAtom → V → Prop} (hΘ : Θ V atom) {I : DInterp D V CName Role DProp}
    (hI : models atom I O) (x : D) : DGood O card (SRIQ.typeOf I.toInterp x, none) := by
  refine ⟨SRIQ.modelRecs I.toInterp, ⟨x, none, rfl⟩, dselfSupp_iff.2
    ⟨SRIQ.modelRecs_selfSupp I.toInterp (models_iff.1 hI).1, ?_⟩⟩
  rintro ρ ⟨y, py, rfl⟩
  exact dataSat_of_model hup hΘ hI y

/-- **Stars to model.** A good root record is the type of an element of
a model, given (lower) and an ALCHIQ object part. -/
theorem model_of_dgood
    (hlow : ∀ need : Finset DAtom → Nat, (∀ τ k, card τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ)
    (hA : IsALCHIQ O) {t : Finset CName} (hg : DGood O card (t, none)) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : DAtom → V → Prop), Θ V atom ∧
      ∃ (I : DInterp D V CName Role DProp) (x : D), models atom I O ∧ ∀ a, I.c a x ↔ a ∈ t := by
  obtain ⟨G, hmem, hG⟩ := hg
  obtain ⟨hS, hds⟩ := dselfSupp_iff.1 hG
  let ty : SRIQ.Node hS (t, none) → Finset CName := fun p =>
    ((SRIQ.recOf hS (t, none) p.1).map Prod.fst).getD ∅
  have hty : ∀ p : SRIQ.Node hS (t, none), ∃ ρ, SRIQ.recOf hS (t, none) p.1 = some ρ ∧
      ty p = ρ.1 := by
    rintro ⟨p, ρ, hp⟩
    exact ⟨ρ, hp, by simp [ty, hp]⟩
  obtain ⟨V, atom, hΘ, d, hm⟩ := exists_dmodel_types hlow (SRIQ.unravel hS (t, none))
    (SRIQ.unravel_models hS _ hmem rfl hA) ty
    (fun a p => by
      obtain ⟨ρ, hp, he⟩ := hty p
      rw [he]
      exact SRIQ.unravel_c hp)
    (fun p => by
      obtain ⟨ρ, hp, he⟩ := hty p
      rw [he]
      exact hds ρ (SRIQ.recOf_mem hS _ hmem p.1 ρ hp))
  refine ⟨_, V, ⟨⟨[], _, rfl⟩⟩, atom, hΘ, _, ⟨[], _, rfl⟩, hm, fun a => ?_⟩
  exact SRIQ.unravel_c (p := ⟨[], _, rfl⟩) rfl

/-- **Characterisation.** Under the oracle specification and for an
ALCHIQ object part, `a ⊑ b` holds iff every good root record that
contains `a` contains `b`. -/
theorem entailsSub_iff_dstar (hspec : OracleSpec Θ card) (O : Ontology CName Role DProp DAtom)
    (hA : IsALCHIQ O) (a b : CName) :
    EntailsSub Θ O a b ↔ ∀ t, DGood O card (t, none) → a ∈ t → b ∈ t := by
  constructor
  · intro hent t hg hat
    obtain ⟨D, V, hD, atom, hΘ, I, x, hm, hx⟩ := model_of_dgood hspec.lower hA hg
    exact (hx b).1 (hent D V atom hΘ I hm x ((hx a).2 hat))
  · intro hgood D V _ atom hΘ I hI x hax
    exact (SRIQ.mem_typeOf I.toInterp).1 (hgood _ (dgood_of_model hspec.upper hΘ hI x)
      ((SRIQ.mem_typeOf I.toInterp).2 hax))

/-- A concept name is unsatisfiable iff no good root record contains it. -/
theorem unsat_iff_no_dstar (hspec : OracleSpec Θ card) (O : Ontology CName Role DProp DAtom)
    (hA : IsALCHIQ O) (a : CName) :
    Unsat Θ O a ↔ ∀ t, DGood O card (t, none) → a ∉ t := by
  constructor
  · intro hun t hg hat
    obtain ⟨D, V, hD, atom, hΘ, I, x, hm, hx⟩ := model_of_dgood hspec.lower hA hg
    exact hun D V atom hΘ I hm x ((hx a).2 hat)
  · intro hno D V _ atom hΘ I hI x hax
    exact hno _ (dgood_of_model hspec.upper hΘ hI x) ((SRIQ.mem_typeOf I.toInterp).2 hax)

end Characterisation

end ContextCalculus.SRIQD

#print axioms ContextCalculus.SRIQD.dok_of_local
#print axioms ContextCalculus.SRIQD.local_of_dok
#print axioms ContextCalculus.SRIQD.exists_assign
#print axioms ContextCalculus.SRIQD.exists_dmodel
#print axioms ContextCalculus.SRIQD.dgood_of_model
#print axioms ContextCalculus.SRIQD.model_of_dgood
#print axioms ContextCalculus.SRIQD.entailsSub_iff_dstar
#print axioms ContextCalculus.SRIQD.unsat_iff_no_dstar
