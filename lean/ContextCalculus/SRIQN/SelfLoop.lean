import ContextCalculus.SRIQN.DataParts
import ContextCalculus.SRIQD.CellPartsProc

/-!
# Loops of C2a models (stage C3c, Self and irreflexive roles)

`docs/V1.7.0-C3-ROLES-DESIGN.md`, section 5 (deviation D12). The forest of
a realisation has loops only at core elements (`forestN_loop`): a tree node
is never its own neighbour. The realisation that C2a completeness builds
from a model has a nominal name in each core type when there is a nominal
name. Together: a consistent C2a ontology with a nominal name has a model
in which every loop sits at an element of a nominal name
(`loopNom_of_c2a`). The same holds with data under a bounded oracle
(`loopNom_data`) and in a cell theory (`loopNom_cells`).

The Self encoding (`SRIQN/Self.lean`) uses this: a loop at a nominal
element is forbidden by ordinary clauses, so such a model has no loops at
all on the roles it controls.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd)
open ContextCalculus.SRIQ (FR)

variable {CName Role : Type}

/-- Every loop sits at an element of a nominal name. -/
def LoopNom {D : Type} (I : Interp D CName Role) (N : List CName) : Prop :=
  ∀ R x, I.rt R x x → ∃ a ∈ N, I.c a x

section Forest

variable [DecidableEq CName] [DecidableEq Role] {B : SRIQ.Ontology CName Role} {N : List CName}
  {K : Type} [Fintype K] (r : RealisationN B N K)

theorem tadj_irrefl (c : K) (i : Nat) (R : RoleT Role) (p : List Nat) : ¬ TAdj r c i R p p := by
  rintro (⟨j, -, -, h, -⟩ | ⟨j, -, -, h, -⟩) <;>
    exact absurd (congrArg List.length h) (by simp)

/-- **Loops of the forest** are core loops. -/
theorem forestN_loop {R : RoleT Role} {x : {x : FR K // validN r x}} (h : (forestN r).rt R x x) :
    ∃ c, x.1 = .inl c ∧ R ∈ r.lab c c := by
  rw [forestN_rt] at h
  obtain ⟨x | ⟨b, i, p⟩, hx⟩ := x
  · exact ⟨x, rfl, h⟩
  · exact absurd h.2.2 (tadj_irrefl r b i R p)

end Forest

section C2a

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]

/-- **Loops at nominal elements.** A model of a C2a ontology with a
nominal name, in which the exempt names hold at nominal elements only,
gives a model in which every loop sits at an element of a nominal name. -/
theorem loopNom_of_c2a {O : Ontology CName Role} {S : CName → Prop} (hA : IsALCHOIQ O)
    (hC : IsC2aS O S) (hne : noms O ≠ []) {D : Type} [Nonempty D] (I : Interp D CName Role)
    (hI : models I O) (hS0 : ∀ X, S X → ∀ x, I.c X x → ∃ a ∈ noms O, I.c a x) :
    ∃ (D' : Type) (_ : Nonempty D') (F : Interp D' CName Role), models F O ∧ LoopNom F (noms O) := by
  obtain ⟨k, hk, -, r, hr⟩ := c2a_complete_of hC I hI hS0
  have hr' : ∀ c, ∃ a ∈ noms O, a ∈ r.ty c := hr.resolve_left hne
  refine ⟨_, ⟨⟨.inl ⟨0, hk⟩, trivial⟩⟩, forestN r,
    models_iff.2 ⟨forestN_models_base r hA, fun a ha => forestN_nom r ha⟩, ?_⟩
  intro R x hx
  obtain ⟨c, hc, -⟩ := forestN_loop r hx
  obtain ⟨a, ha, hac⟩ := hr' c
  refine ⟨a, ha, ?_⟩
  show a ∈ typN r x.1
  rw [hc]
  exact hac

end C2a

/-! ## With data -/

section Data

set_option linter.unusedSectionVars false

variable {DProp DAtom : Type}
variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat} {B : Nat}

/-- A data model whose loops sit at elements of nominal names. -/
def ConsistentDL (Θ : DataTheory DAtom) (O : DOntology CName Role DProp DAtom) : Prop :=
  ∃ (D V : Type) (_ : Nonempty D) (atom : DAtom → V → Prop), Θ V atom ∧
    ∃ I : DInterp D V CName Role DProp, SRIQD.models atom I (dbase O) ∧
      (∀ a ∈ dnoms O, NomAt I.toInterp a) ∧ LoopNom I.toInterp (dnoms O)

theorem consistentDN_of_DL {O : DOntology CName Role DProp DAtom} (h : ConsistentDL Θ O) :
    ConsistentDN Θ O := by
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn, -⟩ := h
  exact ⟨D, V, hD, atom, hΘ, I, hI, hn⟩

/-- **Loops at nominal elements, with data**, under a bounded oracle. -/
theorem loopNom_data (hspec : OracleSpecB Θ card B) {O : DOntology CName Role DProp DAtom}
    (hB : dbnd (dbase O) ≤ B) (hA : SRIQD.IsALCHIQ (dbase O)) (hC : IsC2aD O)
    (hne : dnoms O ≠ []) (hc : ConsistentDN Θ O) : ConsistentDL Θ O := by
  classical
  let toL : Finset CName → List CName := fun t => t.toList
  have htoL : ∀ t a, a ∈ toL t ↔ a ∈ t := fun t a => Finset.mem_toList
  let bad : List (Finset CName) :=
    (Finset.univ.filter fun t => ¬ DataSat (dbase O) card t).toList
  have hbad : ∀ t, t ∈ bad ↔ ¬ DataSat (dbase O) card t := fun t => by simp [bad]
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn⟩ := hc
  obtain ⟨hI', hn'⟩ := shrinkD_models hI hn
  have hm : models (shrinkD O I).toInterp (reduceN O toL bad) := by
    refine models_iff.2 ⟨?_, by rw [noms_reduceN]; exact hn'⟩
    rw [basePart_reduceN]
    exact (SRIQD.models_reduceWith_iff htoL hbad).2
      ⟨(SRIQD.models_iff.1 hI').1, SRIQD.dataSat_of_model hspec.upper hΘ hI'⟩
  have hA' : IsALCHOIQ (reduceN O toL bad) := by
    unfold IsALCHOIQ
    rw [basePart_reduceN]
    exact SRIQD.isALCHIQ_reduceWith hA _ _
  obtain ⟨D', hD', F, hF, hL⟩ := loopNom_of_c2a hA' (isC2aS_reduceN hC toL bad)
    (by rw [noms_reduceN]; exact hne) _ hm fun X hX x hx => by
      obtain ⟨a, ha, hax⟩ := shrinkI_nomOnly hX hx
      rw [noms_objN] at ha
      refine ⟨a, by rw [noms_reduceN]; exact ha, ?_⟩
      exact (shrinkI_c_of_not I.toInterp (nom_not_nomOnly (by rw [noms_objN]; exact ha)) x).2 hax
  obtain ⟨hb, hnF⟩ := models_iff.1 hF
  rw [basePart_reduceN] at hb
  rw [noms_reduceN] at hnF hL
  obtain ⟨hFo, hds⟩ := (SRIQD.models_reduceWith_iff htoL hbad).1 hb
  obtain ⟨V', atom', hΘ', d, hmd⟩ := SRIQD.exists_dmodel_types (card := SRIQD.capCard card B)
    hspec.lowCap F hFo (SRIQ.typeOf F) (fun a x => (SRIQ.mem_typeOf F).symm)
    (fun x => (SRIQD.dataSat_cap_iff hB _).2 (hds x))
  exact ⟨D', V', hD', atom', hΘ', { toInterp := F, d := d }, hmd, hnF, hL⟩

end Data

section Cells

set_option linter.unusedSectionVars false

open ContextCalculus.SRIQD (CellSpec cellTheory part_of_cellTheory cellTheory_of_part oracleSpecB_part
  small small_size allG splitCell splitCell_ok vtc)

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}
variable {n m p : Nat}

/-- **Loops at nominal elements in a cell theory.** -/
theorem loopNom_cells (hc : CellSpec key cells size) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hA : SRIQD.IsALCHIQ (dbase O)) (hC : IsC2aD O) (hne : dnoms O ≠ [])
    (h : ConsistentDN (cellTheory key E) O) : ConsistentDL (cellTheory key E) O := by
  classical
  let L := dbnd (dbase O) * (allG s).length
  let sp := splitCell cells size L E
  have hsp : ∀ c ∈ cells, sp c = true → small size L c = true := splitCell_ok.1
  have hcov := (splitCell_ok (cells := cells) (size := size) (L := L) (E := E)).2
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc' hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc' hs); exact ⟨k, hk⟩
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn⟩ := h
  obtain ⟨fr, hval, hpart⟩ := part_of_cellTheory hc hfin hΘ
  have hspec := oracleSpecB_part (key := key) (E := E) hc (B := dbnd (dbase O)) (le_refl L) hsp hcov hval
  obtain ⟨D', V', hD', atom', hΘ', I', hI', hn', hL⟩ :=
    loopNom_data hspec (le_refl _) hA hC hne ⟨D, V, hD, atom, hpart, I, hI, hn⟩
  exact ⟨D', V', hD', atom', cellTheory_of_part hΘ', I', hI', hn', hL⟩

end Cells

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.forestN_loop
#print axioms ContextCalculus.SRIQN.loopNom_of_c2a
#print axioms ContextCalculus.SRIQN.loopNom_data
#print axioms ContextCalculus.SRIQN.loopNom_cells
