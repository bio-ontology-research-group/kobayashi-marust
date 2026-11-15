import ContextCalculus.SRIQN.HintModel

/-!
# The model of a flat hint (stage H4, item 1)

A hint without `kid` lines (a *flat* hint) has every element of its model
in the core: `coreI` is the interpretation over the core elements, a name
holds at `b` when it is in `ty b`, and a role term from `b` to `c` when it
is in `lab b c`. When the hint checks, `coreI` models the ontology
(`models_of_starLists'` with the core neighbours as the stars).

The primed forms of `forest_of_check`, `hintDNS_model`, `hintPartsN_model`
and `hintPartsP_model` add one conjunct to each: for a flat hint, every
element of the model is the image of a core element. They take the core
model when the hint is flat and the forest otherwise, so the earlier
statements are unchanged and every earlier conjunct holds as before.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd)
open ContextCalculus.SRIQ (flipL mem_flipL)

variable {n m p q : Nat}

/-- The interpretation over the core of a hint. -/
def coreI (h : Proc.HintN n m) : Interp (Fin h.k) (Fin n) (Fin m) where
  c a b := a ∈ h.ty b
  r s b c := RoleT.pos s ∈ h.lab b c

theorem coreI_rt (h : Proc.HintN n m) (hs : ∀ b c, h.lab c b = flipL (h.lab b c))
    (R : RoleT (Fin m)) (b c : Fin h.k) : (coreI h).rt R b c ↔ R ∈ h.lab b c := by
  cases R with
  | pos s => exact Iff.rfl
  | inv s =>
    show RoleT.pos s ∈ h.lab c b ↔ _
    rw [hs b c, mem_flipL]
    rfl

/-- **The core model of a flat hint.** -/
theorem core_of_check {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : Proc.HintN n m)
    (hc : Proc.checkRealisationN (basePart O) (noms O) h = true) (hk : ∀ b, h.kids b = []) :
    0 < h.k ∧ models (coreI h) O ∧ ∀ R b c, (coreI h).rt R b c ↔ R ∈ h.lab b c := by
  simp only [Proc.checkRealisationN, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, true_implies, List.isEmpty_iff] at hc
  obtain ⟨⟨hpos, hcore, hstar⟩, -⟩ := hc
  have hrt := coreI_rt h hcore.1
  refine ⟨hpos, models_iff.2 ⟨?_, fun a ha => ?_⟩, hrt⟩
  · refine models_of_starLists' hA (coreI h) h.ty (fun _ _ => Iff.rfl) h.lab
      (fun R x y => (hrt R x y).symm)
      (fun b => (List.finRange h.k).filter fun c => decide (h.lab b c ≠ ∅))
      (fun b => (List.nodup_finRange _).filter _) (fun R x y hr hy => ?_) (fun b => ?_)
    · exfalso
      refine hy (List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true fun he => ?_⟩)
      have := (hrt R x y).1 hr
      rw [he] at this
      simp at this
    · have := hstar b
      rw [hk b, List.append_nil] at this
      exact this
  · obtain ⟨c, hc, huniq⟩ := hcore.2 a ha
    exact ⟨c, fun y => ⟨fun hy => huniq y hy, fun hy => hy ▸ hc⟩⟩

/-- `forest_of_check` with the flat case: every element is a core element. -/
theorem forest_of_check' {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : Proc.HintN n m)
    (hc : Proc.checkRealisationN (basePart O) (noms O) h = true) :
    ∃ (D : Type) (_ : Nonempty D) (F : Interp D (Fin n) (Fin m)) (f : Fin h.k → D), models F O ∧
      Function.Injective f ∧ (∀ a b, F.c a (f b) ↔ a ∈ h.ty b) ∧
      (∀ R b c, F.rt R (f b) (f c) ↔ R ∈ h.lab b c) ∧
      ((∀ b, h.kids b = []) → ∀ y, ∃ b, f b = y) := by
  by_cases hk : ∀ b, h.kids b = []
  · obtain ⟨hpos, hm, hrt⟩ := core_of_check hA h hc hk
    exact ⟨Fin h.k, ⟨⟨0, hpos⟩⟩, coreI h, id, hm, Function.injective_id, fun _ _ => Iff.rfl, hrt,
      fun _ y => ⟨y, rfl⟩⟩
  · obtain ⟨D, hD, F, f, hF, hinj, hty, hlab⟩ := forest_of_check hA h hc
    exact ⟨D, hD, F, f, hF, hinj, hty, hlab, fun h' => absurd h' hk⟩

namespace Proc

/-- `hintDNS_model` with the flat case. -/
theorem hintDNS_model' {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hS : SRIQD.Proc.IsSHIQD (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HintN (n + encKD O) m} (hc : hintDNS O card h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), Θ V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.ty b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.lab b c) ∧
        ((∀ b, h.kids b = []) → ∀ y, ∃ b, f b = y) := by
  obtain ⟨D, hD, F, f, hF, hinj, hty, hlab, hsur⟩ := forest_of_check' (isALCHOIQ_reduceS O card) h
    (checkRealisationN_of_hintDNS hc)
  rw [reduceS, reduceNQ] at hF
  obtain ⟨hb, hnF⟩ := models_iff.1 hF
  rw [basePart_reduceN] at hb
  rw [noms_reduceN] at hnF
  obtain ⟨hFo, hds⟩ := (SRIQD.models_reduceWith_iff SRIQD.Proc.mem_toLFin
    SRIQD.Proc.mem_badQ).1 hb
  obtain ⟨V, atom, hΘ, d, hmd⟩ := SRIQD.exists_dmodel_types (card := SRIQD.capCard card B)
    hspec.lowCap F hFo (SRIQ.typeOf F) (fun a x => (SRIQ.mem_typeOf F).symm)
    (fun x => (SRIQD.dataSat_cap_iff hB _).2 (hds x))
  have hJ' : SRIQD.models atom ({ toInterp := F, d := d } : DInterp D V _ _ _)
      (SRIQD.Proc.encTransQD (dbase O)).2 := by
    rw [← dbase_encTransDN]; exact hmd
  refine ⟨D, V, hD, atom, hΘ, _, f, SRIQD.Proc.models_downD hS hJ', fun a ha => ?_, hinj,
    fun a b => hty _ b, fun hAs R b c => (downI_rt_of_alchi hAs F R (f b) (f c)).trans (hlab R b c),
    hsur⟩
  exact hnF (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)

end Proc

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part validPart_of_mem small_size)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- `hintPartsN_model` with the flat case. -/
theorem hintPartsN_model' (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hS : SRIQD.Proc.IsSHIQD (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : Proc.HintN (n + Proc.encKD O) m}
    (hh : hintPartsN O cells size sp E h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.ty b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.lab b c) ∧
        ((∀ b, h.kids b = []) → ∀ y, ∃ b, f b = y) := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  obtain ⟨xa, hxa, hx⟩ := List.any_eq_true.1 hh
  obtain ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur⟩ := Proc.hintDNS_model'
    (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hx
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur⟩

/-- `hintPartsP_model` with the flat case: a sparse hint without `kid`
lines has every element of its model in the core. -/
theorem hintPartsP_model' (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hS : SRIQD.Proc.IsSHIQD (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : HF.HintS (n + Proc.encKD O) m}
    (hh : HF.hintPartsP O cells size sp E h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.tyF b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.toN.lab b c) ∧
        (h.kids = [] → ∀ y, ∃ b, f b = y) := by
  obtain ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur⟩ :=
    hintPartsN_model' hc hL hsp hcov hS hB (HF.hintPartsP_imp _ _ _ _ _ h hh)
  refine ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, fun hk => hsur fun b => ?_⟩
  simp [HF.HintS.toN, hk]

end Parts

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.core_of_check
#print axioms ContextCalculus.SRIQN.forest_of_check'
#print axioms ContextCalculus.SRIQN.Proc.hintDNS_model'
#print axioms ContextCalculus.SRIQN.hintPartsP_model'
