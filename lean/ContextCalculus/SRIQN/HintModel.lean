import ContextCalculus.SRIQN.HintFast

/-!
# The model of an accepted hint, with its core elements (stage H2, item 5)

`checkRealisationN_sound` and `hintPartsN_sound` give consistency only.
The witness row of stage H2 reads non-entailments off the types of the
core elements, so it needs the model itself: the forest of the
realisation (`forestN`), in which a core element is in a name exactly when
the name is in its type, carried down through the data reduction and the
transitivity encoding with the concept names unchanged.

* `forest_of_check`: an accepted hint gives a model of the reduced
  ontology and an injective map `f` of the core into its domain with
  `F.c a (f b) ↔ a ∈ ty b` and `F.rt R (f b) (f c) ↔ R ∈ lab b c`;
* `hintDNS_model`, `hintPartsN_model`, `hintPartsS_model`: the same for
  the data routes, at the names of the ontology before the transitivity
  encoding (`J.c a (f b) ↔ castAdd a ∈ ty b`).
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd)

variable {n m p q : Nat}

/-- **The forest of an accepted hint, with its core.** -/
theorem forest_of_check {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : Proc.HintN n m)
    (hc : Proc.checkRealisationN (basePart O) (noms O) h = true) :
    ∃ (D : Type) (_ : Nonempty D) (F : Interp D (Fin n) (Fin m)) (f : Fin h.k → D), models F O ∧
      Function.Injective f ∧ (∀ a b, F.c a (f b) ↔ a ∈ h.ty b) ∧
      ∀ R b c, F.rt R (f b) (f c) ↔ R ∈ h.lab b c := by
  simp only [Proc.checkRealisationN, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, true_implies, List.isEmpty_iff] at hc
  obtain ⟨⟨hpos, hcore, hstar⟩, hkids⟩ := hc
  let r := Proc.realOfCoreN hcore fun b => ⟨h.kids b, hstar b, fun e he => by
    rcases hkids with (hk | hk) | hk
    · rw [hk b] at he
      simp at he
    · exact Proc.cert_good hk b e he
    · exact (Proc.good_iff_mem_aliveN _).2 (hk b e he)⟩
  refine ⟨_, ⟨⟨.inl ⟨0, hpos⟩, trivial⟩⟩, forestN r, fun b => ⟨.inl b, trivial⟩,
    models_iff.2 ⟨forestN_models_base r hA, fun a ha => forestN_nom r ha⟩, ?_, fun a b => Iff.rfl,
    fun R b c => ?_⟩
  · intro b c hbc
    have := congrArg Subtype.val hbc
    simpa using this
  · rw [forestN_rt]
    rfl

namespace Proc

/-- **The model of an accepted data hint**, at the names before the
transitivity encoding. -/
theorem hintDNS_model {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hS : SRIQD.Proc.IsSHIQD (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HintN (n + encKD O) m} (hc : hintDNS O card h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), Θ V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.ty b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.lab b c) := by
  obtain ⟨D, hD, F, f, hF, hinj, hty, hlab⟩ := forest_of_check (isALCHOIQ_reduceS O card) h
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
    fun a b => hty _ b, fun hAs R b c => (downI_rt_of_alchi hAs F R (f b) (f c)).trans (hlab R b c)⟩
  exact hnF (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)

end Proc

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part validPart_of_mem small_size)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- **The model of a hint accepted by some part.** -/
theorem hintPartsN_model (hc : CellSpec key cells size) {B L : Nat}
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
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.lab b c) := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  obtain ⟨xa, hxa, hx⟩ := List.any_eq_true.1 hh
  obtain ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab⟩ := Proc.hintDNS_model
    (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hx
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, J, f, hJ, hn, hinj, hty, hlab⟩

/-- **The model of an accepted sparse hint.** -/
theorem hintPartsS_model (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hS : SRIQD.Proc.IsSHIQD (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : HF.HintS (n + Proc.encKD O) m}
    (hh : HF.hintPartsS O cells size sp E h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.tyF b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.toN.lab b c) := by
  rw [HF.hintPartsS_eq] at hh
  exact hintPartsN_model hc hL hsp hcov hS hB hh

/-- **The model of a sparse hint accepted on its named part** (or on some
part when it names none). -/
theorem hintPartsP_model (hc : CellSpec key cells size) {B L : Nat}
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
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.toN.lab b c) :=
  hintPartsN_model hc hL hsp hcov hS hB (HF.hintPartsP_imp _ _ _ _ _ h hh)

end Parts

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.forest_of_check
#print axioms ContextCalculus.SRIQN.Proc.hintDNS_model
#print axioms ContextCalculus.SRIQN.hintPartsS_model
#print axioms ContextCalculus.SRIQN.hintPartsP_model
