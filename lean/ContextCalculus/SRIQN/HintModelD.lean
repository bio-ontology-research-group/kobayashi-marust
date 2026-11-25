import ContextCalculus.SRIQN.HintModelFlat

/-!
# The data values of the model of a hint (stage H5, item 1)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 13. The data reduction
(`SRIQD.exists_dmodel_types`) picks a data star for every element and
drops it. Here the model keeps the stars the hint gives (`dstar` lines):

* `SRIQD.exists_dmodelP`: `exists_dmodel` with the values exposed. Each
  element `x` reads its data from a list `P (g x)` of labelled values whose
  shape is its data star (labels and value types) and whose values are
  pairwise distinct; `d u x v` holds exactly when some listed value is `v`
  with `u` in its label.
* `HF.givenStar h stars b`: the data star the hint gives for the core
  element `b` (`none` when there is none or an entry is out of range).
* `hintPartsP_modelD`: `hintPartsP_model'` with one more conjunct. For a
  core element `b` with a given star `S`, the values of `f b` are a list
  `P` of shape `S` with distinct values, and `J.d u (f b) v` iff `v` is
  the value of an entry of `P` whose label holds `u`. So the
  `u`-values of `f b` are exactly one value per entry of `S` whose label
  holds `u`, of the value type the entry lists, distinct per element.
-/

namespace ContextCalculus.SRIQD

open ContextCalculus.SRI (Interp)

section AddDataP

set_option linter.unusedSectionVars false

variable {D CName Role DProp DAtom : Type}
variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {O : Ontology CName Role DProp DAtom} {card : Finset DAtom → Option Nat}
  {Θ : DataTheory DAtom}

/-- **Adding data, with the values exposed.** -/
theorem exists_dmodelP
    (hlow : ∀ need : Finset DAtom → Nat, (∀ τ k, card τ = some k → need τ ≤ k) →
      ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧
        ∀ τ, ∃ l : List V, l.Nodup ∧ l.length = need τ ∧ ∀ v ∈ l, vt atom v = τ)
    (I : Interp D CName Role) (hI : SRIQ.models I (objPart O)) {X : Type} [Fintype X]
    (g : D → X) (ty : X → Finset CName) (hty : ∀ a x, I.c a x ↔ a ∈ ty (g x))
    (f : X → List (DNbr DProp DAtom)) (hok : ∀ y, DOK O card (ty y) (f y)) :
    ∃ (V : Type) (atom : DAtom → V → Prop), Θ V atom ∧ ∃ P : X → List (Finset DProp × V),
      (∀ y, (P y).map (fun p => (p.1, vt atom p.2)) = f y ∧ ((P y).map Prod.snd).Nodup) ∧
      models atom { toInterp := I, d := fun u x v => dOf (P (g x)) u v } O := by
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
  refine ⟨V, atom, hΘ, P, fun y => ⟨hPmap y, hPnd y⟩, ?_⟩
  refine models_iff.2 ⟨hI, fun cl hcl x => ?_⟩
  have := local_of_dok (hPnd (g x)) ((hPmap (g x)).symm ▸ hok (g x)) cl hcl
  have hc : (fun a => I.c a x) = (· ∈ ty (g x)) := funext fun a => propext (hty a x)
  simp only
  rw [hc]
  exact this

end AddDataP

end ContextCalculus.SRIQD

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd DNbr DOK)

namespace HF

variable {n m p q : Nat}

/-- The data star the hint gives for a core element (`none`: no `dstar`
lines for it, or an entry out of range). -/
def givenStar (h : HintS n m) (stars : Array (Option (List (Option (DNbr (Fin p) (Fin q))))))
    (b : Fin h.k) : Option (List (DNbr (Fin p) (Fin q))) :=
  match (stars[b.val]?).getD none with
  | some l => if l.all Option.isSome then some (l.filterMap id) else none
  | none => none

theorem okOf_given {Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {h : HintS n m} {stars} {b : Fin h.k}
    {S : List (DNbr (Fin p) (Fin q))} (hb : okOf Db card h stars b = true)
    (hg : givenStar h stars b = some S) : starGivenB Db card (h.tyF b) S = true := by
  unfold givenStar at hg
  unfold okOf at hb
  split at hg
  next l hl =>
    rw [hl] at hb
    simp only at hb
    split_ifs at hg with ha
    simp only [Option.some.injEq] at hg
    subst hg
    rw [if_pos ha] at hb
    exact hb
  next => cases hg

theorem dok_dataOnly {Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {t : Finset (Fin n)} {Dn : List (DNbr (Fin p) (Fin q))}
    (h : DOK (dataOnly Db) card t Dn) : DOK Db card t Dn := by
  have hm : ∀ cl, isDataC cl = true → cl ∈ Db → cl ∈ dataOnly Db := fun cl hc hm =>
    List.mem_filter.2 ⟨hm, hc⟩
  exact ⟨fun e he u w hs => h.up e he u w (hm _ rfl hs), h.card,
    fun a u hd hcl => h.all a u hd (hm _ rfl hcl),
    fun a u ps ng hcl => h.ex a u ps ng (hm _ rfl hcl),
    fun a k u ps ng hcl => h.atLeast a k u ps ng (hm _ rfl hcl),
    fun a k u ps ng hcl => h.atMost a k u ps ng (hm _ rfl hcl)⟩

theorem dbnd_dataOnly (Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    dbnd (dataOnly Db) = dbnd Db := by
  have hL : SRIQD.dLowerL (dataOnly Db) = SRIQD.dLowerL Db :=
    filterMap_filter_of _ _ (fun x hx => by cases x <;> simp_all [isDataC]) Db
  unfold dbnd
  rw [hL]

/-- A given star that passes `starGivenB` is a data star under the capped
oracle. -/
theorem dok_of_given {Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {B : Nat} (hB : dbnd Db ≤ B) {t : Finset (Fin n)}
    {S : List (DNbr (Fin p) (Fin q))} (h : starGivenB (dataOnly Db) card t S = true) :
    DOK Db (SRIQD.capCard card B) t S := by
  unfold starGivenB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  rw [dbnd_dataOnly] at h1
  exact SRIQD.dok_cap_of_short (dok_dataOnly h3) (h1.trans hB)

end HF

namespace Proc

/-- The checked data stars give a data model whose given core elements
carry exactly their given stars. -/
theorem hintDNS_modelD {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hS : SRIQD.Proc.IsSHIQD (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HF.HintS (n + encKD O) m} (hc : hintDNS O card h.toN = true)
    (gs : Fin h.k → Option (List (DNbr (Fin p) (Fin q))))
    (hgs : ∀ b S, gs b = some S → DOK (dbase (encTransDN O)) (SRIQD.capCard card B) (h.tyF b) S) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), Θ V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        Function.Injective f ∧ (∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.tyF b) ∧
        (SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) →
          ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ h.toN.lab b c) ∧
        (h.kids = [] → ∀ y, ∃ b, f b = y) ∧
        ∀ b S, gs b = some S → ∃ P : List (Finset (Fin p) × V),
          P.map (fun x => (x.1, SRIQD.vt atom x.2)) = S ∧ (P.map Prod.snd).Nodup ∧
          ∀ u v, J.d u (f b) v ↔ ∃ x ∈ P, u ∈ x.1 ∧ x.2 = v := by
  classical
  obtain ⟨D, hD, F, f, hF, hinj, hty, hlab, hsur⟩ := forest_of_check' (isALCHOIQ_reduceS O card)
    h.toN (checkRealisationN_of_hintDNS hc)
  rw [reduceS, reduceNQ] at hF
  obtain ⟨hb, hnF⟩ := models_iff.1 hF
  rw [basePart_reduceN] at hb
  rw [noms_reduceN] at hnF
  obtain ⟨hFo, hds⟩ := (SRIQD.models_reduceWith_iff SRIQD.Proc.mem_toLFin
    SRIQD.Proc.mem_badQ).1 hb
  set Db := dbase (encTransDN O) with hDb
  set cc := SRIQD.capCard card B
  -- the type of a core element is its hint type
  have htyF : ∀ b, SRIQ.typeOf F (f b) = h.tyF b := fun b => by
    ext a; rw [SRIQ.mem_typeOf]; exact hty a b
  -- the elements: a core element with a given star, or none, and the type
  let valid : Option (Fin h.k) × Finset (Fin (n + encKD O)) → Prop := fun y =>
    DataSat Db cc y.2 ∧ ∀ b, y.1 = some b → ∃ S, gs b = some S ∧ DOK Db cc y.2 S
  let X := {y : Option (Fin h.k) × Finset (Fin (n + encKD O)) // valid y}
  letI : Fintype X := Fintype.ofFinite X
  let o : D → Option (Fin h.k) := fun x =>
    if hx : ∃ b, f b = x ∧ (gs b).isSome then some hx.choose else none
  have ho : ∀ x b, o x = some b → f b = x ∧ (gs b).isSome := by
    intro x b hob
    simp only [o] at hob
    split_ifs at hob with hx
    cases hob
    exact hx.choose_spec
  have hob : ∀ b, (gs b).isSome → o (f b) = some b := by
    intro b hs
    have hx : ∃ b', f b' = f b ∧ (gs b').isSome := ⟨b, rfl, hs⟩
    simp only [o, dif_pos hx]
    exact congrArg some (hinj hx.choose_spec.1)
  have hval : ∀ x, valid (o x, SRIQ.typeOf F x) := by
    intro x
    refine ⟨(SRIQD.dataSat_cap_iff hB _).2 (hds x), fun b hb => ?_⟩
    obtain ⟨hfb, hs⟩ := ho x b hb
    obtain ⟨S, hS⟩ := Option.isSome_iff_exists.1 hs
    refine ⟨S, hS, ?_⟩
    rw [← hfb, htyF]
    exact hgs b S hS
  let g : D → X := fun x => ⟨(o x, SRIQ.typeOf F x), hval x⟩
  let ty : X → Finset (Fin (n + encKD O)) := fun y => y.1.2
  let fs : X → List (DNbr (Fin p) (Fin q)) := fun y =>
    match hy : y.1.1 with
    | some b => (gs b).getD []
    | none => y.2.1.choose
  have hfs : ∀ y, DOK Db cc (ty y) (fs y) := by
    intro y
    simp only [fs, ty]
    split
    next b hy =>
      obtain ⟨S, hS, hok⟩ := y.2.2 b hy
      rw [hS]
      exact hok
    next => exact y.2.1.choose_spec
  obtain ⟨V, atom, hΘ, P, hP, hmd⟩ := SRIQD.exists_dmodelP (card := cc) hspec.lowCap F hFo g ty
    (fun a x => (SRIQ.mem_typeOf (I := F)).symm) fs hfs
  have hJ' : SRIQD.models atom ({ toInterp := F, d := fun u x v => SRIQD.dOf (P (g x)) u v } :
      DInterp D V _ _ _) (SRIQD.Proc.encTransQD (dbase O)).2 := by
    rw [← dbase_encTransDN]; exact hmd
  refine ⟨D, V, hD, atom, hΘ, _, f, SRIQD.Proc.models_downD hS hJ', fun a ha => ?_, hinj,
    fun a b => hty _ b, fun hAs R b c => (downI_rt_of_alchi hAs F R (f b) (f c)).trans (hlab R b c),
    fun hk => hsur (fun b => by simp [HF.HintS.toN, hk]), fun b S hS => ?_⟩
  · exact hnF (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)
  · have hg : (g (f b)).1.1 = some b := hob b (by rw [hS]; rfl)
    have hfsb : fs (g (f b)) = S := by
      simp only [fs]
      split
      next b' hy =>
        rw [hg] at hy
        cases hy
        rw [hS]; rfl
      next hy => rw [hg] at hy; cases hy
    refine ⟨P (g (f b)), (hP _).1.trans hfsb, (hP _).2, fun u v => Iff.rfl⟩

end Proc

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part validPart_of_mem small_size)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- **The model of an accepted sparse hint, with the given data stars.**
`hintPartsP_model'` with one more conjunct: a core element with a given
data star `S` has exactly one value per entry of `S`, the values pairwise
distinct, of the entry's value type, and the data properties of each
value are the entry's label. -/
theorem hintPartsP_modelD (hc : CellSpec key cells size) {B L : Nat}
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
        (h.kids = [] → ∀ y, ∃ b, f b = y) ∧
        ∀ b S, HF.givenStar h (HF.starsOf (p := p) (q := q) h) b = some S →
          ∃ P : List (Finset (Fin p) × V),
            P.map (fun x => (x.1, SRIQD.vt atom x.2)) = S ∧ (P.map Prod.snd).Nodup ∧
            ∀ u v, J.d u (f b) v ↔ ∃ x ∈ P, u ∈ x.1 ∧ x.2 = v := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  -- the part the stars were checked on
  have hmc : ∀ (c : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))),
      HF.lookCard c (HF.memoTab c L) = c := HF.memoCard_eq
  unfold HF.hintPartsP at hh
  simp only [hmc, HF.partCardT_eq] at hh
  rw [Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  have hx : ∃ x ∈ partsOf size s (cells.filter sp),
      ((List.finRange h.k).all (fun b => HF.okOf (HF.dataOnly (dbase (Proc.encTransDN O)))
        (partCard cells size sp E (toPart s x)) h (HF.starsOf (p := p) (q := q) h) b) &&
      (h.kids.isEmpty || h.recs.all (fun e => SRIQD.Proc.dataSatB
        (HF.dataOnly (dbase (Proc.encTransDN O))) (partCard cells size sp E (toPart s x)) e.ty))) = true := by
    split_ifs at h2
    · rw [Bool.and_eq_true] at h2
      exact ⟨_, HF.mem_of_validPartB h2.1, h2.2⟩
    · obtain ⟨x, hx, hx2⟩ := List.any_eq_true.1 h2
      exact ⟨x, hx, hx2⟩
  obtain ⟨x, hxm, hxok⟩ := hx
  set card := partCard cells size sp E (toPart s x)
  have hspec := oracleSpecB_part (E := E) (key := key) hc hL hsp hcov (validPart_of_mem hfin hxm)
  simp only [Bool.and_eq_true, List.all_eq_true] at hxok
  -- the hint check on that part
  have hdns : Proc.hintDNS O card h.toN = true := by
    unfold Proc.hintDNS
    rw [checkRedN_split]
    have hk : ((List.finRange h.toN.k).all fun b => (h.toN.kids b).isEmpty) = h.kids.isEmpty :=
      HF.noKids_eq h
    rw [← HF.coreB_eq, ← HF.certB_eq, hk]
    rw [Bool.and_eq_true]
    refine ⟨h1, ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun b hb => ?_, ?_⟩
    · have := HF.okOf_imp (hxok.1 b hb)
      rwa [HF.dataSatB_dataOnly] at this
    · have hrec : ∀ ok : Finset (Fin (n + Proc.encKD O)) → Bool,
          (h.toN.recs.all fun e => ok e.1.1) = h.recs.all fun e => ok e.ty := fun ok => by
        simp [HF.HintS.toN, HF.RecS.toN, List.all_map, Function.comp_def]
      rw [hrec, ← HF.dataSatB_dataOnly]
      exact hxok.2
  obtain ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur, hdat⟩ := Proc.hintDNS_modelD
    hspec hS hB hdns (HF.givenStar h (HF.starsOf (p := p) (q := q) h))
    (fun b S hg => HF.dok_of_given hB (HF.okOf_given (hxok.1 b (List.mem_finRange b)) hg))
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur, hdat⟩

end Parts

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQD.exists_dmodelP
#print axioms ContextCalculus.SRIQN.Proc.hintDNS_modelD
#print axioms ContextCalculus.SRIQN.hintPartsP_modelD
