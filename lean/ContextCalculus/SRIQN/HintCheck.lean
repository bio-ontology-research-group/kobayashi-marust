import ContextCalculus.SRIQN.SelfLoop

/-!
# Hint checks without the C2a condition (stage C5)

`docs/V1.7.0-PLAN.md`, section 18. `realisation_sound` (`SRIQN/Forest.lean`)
holds for every core, with no C2a condition: a realisation that passes the
proved check gives a model. C2a is needed only for the completeness of the
reference search. This file states the hint checks of the data routes as
one-directional procedures:

* `Proc.hintDNS O card h`: the hint `h` checks over the object part of the
  transitivity encoding, with one data-star test per type of the hint
  (`checkRedN`, stage C3e). `hintDNS_sound`: then `O` is consistent, under a
  bounded oracle.
* `Proc.hintDNSL`: the same and every core element with a loop carries a
  nominal name (`loopOKH`). `hintDNSL_sound`: then `O` has a model whose
  loops sit at nominal elements (`ConsistentDL`), for an ALCHIQ `O` (no
  transitive role; the Self encoding needs such a model, `encSelf_down`).
* `hintPartsN`, `hintPartsNL`: some part of a cell theory accepts the hint;
  `hintPartsN_sound`, `hintPartsNL_sound`.

No statement here needs C2a or any other fragment condition besides the
SHIQ(D) (resp. ALCHIQ) shape of the base part. Nothing here is complete:
a hint that does not check says nothing.

A hint may have core elements without a nominal name (anonymous shared
elements): `NomOK` asks only that each nominal name holds at exactly one
core element.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd)

namespace Proc

variable {n m p q : Nat}

/-! ## Without loops -/

/-- **Hint check with data**, over the object part of the transitivity
encoding. -/
def hintDNS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)
    (h : HintN (n + encKD O) m) : Bool :=
  checkRedN (SRIQD.objPart (dbase (encTransDN O)))
    (SRIQD.Proc.dataSatB (dbase (encTransDN O)) card) (dnoms (encTransDN O)) h

theorem isALCHOIQ_reduceS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) : IsALCHOIQ (reduceS O card) := by
  unfold IsALCHOIQ reduceS reduceNQ
  rw [basePart_reduceN]
  refine SRIQD.isALCHIQ_reduceWith ?_ _ _
  rw [dbase_encTransDN]
  exact SRIQD.Proc.encTransQD_isALCHIQ _

theorem checkRealisationN_of_hintDNS {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {h : HintN (n + encKD O) m}
    (hc : hintDNS O card h = true) :
    checkRealisationN (basePart (reduceS O card)) (noms (reduceS O card)) h = true := by
  rw [reduceS, reduceNQ, basePart_reduceN, noms_reduceN]
  exact checkRealisationN_of_red (allGci_forbidWith _) (fun t ht => closed_forbidWith
    (fun hb => (SRIQD.Proc.mem_badQ t).1 hb ((SRIQD.Proc.dataSatB_iff t).1 ht))) hc

/-- **Soundness of the hint check with data**, for every hint and without
C2a. -/
theorem hintDNS_sound {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hS : SRIQD.Proc.IsSHIQD (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HintN (n + encKD O) m} (hc : hintDNS O card h = true) : ConsistentDN Θ O := by
  have hr := checkRealisationN_sound (isALCHOIQ_reduceS O card) h
    (checkRealisationN_of_hintDNS hc)
  rw [reduceS, reduceNQ,
    consistentN_reduceNB hspec hB SRIQD.Proc.mem_toLFin SRIQD.Proc.mem_badQ] at hr
  exact (consistentDN_encTransDN hS).2 hr

/-! ## With loops at nominal elements -/

/-- Every core element with a loop has a nominal name of `N`. -/
def loopOKH (N : List (Fin n)) (h : HintN n m) : Bool :=
  (List.finRange h.k).all fun c => decide (h.lab c c = ∅) || N.any fun a => decide (a ∈ h.ty c)

/-- A hint that checks and whose loops sit at nominal core elements gives a
model whose loops sit at nominal elements. -/
theorem checkRealisationN_loop {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : HintN n m)
    (hc : checkRealisationN (basePart O) (noms O) h = true) (hl : loopOKH (noms O) h = true) :
    ∃ (D : Type) (_ : Nonempty D) (F : Interp D (Fin n) (Fin m)), models F O ∧
      LoopNom F (noms O) := by
  simp only [checkRealisationN, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_finRange, true_implies, List.isEmpty_iff] at hc
  obtain ⟨⟨hpos, hcore, hstar⟩, hkids⟩ := hc
  let r := realOfCoreN hcore fun b => ⟨h.kids b, hstar b, fun e he => by
    rcases hkids with (hk | hk) | hk
    · rw [hk b] at he
      simp at he
    · exact cert_good hk b e he
    · exact (good_iff_mem_aliveN _).2 (hk b e he)⟩
  refine ⟨_, ⟨⟨.inl ⟨0, hpos⟩, trivial⟩⟩, forestN r,
    models_iff.2 ⟨forestN_models_base r hA, fun a ha => forestN_nom r ha⟩, ?_⟩
  intro R x hx
  obtain ⟨c, hc, hR⟩ := forestN_loop r hx
  have hl' := List.all_eq_true.1 hl c (List.mem_finRange c)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hl'
  rcases hl' with he | ⟨a, ha, hac⟩
  · exact absurd (he ▸ hR : R ∈ (∅ : Finset (RoleT (Fin m)))) (Finset.notMem_empty _)
  · refine ⟨a, ha, ?_⟩
    show a ∈ typN r x.1
    rw [hc]
    exact hac

/-- **Hint check with data and loops at nominal elements.** -/
def hintDNSL (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)
    (h : HintN (n + encKD O) m) : Bool :=
  hintDNS O card h && loopOKH (dnoms (encTransDN O)) h

theorem not_mem_transTerms {O : SRI.Ontology (Fin n) (Fin m)} (hA : SRI.IsALCHI O)
    (T : RoleT (Fin m)) : T ∉ SRI.Proc.transTerms O := by
  intro hT
  rcases SRI.Proc.mem_transTerms.1 hT with h | h
  · exact absurd (hA _ _ h) (by simp)
  · exact absurd (hA _ _ h) (by simp)

theorem downI_rt_of_alchi {O : SRI.Ontology (Fin n) (Fin m)} (hA : SRI.IsALCHI O) {D : Type}
    (J : Interp D (Fin (n + (SRI.Proc.transPairs O).length)) (Fin m)) (R : RoleT (Fin m))
    (x y : D) : (SRI.Proc.downI O J).rt R x y ↔ J.rt R x y := by
  have hr : ∀ r x y, (SRI.Proc.downI O J).r r x y ↔ J.r r x y := fun r x y => by
    simp only [SRI.Proc.downI]
    exact ⟨fun h => h.resolve_right fun ⟨T, hT, _⟩ => not_mem_transTerms hA T hT, Or.inl⟩
  cases R with
  | pos r => exact hr r x y
  | inv r => exact hr r y x

/-- **Soundness of the hint check with loops**, for an ALCHIQ ontology: a
model whose loops sit at nominal elements. -/
theorem hintDNSL_sound {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hA : SRIQD.IsALCHIQ (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HintN (n + encKD O) m} (hc : hintDNSL O card h = true) : ConsistentDL Θ O := by
  simp only [hintDNSL, Bool.and_eq_true] at hc
  obtain ⟨hc, hl⟩ := hc
  have hl' : loopOKH (noms (reduceS O card)) h = true := by
    rw [reduceS, reduceNQ, noms_reduceN]; exact hl
  obtain ⟨D, hD, F, hF, hL⟩ := checkRealisationN_loop (isALCHOIQ_reduceS O card) h
    (checkRealisationN_of_hintDNS hc) hl'
  rw [reduceS, reduceNQ] at hF hL
  obtain ⟨hb, hnF⟩ := models_iff.1 hF
  rw [basePart_reduceN] at hb
  rw [noms_reduceN] at hnF hL
  obtain ⟨hFo, hds⟩ := (SRIQD.models_reduceWith_iff SRIQD.Proc.mem_toLFin
    SRIQD.Proc.mem_badQ).1 hb
  obtain ⟨V, atom, hΘ, d, hmd⟩ := SRIQD.exists_dmodel_types (card := SRIQD.capCard card B)
    hspec.lowCap F hFo (SRIQ.typeOf F) (fun a x => (SRIQ.mem_typeOf F).symm)
    (fun x => (SRIQD.dataSat_cap_iff hB _).2 (hds x))
  -- down through the transitivity encoding, which changes no role on an ALCHIQ ontology
  have hS : SRIQD.Proc.IsSHIQD (dbase O) :=
    ⟨fun body S hcl => Or.inl (hA body S hcl), fun a k R b _ T hT => absurd (hA _ _ hT) (by simp)⟩
  have hJ' : SRIQD.models atom ({ toInterp := F, d := d } : DInterp D V _ _ _)
      (SRIQD.Proc.encTransQD (dbase O)).2 := by
    rw [← dbase_encTransDN]; exact hmd
  have hAs : SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) := SRIQ.isALCHI_sriPart hA
  refine ⟨D, V, hD, atom, hΘ, _, SRIQD.Proc.models_downD hS hJ', fun a ha => ?_, ?_⟩
  · exact hnF (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)
  · intro R x hx
    have hx' := (downI_rt_of_alchi hAs F R x x).1 hx
    obtain ⟨a', ha', hax⟩ := hL R x hx'
    rw [dnoms_encTransDN] at ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
    exact ⟨a, ha, hax⟩

end Proc

/-! ## Parts of a cell theory -/

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part validPart_of_mem small_size)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}
variable {n m p : Nat}

/-- Some part accepts the hint. -/
def hintPartsN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : Proc.HintN (n + Proc.encKD O) m) : Bool :=
  (partsOf size s (cells.filter sp)).any fun x =>
    Proc.hintDNS O (partCard cells size sp E (toPart s x)) h

/-- Some part accepts the hint, with loops at nominal elements. -/
def hintPartsNL (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : Proc.HintN (n + Proc.encKD O) m) : Bool :=
  (partsOf size s (cells.filter sp)).any fun x =>
    Proc.hintDNSL O (partCard cells size sp E (toPart s x)) h

/-- **Soundness of the hint check over the parts**, without C2a. -/
theorem hintPartsN_sound (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hS : SRIQD.Proc.IsSHIQD (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : Proc.HintN (n + Proc.encKD O) m}
    (hh : hintPartsN O cells size sp E h = true) : ConsistentDN (cellTheory key E) O := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  obtain ⟨xa, hxa, hx⟩ := List.any_eq_true.1 hh
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn⟩ := Proc.hintDNS_sound
    (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hx
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, I, hI, hn⟩

/-- **Soundness of the hint check with loops over the parts**, for an
ALCHIQ ontology. -/
theorem hintPartsNL_sound (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : SRIQD.IsALCHIQ (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : Proc.HintN (n + Proc.encKD O) m}
    (hh : hintPartsNL O cells size sp E h = true) : ConsistentDL (cellTheory key E) O := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  obtain ⟨xa, hxa, hx⟩ := List.any_eq_true.1 hh
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn, hl⟩ := Proc.hintDNSL_sound
    (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hA hB hx
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, I, hI, hn, hl⟩

end Parts

/-! ## The part loop with the part-independent checks done once

`checkRedN` reads the part only through the data-star test `ok`; the core
conditions and the certificate check are the same for every part. The
`@[csimp]` equalities below check them once and then loop over the parts
with the data-star tests only. -/

section Fast

open ContextCalculus.SRIQD (partsOf toPart partCard)

variable {Val K : Type} [DecidableEq K] {q s : Nat}
variable {n m p : Nat}

theorem bool_split (a t k r c : Bool) :
    (a && t && (k || (r && c))) = ((a && (k || c)) && (t && (k || r))) := by
  cases a <;> cases t <;> cases k <;> cases r <;> cases c <;> rfl

theorem checkRedN_split (A : SRIQ.Ontology (Fin n) (Fin m)) (ok : Finset (Fin n) → Bool)
    (N : List (Fin n)) (h : Proc.HintN n m) :
    Proc.checkRedN A ok N h =
      ((decide (0 < h.k ∧ Proc.coreOKN N h.ty h.lab ∧
          ∀ b, SRIQ.StarOK A (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)) &&
        ((List.finRange h.k).all (fun b => (h.kids b).isEmpty) || decide (Proc.CertOK A N h))) &&
      ((List.finRange h.k).all (fun b => ok (h.ty b)) &&
        ((List.finRange h.k).all (fun b => (h.kids b).isEmpty) || h.recs.all (fun e => ok e.1.1)))) := by
  unfold Proc.checkRedN
  exact bool_split _ _ _ _ _

theorem any_and_const {α : Type} (l : List α) (c : Bool) (f : α → Bool) :
    l.any (fun x => c && f x) = (c && l.any f) := by
  cases c <;> simp

/-- `hintPartsN` with the core and certificate checks done once. -/
def hintPartsNF (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : Proc.HintN (n + Proc.encKD O) m) : Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let A := SRIQD.objPart Db
  let N := dnoms D
  let noKids := (List.finRange h.k).all (fun b => (h.kids b).isEmpty)
  (decide (0 < h.k ∧ Proc.coreOKN N h.ty h.lab ∧
      ∀ b, SRIQ.StarOK A (h.ty b) (SRIQ.Proc.nbrsL h.ty h.lab b ++ h.kids b)) &&
    (noKids || decide (Proc.CertOK A N h))) &&
  (partsOf size s (cells.filter sp)).any fun x =>
    let ok := SRIQD.Proc.dataSatB Db (partCard cells size sp E (toPart s x))
    (List.finRange h.k).all (fun b => ok (h.ty b)) && (noKids || h.recs.all (fun e => ok e.1.1))

@[csimp] theorem hintPartsN_eq_F : @hintPartsN = @hintPartsNF := by
  funext K _ q s n m p O cells size sp E h
  simp only [hintPartsN, hintPartsNF, Proc.hintDNS, checkRedN_split, any_and_const]

/-- `hintPartsNL` with the core, certificate and loop checks done once. -/
def hintPartsNLF (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : Proc.HintN (n + Proc.encKD O) m) : Bool :=
  Proc.loopOKH (dnoms (Proc.encTransDN O)) h && hintPartsNF O cells size sp E h

@[csimp] theorem hintPartsNL_eq_F : @hintPartsNL = @hintPartsNLF := by
  funext K _ q s n m p O cells size sp E h
  have : ∀ (a b : Bool), (a && b) = (b && a) := fun a b => by cases a <;> cases b <;> rfl
  simp only [hintPartsNL, hintPartsNLF, Proc.hintDNSL, this _ (Proc.loopOKH _ _), any_and_const]
  rw [← hintPartsN_eq_F]
  rfl

end Fast

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.Proc.hintDNS_sound
#print axioms ContextCalculus.SRIQN.Proc.hintDNSL_sound
#print axioms ContextCalculus.SRIQN.hintPartsN_sound
#print axioms ContextCalculus.SRIQN.hintPartsNL_sound
#print axioms ContextCalculus.SRIQN.hintPartsN_eq_F
#print axioms ContextCalculus.SRIQN.hintPartsNL_eq_F
