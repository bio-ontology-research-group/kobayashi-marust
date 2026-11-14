import ContextCalculus.SRIQN.Data
import ContextCalculus.SRIQD.KBParts

/-!
# Data with nominals: bounded oracles, transitivity and parts (stage C2a)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, section 6, with the bounded-oracle
machinery of the SHIQ(D) knowledge-base route (`SRIQD/KBB.lean`,
`SRIQD/KBParts.lean`).

* `IsC2aD O`: the object part with the nominal clauses (`objN O`) is C2a.
  A data model shrinks its nominal-only names like an object model
  (`shrinkD_models`: data clauses mention names only as subjects), so the
  reduced ontology, whose forbidding gcis break nominal-only-ness, still
  has small realisations (`small_reduceN`).
* `consistentN_reduceNB`: the reduction under a bounded oracle
  `OracleSpecB Θ card B` with `dbnd ≤ B`.
* `encTransDN`, `consistentDN_encTransDN`: transitivity removal.
* `consistentDNS_iffB`: transitivity removal, reduction and the C2a
  procedure, exact for every hint.
* `consistentPartsN_iff`: some part of a cell theory accepts the ontology
  iff it is consistent in the cell theory, as `SRIQD.consistentParts_iff`.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpec OracleSpecB DataSat dbnd)

variable {CName Role DProp DAtom : Type}

/-- The object part with the nominal clauses. -/
def objN (O : DOntology CName Role DProp DAtom) : Ontology CName Role :=
  ofSRIQ (SRIQD.objPart (dbase O)) ++ (dnoms O).map fun a => .nom (id a)

/-- **C2a with data**: the object part with the nominal clauses is C2a. -/
def IsC2aD (O : DOntology CName Role DProp DAtom) : Prop := IsC2a (objN O)

theorem basePart_objN (O : DOntology CName Role DProp DAtom) :
    basePart (objN O) = SRIQD.objPart (dbase O) :=
  basePart_ofSRIQ_noms _ _ _

theorem noms_objN (O : DOntology CName Role DProp DAtom) : noms (objN O) = dnoms O := by
  rw [objN, noms_append, noms_ofSRIQ]
  simp [noms, List.filterMap_map]

/-! ## Shrinking a data model -/

section Shrink

variable {D V : Type} {atom : DAtom → V → Prop}

/-- A data interpretation with the nominal-only names of the object part
shrunk. -/
noncomputable def shrinkD (O : DOntology CName Role DProp DAtom)
    (I : DInterp D V CName Role DProp) : DInterp D V CName Role DProp :=
  { toInterp := shrinkI (objN O) I.toInterp, d := I.d }

theorem objN_models {O : DOntology CName Role DProp DAtom} {I : DInterp D V CName Role DProp}
    (hI : SRIQD.models atom I (dbase O)) (hn : ∀ a ∈ dnoms O, NomAt I.toInterp a) :
    models I.toInterp (objN O) :=
  models_iff.2 ⟨by rw [basePart_objN]; exact (SRIQD.models_iff.1 hI).1,
    by rw [noms_objN]; exact hn⟩

theorem shrinkD_models {O : DOntology CName Role DProp DAtom} {I : DInterp D V CName Role DProp}
    (hI : SRIQD.models atom I (dbase O)) (hn : ∀ a ∈ dnoms O, NomAt I.toInterp a) :
    SRIQD.models atom (shrinkD O I) (dbase O) ∧ ∀ a ∈ dnoms O, NomAt (shrinkD O I).toInterp a := by
  have hO := objN_models hI hn
  have hS := shrinkI_models hO
  have hb : SRIQ.models I.toInterp (basePart (objN O)) := (models_iff.1 hO).1
  obtain ⟨hSb, hSn⟩ := models_iff.1 hS
  rw [basePart_objN] at hSb
  rw [noms_objN] at hSn
  refine ⟨SRIQD.models_iff.2 ⟨hSb, fun cl hcl y => ?_⟩, hSn⟩
  have hl := (SRIQD.models_iff.1 hI).2 cl hcl y
  have sub : ∀ a, (shrinkD O I).c a y → I.c a y := fun a h => shrinkI_sub hb h
  cases cl with
  | obj _ => trivial
  | dEx a u pos neg => exact fun h => hl (sub a h)
  | dAll a u head => exact fun h => hl (sub a h)
  | dAtLeast a k u pos neg => exact fun h => hl (sub a h)
  | dAtMost a k u pos neg => exact fun h => hl (sub a h)
  | dSub u w => exact hl

end Shrink

section Reduce

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable [Fintype DProp] [DecidableEq DProp] [Fintype DAtom] [DecidableEq DAtom]
variable {Θ : DataTheory DAtom} {card : Finset DAtom → Option Nat} {B : Nat}

/-- **Reduction under a bounded oracle.** -/
theorem consistentN_reduceNB (hspec : OracleSpecB Θ card B) {O : DOntology CName Role DProp DAtom}
    (hB : dbnd (dbase O) ≤ B) {toL : Finset CName → List CName} (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t)
    {bad : List (Finset CName)} (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat (dbase O) card t) :
    ConsistentN (reduceN O toL bad) ↔ ConsistentDN Θ O := by
  constructor
  · rintro ⟨D, hD, I, hI⟩
    obtain ⟨hb, hn⟩ := models_iff.1 hI
    rw [basePart_reduceN] at hb
    rw [noms_reduceN] at hn
    obtain ⟨hIo, hds⟩ := (SRIQD.models_reduceWith_iff htoL hbad).1 hb
    obtain ⟨V, atom, hΘ, d, hm⟩ := SRIQD.exists_dmodel_types (card := SRIQD.capCard card B)
      hspec.lowCap I hIo (SRIQ.typeOf I) (fun a x => (SRIQ.mem_typeOf I).symm)
      (fun x => (SRIQD.dataSat_cap_iff hB _).2 (hds x))
    exact ⟨D, V, hD, atom, hΘ, _, hm, hn⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    refine ⟨D, hD, I.toInterp, models_iff.2 ⟨?_, ?_⟩⟩
    · rw [basePart_reduceN]
      exact (SRIQD.models_reduceWith_iff htoL hbad).2
        ⟨(SRIQD.models_iff.1 hI).1, SRIQD.dataSat_of_model hspec.upper hΘ hI⟩
    · rw [noms_reduceN]
      exact hn

theorem lowerL_reduceWith (O : SRIQD.Ontology CName Role DProp DAtom)
    (toL : Finset CName → List CName) (bad : List (Finset CName)) :
    SRIQ.lowerL (SRIQD.reduceWith O toL bad) = SRIQ.lowerL (SRIQD.objPart O) := by
  simp [SRIQD.reduceWith, SRIQD.forbidWith, SRIQ.lowerL, List.filterMap_append,
    List.filterMap_map]

theorem upperL_reduceWith (O : SRIQD.Ontology CName Role DProp DAtom)
    (toL : Finset CName → List CName) (bad : List (Finset CName)) :
    SRIQ.upperL (SRIQD.reduceWith O toL bad) = SRIQ.upperL (SRIQD.objPart O) := by
  simp [SRIQD.reduceWith, SRIQD.forbidWith, SRIQ.upperL, List.filterMap_append,
    List.filterMap_map]

theorem chain_mem_reduceWith {O : SRIQD.Ontology CName Role DProp DAtom}
    {toL : Finset CName → List CName} {bad : List (Finset CName)} {rs : List (RoleT Role)}
    {S : RoleT Role} :
    SRIQ.Clause.chain rs S ∈ SRIQD.reduceWith O toL bad ↔
      SRIQ.Clause.chain rs S ∈ SRIQD.objPart O := by
  simp [SRIQD.reduceWith, SRIQD.forbidWith]

/-- The reduced ontology is C2a relative to the nominal-only names of the
object part. -/
theorem isC2aS_reduceN {O : DOntology CName Role DProp DAtom} (hC : IsC2aD O)
    (toL : Finset CName → List CName) (bad : List (Finset CName)) :
    IsC2aS (reduceN O toL bad) (NomOnly (objN O)) := by
  intro q hq hqn hqo q' hq' hle
  rw [basePart_reduceN, lowerL_reduceWith] at hq
  rw [basePart_reduceN, upperL_reduceWith] at hq'
  rw [noms_reduceN] at hqn
  rw [basePart_reduceN, roleLe_congr (B' := SRIQD.objPart (dbase O))
    (fun _ _ => chain_mem_reduceWith)] at hle
  refine hC q (by rw [basePart_objN]; exact hq) (by rw [noms_objN]; exact hqn) hqo q'
    (by rw [basePart_objN]; exact hq') ?_
  rw [basePart_objN]
  exact hle

/-- **Small realisations of the reduced ontology.** -/
theorem small_reduceN (hspec : OracleSpecB Θ card B) {O : DOntology CName Role DProp DAtom}
    (hB : dbnd (dbase O) ≤ B) (hC : IsC2aD O) {toL : Finset CName → List CName}
    (htoL : ∀ t a, a ∈ toL t ↔ a ∈ t) {bad : List (Finset CName)}
    (hbad : ∀ t, t ∈ bad ↔ ¬ DataSat (dbase O) card t) (hc : ConsistentN (reduceN O toL bad)) :
    ∃ k, 0 < k ∧ k ≤ max 1 (noms (reduceN O toL bad)).toFinset.card ∧
      Nonempty (RealisationN (basePart (reduceN O toL bad)) (noms (reduceN O toL bad)) (Fin k)) := by
  obtain ⟨D, V, hD, atom, hΘ, I, hI, hn⟩ := (consistentN_reduceNB hspec hB htoL hbad).1 hc
  obtain ⟨hI', hn'⟩ := shrinkD_models hI hn
  have hm : models (shrinkD O I).toInterp (reduceN O toL bad) := by
    refine models_iff.2 ⟨?_, by rw [noms_reduceN]; exact hn'⟩
    rw [basePart_reduceN]
    exact (SRIQD.models_reduceWith_iff htoL hbad).2
      ⟨(SRIQD.models_iff.1 hI').1, SRIQD.dataSat_of_model hspec.upper hΘ hI'⟩
  obtain ⟨k, hk, hle, r, -⟩ := c2a_complete_of (isC2aS_reduceN hC toL bad) _ hm
    fun X hX x hx => by
      obtain ⟨a, ha, hax⟩ := shrinkI_nomOnly hX hx
      rw [noms_objN] at ha
      refine ⟨a, by rw [noms_reduceN]; exact ha, ?_⟩
      exact (shrinkI_c_of_not I.toInterp (nom_not_nomOnly (by rw [noms_objN]; exact ha)) x).2 hax
  exact ⟨k, hk, hle, ⟨r⟩⟩

end Reduce

/-! ## The procedures -/

namespace Proc

variable {n m p q : Nat}

/-- The number of names the transitivity encoding adds. -/
abbrev encKD (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) : Nat :=
  (SRIQD.Proc.encTransQD (dbase O)).1

/-- **Transitivity removal with data and nominals.** -/
def encTransDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    DOntology (Fin (n + encKD O)) (Fin m) (Fin p) (Fin q) :=
  (SRIQD.Proc.encTransQD (dbase O)).2.map DClause.base ++
    (dnoms O).map fun a => .nom (Fin.castAdd (encKD O) a)

theorem dbase_map_noms {C C' R P A : Type} (L : SRIQD.Ontology C R P A) (M : List C')
    (f : C' → C) : dbase (L.map DClause.base ++ M.map fun a => .nom (f a)) = L := by
  simp [dbase, List.filterMap_append, List.filterMap_map]

theorem dbase_encTransDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    dbase (encTransDN O) = (SRIQD.Proc.encTransQD (dbase O)).2 :=
  dbase_map_noms _ _ _

theorem dnoms_encTransDN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) :
    dnoms (encTransDN O) = (dnoms O).map (Fin.castAdd _) := by
  simp only [encTransDN, dnoms, List.filterMap_append, List.filterMap_map]
  simp [List.map_filterMap]

theorem consistentDN_encTransDN {Θ : DataTheory (Fin q)}
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (h : SRIQD.Proc.IsSHIQD (dbase O)) :
    ConsistentDN Θ O ↔ ConsistentDN Θ (encTransDN O) := by
  constructor
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    have hm := SRIQD.Proc.models_upD hI
    refine ⟨D, V, hD, atom, hΘ, _, by rw [dbase_encTransDN]; exact hm, fun a' ha' => ?_⟩
    have ha'' : a' ∈ dnoms (encTransDN O) := ha'
    rw [dnoms_encTransDN] at ha''
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha''
    obtain ⟨x, hx⟩ := hn a ha
    exact ⟨x, fun y => (SRI.Proc.upI_old I.toInterp a y).trans (hx y)⟩
  · rintro ⟨D, V, hD, atom, hΘ, J, hJ, hn⟩
    have hJ' : SRIQD.models atom J (SRIQD.Proc.encTransQD (dbase O)).2 := by
      rw [← dbase_encTransDN]; exact hJ
    refine ⟨D, V, hD, atom, hΘ, _, SRIQD.Proc.models_downD h hJ', fun a ha => ?_⟩
    exact hn (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)

/-- The reduced ontology over `Fin` names after transitivity removal. -/
def reduceS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat) :
    Ontology (Fin (n + encKD O)) (Fin m) :=
  reduceNQ (encTransDN O) card

/-- **Consistency with data, nominals and transitivity**, a hint first. -/
def consistentDNS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (hint : Option (HintN (n + encKD O) m)) : Bool :=
  consistentN (basePart (reduceS O card)) (noms (reduceS O card)) hint

theorem consistentDNS_iffB {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat}
    {B : Nat} (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (h : SRIQD.Proc.IsSHIQD (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    (hC : IsC2aD (encTransDN O)) (hint : Option (HintN (n + encKD O) m)) :
    consistentDNS O card hint = true ↔ ConsistentDN Θ O := by
  have hA : IsALCHOIQ (reduceS O card) := by
    unfold IsALCHOIQ reduceS reduceNQ
    rw [basePart_reduceN]
    refine SRIQD.isALCHIQ_reduceWith ?_ _ _
    rw [dbase_encTransDN]
    exact SRIQD.Proc.encTransQD_isALCHIQ _
  rw [consistentDNS, consistentN_iff_of hA (small_reduceN hspec hB hC SRIQD.Proc.mem_toLFin
    SRIQD.Proc.mem_badQ), reduceS, reduceNQ,
    consistentN_reduceNB hspec hB SRIQD.Proc.mem_toLFin SRIQD.Proc.mem_badQ,
    ← consistentDN_encTransDN h]

end Proc

/-! ## Parts of a cell theory -/

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part part_of_cellTheory partTheory countsOf mem_partsOf
  mem_comps validPart_of_mem small_size lookup_map getD_idxOf_map)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {q s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}
variable {n m p : Nat}

/-- Some part accepts the ontology. -/
def consistentPartsN (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hint : Option (Proc.HintN (n + Proc.encKD O) m)) : Bool :=
  (partsOf size s (cells.filter sp)).any fun x =>
    Proc.consistentDNS O (partCard cells size sp E (toPart s x)) hint

/-- **Consistency over the parts**, for every hint. -/
theorem consistentPartsN_iff (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hS : SRIQD.Proc.IsSHIQD (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) (hC : IsC2aD (Proc.encTransDN O))
    (hint : Option (Proc.HintN (n + Proc.encKD O) m)) :
    consistentPartsN O cells size sp E hint = true ↔ ConsistentDN (cellTheory key E) O := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  unfold consistentPartsN
  rw [List.any_eq_true]
  constructor
  · rintro ⟨xa, hxa, h⟩
    obtain ⟨D, V, hD, atom, hΘ, I, hI, hn⟩ := (Proc.consistentDNS_iffB
      (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hC hint).1 h
    exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, I, hI, hn⟩
  · rintro ⟨D, V, hD, atom, hΘ, I, hI, hn⟩
    obtain ⟨fr, hval, hpart⟩ := part_of_cellTheory hc hfin hΘ
    let sc := cells.filter sp
    let xa : List (K × List Nat) := sc.map fun c => (c, (allG s).map (countsOf key fr c))
    have hxa : xa ∈ partsOf size s sc := by
      refine mem_partsOf.2 ⟨by simp [xa, Function.comp_def], fun pr hpr => ?_⟩
      obtain ⟨c, hcs, rfl⟩ := List.mem_map.1 hpr
      obtain ⟨hcc, hs⟩ := List.mem_filter.1 hcs
      refine mem_comps.2 ⟨by simp, ?_⟩
      have := hval c hcc hs
      simp [this]
    have hagree : ∀ c ∈ cells, sp c = true → ∀ g, toPart s xa c g = countsOf key fr c g := by
      intro c hcc hs g
      unfold toPart
      rw [lookup_map sc _ (List.mem_filter.2 ⟨hcc, hs⟩), Option.getD_some, getD_idxOf_map]
    have hpart' : partTheory key cells sp E (toPart s xa) V atom := by
      obtain ⟨e, fr', hin, hat⟩ := hpart
      refine ⟨e, fr', fun c hcc hs g => ?_, hat⟩
      rw [hin c hcc hs g, hagree c hcc hs g]
    refine ⟨xa, hxa, (Proc.consistentDNS_iffB
      (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hS hB hC hint).2
      ⟨D, V, hD, atom, hpart', I, hI, hn⟩⟩

end Parts

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.consistentN_reduceNB
#print axioms ContextCalculus.SRIQN.small_reduceN
#print axioms ContextCalculus.SRIQN.Proc.consistentDN_encTransDN
#print axioms ContextCalculus.SRIQN.Proc.consistentDNS_iffB
#print axioms ContextCalculus.SRIQN.consistentPartsN_iff
