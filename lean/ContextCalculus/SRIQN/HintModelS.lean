import ContextCalculus.SRIQN.HintModel
import ContextCalculus.SROIQ.ChainSelf

/-!
# The model of an accepted hint on the Self routes, with its core (stage H2)

The Self routes of `sroiq-hint` check a hint with loops at nominal core
elements over the Self encoding (`encSelfD`) of the chain encoding. This
file carries the forest of the hint, with the map of its core, down
through the data reduction and the transitivity encoding
(`hintPartsNL_model`), the Self encoding (`encSelf_core`) and chain
elimination with self clauses (`chainSelf_core`); the concept names move
by `Fin.castAdd` at each step.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQD (DInterp DataTheory OracleSpecB DataSat dbnd)

variable {n m p q : Nat}

/-- **The forest of an accepted hint whose loops sit at nominal core
elements**, with its core. -/
theorem forest_of_check_loop {O : Ontology (Fin n) (Fin m)} (hA : IsALCHOIQ O) (h : Proc.HintN n m)
    (hc : Proc.checkRealisationN (basePart O) (noms O) h = true)
    (hl : Proc.loopOKH (noms O) h = true) :
    ∃ (D : Type) (_ : Nonempty D) (F : Interp D (Fin n) (Fin m)) (f : Fin h.k → D), models F O ∧
      LoopNom F (noms O) ∧ Function.Injective f ∧ ∀ a b, F.c a (f b) ↔ a ∈ h.ty b := by
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
    models_iff.2 ⟨forestN_models_base r hA, fun a ha => forestN_nom r ha⟩, ?_, ?_,
    fun a b => Iff.rfl⟩
  · intro R x hx
    obtain ⟨c, hc, hR⟩ := forestN_loop r hx
    have hl' := List.all_eq_true.1 hl c (List.mem_finRange c)
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hl'
    rcases hl' with he | ⟨a, ha, hac⟩
    · exact absurd (he ▸ hR : R ∈ (∅ : Finset (RoleT (Fin m)))) (Finset.notMem_empty _)
    · refine ⟨a, ha, ?_⟩
      show a ∈ typN r x.1
      rw [hc]
      exact hac
  · intro b c hbc
    have := congrArg Subtype.val hbc
    simpa using this

namespace Proc

/-- **The model of an accepted data hint with loops at nominal elements.** -/
theorem hintDNSL_model {Θ : DataTheory (Fin q)} {card : Finset (Fin q) → Option Nat} {B : Nat}
    (hspec : OracleSpecB Θ card B) {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    (hA : SRIQD.IsALCHIQ (dbase O)) (hB : dbnd (dbase (encTransDN O)) ≤ B)
    {h : HintN (n + encKD O) m} (hc : hintDNSL O card h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), Θ V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        LoopNom J.toInterp (dnoms O) ∧
        Function.Injective f ∧ ∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.ty b := by
  simp only [hintDNSL, Bool.and_eq_true] at hc
  obtain ⟨hc, hl⟩ := hc
  have hl' : loopOKH (noms (reduceS O card)) h = true := by
    rw [reduceS, reduceNQ, noms_reduceN]; exact hl
  obtain ⟨D, hD, F, f, hF, hL, hinj, hty⟩ := forest_of_check_loop (isALCHOIQ_reduceS O card) h
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
  have hS : SRIQD.Proc.IsSHIQD (dbase O) :=
    ⟨fun body S hcl => Or.inl (hA body S hcl), fun a k R b _ T hT => absurd (hA _ _ hT) (by simp)⟩
  have hJ' : SRIQD.models atom ({ toInterp := F, d := d } : DInterp D V _ _ _)
      (SRIQD.Proc.encTransQD (dbase O)).2 := by
    rw [← dbase_encTransDN]; exact hmd
  have hAs : SRI.IsALCHI (SRIQ.sriPart (SRIQD.objPart (dbase O))) := SRIQ.isALCHI_sriPart hA
  refine ⟨D, V, hD, atom, hΘ, _, f, SRIQD.Proc.models_downD hS hJ', fun a ha => ?_, ?_, hinj,
    fun a b => hty _ b⟩
  · exact hnF (Fin.castAdd _ a) (by rw [dnoms_encTransDN]; exact List.mem_map_of_mem ha)
  · intro R x hx
    have hx' := (downI_rt_of_alchi hAs F R x x).1 hx
    obtain ⟨a', ha', hax⟩ := hL R x hx'
    rw [dnoms_encTransDN] at ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
    exact ⟨a, ha, hax⟩

end Proc

section Parts

open ContextCalculus.SRIQD (CellSpec cellTheory partsOf toPart partCard small allG vtc
  oracleSpecB_part cellTheory_of_part validPart_of_mem small_size)

set_option linter.unusedSectionVars false

variable {Val K : Type} [DecidableEq K] {s : Nat}
  {key : Val → K} {cells : List K} {size : K → Option Nat}
  {E : Fin q → K → (Fin s → Bool) → Bool}

/-- **The model of a hint accepted by some part, with loops at nominal elements.** -/
theorem hintPartsNL_model (hc : CellSpec key cells size) {B L : Nat}
    (hL : B * (allG s).length ≤ L) {sp : K → Bool}
    (hsp : ∀ c ∈ cells, sp c = true → small size L c = true)
    (hcov : ∀ c ∈ cells, sp c = false → small size L c = true → ∀ g,
      ∃ c' ∈ cells, ∃ g', small size L c' = false ∧ vtc E c' g' = vtc E c g)
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hA : SRIQD.IsALCHIQ (dbase O))
    (hB : dbnd (dbase (Proc.encTransDN O)) ≤ B) {h : Proc.HintN (n + Proc.encKD O) m}
    (hh : hintPartsNL O cells size sp E h = true) :
    ∃ (D V : Type) (_ : Nonempty D) (atom : Fin q → V → Prop), cellTheory key E V atom ∧
      ∃ (J : DInterp D V (Fin n) (Fin m) (Fin p)) (f : Fin h.k → D),
        SRIQD.models atom J (dbase O) ∧ (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧
        LoopNom J.toInterp (dnoms O) ∧
        Function.Injective f ∧ ∀ (a : Fin n) b, J.c a (f b) ↔ Fin.castAdd _ a ∈ h.ty b := by
  classical
  have hfin : ∀ c ∈ cells, sp c = true → ∃ k, size c = some k := fun c hc hs => by
    obtain ⟨k, hk, -⟩ := small_size (hsp c hc hs); exact ⟨k, hk⟩
  obtain ⟨xa, hxa, hx⟩ := List.any_eq_true.1 hh
  obtain ⟨D, V, hD, atom, hΘ, J, f, hJ, hn, hl, hinj, hty⟩ := Proc.hintDNSL_model
    (oracleSpecB_part hc hL hsp hcov (validPart_of_mem hfin hxa)) hA hB hx
  exact ⟨D, V, hD, atom, cellTheory_of_part hΘ, J, f, hJ, hn, hl, hinj, hty⟩

end Parts

/-! ## The Self encoding down, with the concepts -/

open SelfE in
theorem encSelf_core {D V : Type} {atom : Fin q → V → Prop}
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)}
    {SC : List (SClause (Fin n) (Fin m))} {lam irr : List (RoleT (Fin m))}
    (hok : LamOK (SRIQD.objPart (dbase O)) SC lam irr) (hA : SRIQ.IsALCHIQ (SRIQD.objPart (dbase O)))
    {F : DInterp D V (SelfE.NC (SRIQD.objPart (dbase O))) (Fin m) (Fin p)}
    (hFm : SRIQD.models atom F (dbase (encSelfD O SC lam irr)))
    (hn : ∀ a ∈ dnoms (encSelfD O SC lam irr), NomAt F.toInterp a)
    (hL : LoopNom F.toInterp (dnoms (encSelfD O SC lam irr))) :
    ∃ J : DInterp D V (Fin n) (Fin m) (Fin p), SRIQD.models atom J (dbase O) ∧
      (∀ a ∈ dnoms O, NomAt J.toInterp a) ∧ (∀ sc ∈ SC, satS J.toInterp sc) ∧
      ∀ a y, J.c a y ↔ F.c (Fin.castAdd _ a) y := by
  rw [dnoms_encSelfD] at hn hL
  obtain ⟨hFo, hFd⟩ := SRIQD.models_iff.1 hFm
  rw [objPart_encSelfD] at hFo
  refine ⟨downS F lam, SRIQD.models_iff.2 ⟨downS_obj hok hFo hL hA,
    fun cl hcl y => ?_⟩, fun a ha => ?_, downS_self hok hFo hL, fun a y => Iff.rfl⟩
  · cases hl : SRIQD.Proc.liftData (kF n m (SRIQD.objPart (dbase O)).length) cl with
    | none =>
      cases cl <;> simp only [SRIQD.Proc.liftData, reduceCtorEq] at hl
      trivial
    | some cl' =>
      have hm : cl' ∈ dbase (encSelfD O SC lam irr) := by
        rw [dbase_encSelfD]
        exact List.mem_append_right _ (List.mem_filterMap.2 ⟨cl, hcl, hl⟩)
      exact (SRIQD.Proc.dLocal_liftData atom hl _ _).1 (hFd cl' hm y)
  · exact hn _ (mem_nomL.2 (Or.inl ⟨a, ha, rfl⟩))

end ContextCalculus.SRIQN

namespace ContextCalculus.SROIQ.Proc

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQN (DOntology dbase dnoms SClause satS NomAt)

variable {n m p q : Nat}

/-- **Chain elimination with self clauses, with the concepts.** -/
theorem chainSelf_core {D V : Type} {atom : Fin q → V → Prop}
    {O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)} {SC : List (SClause (Fin n) (Fin m))}
    (h : CondCD O) (hs : SelfSimple O SC)
    {J : SRIQD.DInterp D V (Fin (n + kCD O)) (Fin m) (Fin p)}
    (hJ : SRIQD.models atom J (dbase (encChainDN O)))
    (hn : ∀ a ∈ dnoms (encChainDN O), NomAt J.toInterp a)
    (hS : ∀ sc ∈ liftSC O SC, satS J.toInterp sc) :
    ∃ J' : SRIQD.DInterp D V (Fin n) (Fin m) (Fin p), SRIQD.models atom J' (dbase O) ∧
      (∀ a ∈ dnoms O, NomAt J'.toInterp a) ∧ (∀ sc ∈ SC, satS J'.toInterp sc) ∧
      ∀ a y, J'.c a y ↔ J.c (Fin.castAdd _ a) y := by
  rw [dbase_encChainDN] at hJ
  have hJo : SRIQ.models J.toInterp (encChain (SRIQD.objPart (dbase O))) := by
    have := (SRIQD.models_iff.1 hJ).1
    rwa [objPart_encChainQD] at this
  refine ⟨_, models_encChainQD_down h hJ, fun a ha => ?_, fun sc hsc => ?_, fun a y => Iff.rfl⟩
  · exact hn (Fin.castAdd _ a) (by rw [dnoms_encChainDN]; exact List.mem_map_of_mem ha)
  · have := hS _ (List.mem_map_of_mem (f := SClause.mapC (Fin.castAdd _)) hsc)
    cases sc with
    | selfR body R =>
      intro x hx
      have h1 := this x fun a' ha' => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
        exact (downC_old J.toInterp a x).1 (hx a ha)
      exact (downC_rt R x x).2 ⟨[R], gen_self R, (path_single _ R x x).2 h1⟩
    | selfL R head =>
      intro x hx
      have h1 := (downC_rt_simple hJo (hs R head hsc) x x).1 hx
      obtain ⟨b', hb', hbx⟩ := this x h1
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hb'
      exact ⟨b, hb, hbx⟩

end ContextCalculus.SROIQ.Proc

#print axioms ContextCalculus.SRIQN.forest_of_check_loop
#print axioms ContextCalculus.SRIQN.Proc.hintDNSL_model
#print axioms ContextCalculus.SRIQN.hintPartsNL_model
#print axioms ContextCalculus.SRIQN.encSelf_core
#print axioms ContextCalculus.SROIQ.Proc.chainSelf_core
