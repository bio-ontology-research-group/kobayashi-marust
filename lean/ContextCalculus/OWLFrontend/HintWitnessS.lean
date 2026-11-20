import ContextCalculus.OWLFrontend.HintBuiltin
import ContextCalculus.SRIQN.HintModelS

/-!
# The witness row on the Self and `ObjectHasSelf` routes (stage H2, item 1)

`wTabSCore X P req hint` is the Self route of `sroiq-hint` (`owlSelfHint`,
`P = []`) and the route with `ObjectHasSelf` (`owlHSHintOn`, `P` the pairs
of `selfPairs`) with the requested classes given to the translation.
`wTabSCore_facts`: an accepted hint gives a model of `X` in which the pairs
hold, with the core inside it and the requested classes and named
individuals read off the core types (`WF`, the facts `wTab_model` gives
for the chain route).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SRIQN (dbase dnoms NomAt)

/-- The facts the witness rows read, for a model of `X` in which `Q` holds. -/
def WF (pat : String → String → Prop) (X : Ontology) (Q : ∀ {Dom : Type}, Interp (owl2MapP pat) Dom → Prop)
    (W : WTab) : Prop :=
  ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
    OWL.Model X I ∧ Q I ∧ Function.Injective f ∧
    (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
    (∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) ∧
    (∀ r R, (r, R) ∈ W.props → ∀ w v, w ≠ v → (I.prop r (f w) (f v) ↔ R ∈ W.lab w v))

/-- The Self route with the pairs `P` (`P = []`: the Self route; otherwise
the route with `ObjectHasSelf` on the rewritten ontology). -/
def wTabSCore (X : Ontology) (P : List (IRI × ObjProp)) (req : List IRI) (hint : RawHint) :
    Option WTab :=
  if X.isSROIQDSKB then
    let rq := req ++ pairNames P
    match translateSHOIQD (roleOff (selfOff X)) rq with
    | none => none
    | some T =>
      match roleCls T (selfOff X), selfCls T X, pairCls T P with
      | some E, some SC, some PC =>
        let L := nomNames (roleOff (selfOff X)) rq
        if sroiqSHOK T L E (SC ++ PC) then
          let sp := spec T.tab
          let as := allBases sp
          let cs := cellsOf as
          let szS := cellSizeS as
          let sz := szS.f
          let eS := owlES sp
          let oe := eS.f
          let D := encS T L E (SC ++ PC)
          let spT := SRIQN.HF.splitTab cs sz (sroiqSBound T L E (SC ++ PC)) oe
          match hint.toHintS _ _ with
          | none => none
          | some h =>
            if SRIQN.HF.hintPartsNLP D cs sz
                (SRIQN.HF.lookSplit spT
                  (ContextCalculus.SRIQD.splitCell cs sz (sroiqSBound T L E (SC ++ PC)) oe))
                oe h then
              let mp := namedMap T.obj.named
              let arr := T.obj.named.toArray
              let emb := fun x : Fin T.obj.conceptCount =>
                Fin.castAdd (SRIQN.Proc.encKD D) (Fin.castAdd _ (Fin.castAdd (SROIQ.Proc.kCD (dosnC T L E)) x))
              let base := nomBase (roleOff (selfOff X)) rq
              let ob := objC T L E
              let hm := Std.HashMap.ofList (SROIQ.Proc.mkTab ob)
              let le := SROIQ.Proc.leH hm
              let rs := SROIQ.rules ob
              some { N := _, k := h.k, ty := h.tyF
                     cls := req.filterMap fun s => (ixOfA T arr rfl mp s).map fun x => (s, emb x)
                     inds := (roleOff (selfOff X)).individualNames.zipIdx.filterMap fun p =>
                       (ixOfA T arr rfl mp (nomName base p.2)).map fun x => (p.1, emb x)
                     M := T.obj.roleCount, lab := h.toN.lab
                     props := propsOf T fun R =>
                       SROIQ.Proc.selfSimpleBL (n := T.obj.conceptCount) le rs [.selfL R []] }
            else none
        else none
      | _, _, _ => none
  else none

def wTabSCoreF (X : Ontology) (P : List (IRI × ObjProp)) (req : List IRI) (hint : RawHint) :
    Option WTab :=
  if X.isSROIQDSKB then
    let rq := req ++ pairNames P
    match translateSHOIQD (roleOff (selfOff X)) rq with
    | none => none
    | some T =>
      match roleCls T (selfOff X), selfCls T X, pairCls T P with
      | some E, some SC, some PC =>
        let L := nomNames (roleOff (selfOff X)) rq
        if sroiqSHOK T L E (SC ++ PC) then
          let spS := specS T.tab
          let sp := spS.f
          let as := allBases sp
          let cs := cellsOf as
          let szS := cellSizeS as
          let sz := szS.f
          let eS := owlES sp
          let oe := eS.f
          let vS := vtcOwlS sp
          let D := encS T L E (SC ++ PC)
          let bnd := ContextCalculus.SRIQD.dbnd (SRIQN.dbase (SRIQN.Proc.encTransDN D)) *
            (ContextCalculus.SRIQD.allG (allFrees sp).length).length
          let spT := SRIQN.HF.splitTabV cs sz bnd vS.f
          match hint.toHintS _ _ with
          | none => none
          | some h =>
            if SRIQN.HF.hintPartsNLPV D cs sz
                (SRIQN.HF.lookSplitHS spT (ContextCalculus.SRIQD.splitCell cs sz bnd oe)).f
                vS.f h then
              let mp := namedMap T.obj.named
              let arr := T.obj.named.toArray
              let emb := fun x : Fin T.obj.conceptCount =>
                Fin.castAdd (SRIQN.Proc.encKD D) (Fin.castAdd _ (Fin.castAdd (SROIQ.Proc.kCD (dosnC T L E)) x))
              let base := nomBase (roleOff (selfOff X)) rq
              let ob := objC T L E
              let hm := Std.HashMap.ofList (SROIQ.Proc.mkTab ob)
              let le := SROIQ.Proc.leH hm
              let rs := SROIQ.rules ob
              some { N := _, k := h.k, ty := h.tyF
                     cls := req.filterMap fun s => (ixOfA T arr rfl mp s).map fun x => (s, emb x)
                     inds := (roleOff (selfOff X)).individualNames.zipIdx.filterMap fun p =>
                       (ixOfA T arr rfl mp (nomName base p.2)).map fun x => (p.1, emb x)
                     M := T.obj.roleCount, lab := h.toN.lab
                     props := propsOf T fun R =>
                       SROIQ.Proc.selfSimpleBL (n := T.obj.conceptCount) le rs [.selfL R []] }
            else none
        else none
      | _, _, _ => none
  else none

@[csimp] theorem wTabSCore_eq_F : @wTabSCore = @wTabSCoreF := by
  funext X P req hint
  unfold wTabSCoreF wTabSCore sroiqSBound
  dsimp only
  split_ifs with hX
  · cases translateSHOIQD (roleOff (selfOff X)) (req ++ pairNames P) with
    | none => rfl
    | some T =>
      dsimp only
      rw [specS_f]
      have hv : ∀ c g, (vtcOwlS (spec T.tab)).f c g = ContextCalculus.SRIQD.vtc (owlES (spec T.tab)).f c g := by
        intro c g; rw [owlES_f]; exact vtcOwlS_f _ c g
      simp only [SRIQN.HF.hintPartsNLPV_eq _ _ _ _ _ _ hv,
        SRIQN.HF.splitTabV_eq _ _ _ _ _ hv,
        SRIQN.HF.lookSplitHS_f]
  · rfl

theorem classCorr_of {T : SRIQDKBTranslation} {rq : List IRI} {Dom : Type}
    {K : SRI.Interp Dom (Fin T.obj.conceptCount) (Fin T.obj.roleCount)} {I : Interp DM Dom}
    (hcl : ∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ rq → ∀ y,
      K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y)
    {S : List IRI} (hS : ∀ s ∈ S, s ∈ rq) : ClassCorr T S K I := by
  intro s hs ix hix y
  obtain ⟨hi, he⟩ := nameIx_spec hix
  have := hcl ix.val hi (he ▸ hS s hs) y
  rw [he] at this
  exact this

/-- **The model of an accepted witness hint on the Self routes.** -/
theorem wTabSCore_facts (pat : String → String → Prop) {X : Ontology} {P : List (IRI × ObjProp)}
    {req : List IRI} {hint : RawHint} {W : WTab} (hw : wTabSCore X P req hint = some W) :
    WF pat X (fun I => PairsHold P I) W := by
  unfold wTabSCore at hw
  split_ifs at hw with hX
  dsimp only at hw
  split at hw
  · cases hw
  next T hT =>
    split at hw
    next E SC PC hE hS hP =>
      split_ifs at hw with hok
      split at hw
      · cases hw
      next h hh =>
        split_ifs at hw with hp
        rw [SRIQN.HF.lookSplit_eq, cellSizeS_f, owlES_f] at hp
        simp only [Option.some.injEq] at hw
        subst hw
        have hX' := selfOff_isSROIQDKB hX
        simp only [sroiqSHOK, Bool.and_eq_true] at hok
        obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h6⟩ := hok
        have hA1 : SRIQ.IsALCHIQ (SRIQD.objPart (SRIQN.dbase (chC T (nomNames (roleOff (selfOff X)) (req ++ pairNames P)) E))) := by
          rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
          exact SROIQ.Proc.encChain_isALCHIQ _
        obtain ⟨Dom, V, hD, atom, hΘ, J, f, hJ, hn, hL, hinj, hty, hlab⟩ := SRIQN.hintPartsNL_model
          (cellSpec _) (le_refl _) ContextCalculus.SRIQD.splitCell_ok.1
          ContextCalculus.SRIQD.splitCell_ok.2 (SRIQN.isALCHIQ_encSelfD hA1) (le_refl _)
          (SRIQN.HF.hintPartsNLP_imp _ _ _ _ _ h hp)
        rw [← owlTheory_eq pat h6] at hΘ
        obtain ⟨J2, hJ2, hn2, hs2, hc2, hr2⟩ := SRIQN.encSelf_core (SROIQ.Proc.lamOK_of_lamOKB h3) hA1
          hJ hn hL
        obtain ⟨K, hK, hKn, hKs, hKc, hKr⟩ := SROIQ.Proc.chainSelf_core (SROIQ.Proc.condC_of_condB h1)
          (selfSimple_of h2) hJ2 hn2 hs2
        rw [dbase_dosnC, models_append_obj] at hK
        rw [dnoms_dosnC] at hKn
        haveI := hD
        obtain ⟨I, hI, hC, hcl, hind⟩ := downW pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hKn
        have hCC : ClassCorr T (P.map Prod.fst) K.toInterp I :=
          classCorr_of hcl fun s hs => List.mem_append_right _ hs
        have hM : OWL.Model X I := (model_selfOff hX I).2
          ⟨(model_roleOff hX' I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩,
            (sat_selfCls hC hS).1 fun sc h => hKs sc (List.mem_append_left _ h)⟩
        have hPH : PairsHold P I := (sat_pairCls hC hCC hP).1 fun sc h => hKs sc (List.mem_append_right _ h)
        refine ⟨Dom, hD, I, f, hM, hPH, hinj, fun s x hs w => ?_, fun a x ha w => ?_,
          fun r R hr w v hwv => ?_⟩
        · obtain ⟨s', hs', hsx⟩ := List.mem_filterMap.1 hs
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hsx
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          have := hcl y.val hi (hnm ▸ List.mem_append_left _ hs') (f w)
          rw [hnm, ← hyv] at this
          exact this.symm.trans ((hKc _ _).trans ((hc2 _ _).trans (hty _ w)))
        · obtain ⟨⟨a', j⟩, hp', hax⟩ := List.mem_filterMap.1 ha
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hax
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          obtain ⟨hmem, hnmOf⟩ := nmOf_eq (req := req ++ pairNames P) hp'
          have := hind _ hmem y.val hi (hnm.trans hnmOf.symm) (f w)
          rw [← hyv] at this
          exact this.symm.trans ((hKc _ _).trans ((hc2 _ _).trans (hty _ w)))
        · obtain ⟨hb, hs, k, hk, hR⟩ := mem_propsOf hr
          have hsim : SROIQ.SimpleC (ContextCalculus.SRIQD.objPart (dbase (dosnC T
              (nomNames (roleOff (selfOff X)) (req ++ pairNames P)) E))) R :=
            selfSimple_of (SC := [.selfL R []]) hs R [] List.mem_cons_self
          exact ((hC r hb k hk R hR (f w) (f v)).symm.trans (hKr R _ _ hsim)).trans
            ((hr2 R _ _ fun he => hwv (hinj he)).trans (hlab R w v))
    next => cases hw

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.wTabSCore_facts
