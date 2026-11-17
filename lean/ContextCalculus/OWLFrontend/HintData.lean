import ContextCalculus.OWLFrontend.HintRoles

/-!
# The data values of the witness model (stage H5, item 1)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 13. A hint may give the data star
of a core element (`dstar` lines); the check then tests that star and no
other. The model of an accepted hint keeps these stars
(`SRIQN.hintPartsP_modelD`), and the translation reads data properties
through the value bijection of the data theory
(`translateSRIQDKB_mapsRD`). So the data values of a core element are
determined up to the choice of one value per entry:

* `WDat pat W I f` (the data facts): a value `val w i` for every entry `i`
  of the given star `S` of a core element `w`, with
  - `val w i ≠ val w j` for different entries `i ≠ j` of one element;
  - `val w i` lies in the data range of atom `j` iff `j` is in the entry's
    atom set (the value type of the entry is exactly the listed one);
  - `I.dprop P (f w) x` iff `P` is the IRI of a data property `u` and `x`
    is `val w i` for an entry `i` whose label holds `u`.
  In words: the `P`-values of `f w` are exactly one value per listed entry
  whose label holds `P`, in the cell the entry names, distinct per element.
* `WDF pat X W`: the role facts of `WRF` and the data facts for one model.
* `wTabCore_dfacts`, `wCoreA_dfacts`, `wTabA_dfacts`: on the chain route
  (`W.chainR`); `wTabA_dfacts` for an ontology without datatype
  definitions (the unfolding changes the extension of the defined
  datatype, so the atoms are not read on the final model there).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SRIQN (dbase dnoms NomAt)
open ContextCalculus.SROIQ (Gen)
open ContextCalculus.SROIQ.Proc (LPath)

/-! ## Chain elimination keeps the data -/

theorem chainDownD {n m p q : Nat} {Dom V : Type}
    {X : SRIQN.DOntology (Fin n) (Fin m) (Fin p) (Fin q)} (hC : SROIQ.Proc.CondCD X)
    {atom : Fin q → V → Prop}
    {J : ContextCalculus.SRIQD.DInterp Dom V (Fin (n + SROIQ.Proc.kCD X)) (Fin m) (Fin p)}
    (hJ : ContextCalculus.SRIQD.models atom J (dbase (SROIQ.Proc.encChainDN X)))
    (hn : ∀ a ∈ dnoms (SROIQ.Proc.encChainDN X), NomAt J.toInterp a) :
    ∃ J' : ContextCalculus.SRIQD.DInterp Dom V (Fin n) (Fin m) (Fin p),
      ContextCalculus.SRIQD.models atom J' (dbase X) ∧ (∀ a ∈ dnoms X, NomAt J'.toInterp a) ∧
      (∀ a y, J'.c a y ↔ J.c (Fin.castAdd _ a) y) ∧
      (∀ R x y, SROIQ.SimpleC (ContextCalculus.SRIQD.objPart (dbase X)) R →
        (J'.rt R x y ↔ J.rt R x y)) ∧
      (∀ R x y, J'.rt R x y ↔
        ∃ w, Gen (ContextCalculus.SRIQD.objPart (dbase X)) w R ∧ J.toInterp.path w x y) ∧
      J'.d = J.d := by
  rw [SROIQ.Proc.dbase_encChainDN] at hJ
  have hJo : SRIQ.models J.toInterp (SROIQ.Proc.encChain (ContextCalculus.SRIQD.objPart (dbase X))) := by
    have := (ContextCalculus.SRIQD.models_iff.1 hJ).1
    rwa [SROIQ.Proc.objPart_encChainQD] at this
  refine ⟨_, SROIQ.Proc.models_encChainQD_down hC hJ, fun a ha => ?_, fun a y => Iff.rfl,
    fun R x y hs => SROIQ.Proc.downC_rt_simple hJo hs x y, fun R x y => SROIQ.Proc.downC_rt R x y,
    rfl⟩
  exact hn (Fin.castAdd _ a) (by rw [SROIQ.Proc.dnoms_encChainDN]; exact List.mem_map_of_mem ha)

/-! ## The translation down, with the data -/

variable {O : Ontology} {requested : List IRI} {T : SRIQDKBTranslation}

/-- **Down, with the data.** `downW` with the data properties of the
model read through the value bijection, and the atoms on the model. -/
theorem downWD (pat : String → String → Prop) (h : translateSHOIQD O requested = some T)
    {Dom V : Type} [Nonempty Dom] {atom : Fin T.tab.length → V → Prop}
    (hΘ : owlTheory pat (spec T.tab) V atom)
    (K : ContextCalculus.SRIQD.DInterp Dom V (Fin T.obj.conceptCount) (Fin T.obj.roleCount)
      (Fin T.dps.length))
    (hK : ContextCalculus.SRIQD.models atom K (dbase (dosn T (nomNames O requested))))
    (hn : ∀ a ∈ dnoms (dosn T (nomNames O requested)), NomAt K.toInterp a) :
    ∃ I : Interp (owl2MapP pat) Dom, OWL.Model O I ∧ RoleCorr T K.toInterp I ∧
      (∀ (i : Nat) (hi : i < T.obj.named.length), T.obj.named[i] ∈ requested → ∀ y,
        K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ I.cls T.obj.named[i] y) ∧
      (∀ a ∈ O.individualNames, ∀ (i : Nat) (hi : i < T.obj.named.length),
        T.obj.named[i] = nmOf O requested a → ∀ y,
        K.c ⟨i, Nat.lt_of_lt_of_le hi T.obj.hnamed⟩ y ↔ y = I.ind (.named a)) ∧
      ∃ eqv : V ≃ Val, (∀ j v, atom j v ↔ (spec T.tab j).ext (owl2MapP pat) I.dtype (eqv v)) ∧
        ∀ (name : IRI) (y : Dom) (w : Val), I.dprop name y w ↔
          ∃ u : Fin T.dps.length, T.dps[u] = name ∧ K.d u y (eqv.symm w) := by
  obtain ⟨hO, hT⟩ := translateSHOIQD_spec h
  obtain ⟨x0⟩ := (inferInstance : Nonempty Dom)
  rw [dbase_dosn] at hK
  obtain ⟨I0, hI0, hc, hr, eqv, hat, hdp⟩ := (translateSRIQDKB_mapsRD pat hT).2 Dom V atom hΘ K
    (fun _ => x0) hK (by rw [translateSHOIQD_abox h]; intro _ h'; simp at h')
  have hcs : ∀ s ∈ requested ++ nomNames O requested, ∀ (ix : Fin T.obj.conceptCount),
      nameIx T.obj s = some ix → ∀ y, I0.cls s y ↔ K.c ix y := by
    intro s hs ix hix y
    obtain ⟨hi, he⟩ := nameIx_spec hix
    have := hc ix.val hi (he ▸ hs) y
    rw [he] at this
    exact this
  have hmem : ∀ a ∈ O.individualNames, nmOf O requested a ∈ requested ++ nomNames O requested :=
    fun a ha => List.mem_append_right _ (List.mem_map_of_mem ha)
  have hsing : ∀ a ∈ O.individualNames, ∃ x, ∀ y, I0.cls (nmOf O requested a) y ↔ y = x := by
    intro a ha
    obtain ⟨ix, hix⟩ := nameIx_some (named_obj h (hmem a ha))
    obtain ⟨z, hz⟩ := hn ix (nomD_mem h ha hix)
    exact ⟨z, fun y => (hcs _ (hmem a ha) ix hix y).trans (hz y)⟩
  obtain ⟨hM, hcls⟩ := nomOntD_down hO requested hI0 hsing
  refine ⟨downI O requested I0, hM, fun r hb k hk R hfin x y => ?_, fun i hi hs y => ?_,
    fun a ha i hi he y => ?_, eqv, hat, hdp⟩
  · have := hr r hb k hk R hfin x y
    cases r <;> exact this.symm
  · rw [hcls]
    exact (hc i hi (List.mem_append_left _ hs) y).symm
  · have h1 := hc i hi (by rw [he]; exact hmem a ha) y
    rw [he] at h1
    rw [← h1]
    exact downI_nom (hsing a ha) y

/-! ## The data facts -/

/-- The given star at position `i` of the table of stars (as `HF.givenStar`). -/
def starAt {p q : Nat} (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))))
    (i : Nat) : Option (List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))) :=
  match (stars[i]?).getD none with
  | some l => if l.all Option.isSome then some (l.filterMap id) else none
  | none => none

theorem givenStar_eq {n m p q : Nat} (h : SRIQN.HF.HintS n m)
    (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q)))))) (b : Fin h.k) :
    SRIQN.HF.givenStar h stars b = starAt stars b.val := rfl

/-- The given data star of a core element. -/
def WTab.dst (W : WTab) (w : Fin W.k) : Option (List (ContextCalculus.SRIQD.DNbr (Fin W.p) (Fin W.q))) :=
  starAt W.dsA w.val

/-- The IRI of a data property index. -/
def WTab.dpn (W : WTab) (u : Fin W.p) : IRI := W.dpsA[u.val]?.getD ""

/-- The data range of an atom. -/
def WTab.dsp (W : WTab) (j : Fin W.q) : DataRange := W.dspA[j.val]?.getD (.datatype "")

/-- **The data facts of a witness model.** -/
def WDat (pat : String → String → Prop) (W : WTab) {Dom : Type} (I : Interp (owl2MapP pat) Dom)
    (f : Fin W.k → Dom) : Prop :=
  ∃ val : Fin W.k → Nat → Val, ∀ w S, W.dst w = some S →
    (∀ i j, i < S.length → j < S.length → val w i = val w j → i = j) ∧
    (∀ i (hi : i < S.length) (j : Fin W.q),
      (W.dsp j).ext (owl2MapP pat) I.dtype (val w i) ↔ j ∈ (S[i]).2) ∧
    (∀ name x, I.dprop name (f w) x ↔
      ∃ u : Fin W.p, W.dpn u = name ∧ ∃ i, ∃ hi : i < S.length, u ∈ (S[i]).1 ∧ x = val w i)

/-- **The role and data facts of a witness model**, for one model. -/
def WDF (pat : String → String → Prop) (X : Ontology) (W : WTab) : Prop :=
  W.chainR = true →
  ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
    OWL.Model X I ∧ Function.Injective f ∧
    (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
    (∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) ∧
    (∀ r R, (r, R) ∈ W.props → ∀ w v, (I.prop r (f w) (f v) ↔ R ∈ W.lab w v)) ∧
    (∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2) ∧
    (∀ r R, (r, R) ∈ W.rprops → ∀ w v word, Gen W.ob word R → LPath W.lab word w v →
      I.prop r (f w) (f v)) ∧
    (W.flat = true → ∀ r R, (r, R) ∈ W.rprops → ∀ w v, I.prop r (f w) (f v) →
      ∃ word, Gen W.ob word R ∧ LPath W.lab word w v) ∧
    (W.flat = true → ∀ y, ∃ w, f w = y) ∧
    WDat pat W I f

/-- From the labelled values of the data model to the data facts. -/
theorem wdat_of {p q k : Nat} {V Dom : Type} {atom : Fin q → V → Prop} (eqv : V ≃ Val)
    (dpn : Fin p → IRI) (dsp : Fin q → DataRange) (dtype : IRI → Val → Prop)
    (dprop : IRI → Dom → Val → Prop) (d : Fin p → Dom → V → Prop) (f : Fin k → Dom)
    (gs : Fin k → Option (List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))
    (pat : String → String → Prop)
    (hat : ∀ j v, atom j v ↔ (dsp j).ext (owl2MapP pat) dtype (eqv v))
    (hdp : ∀ name y w, dprop name y w ↔ ∃ u, dpn u = name ∧ d u y (eqv.symm w))
    (hdat : ∀ b S, gs b = some S → ∃ P : List (Finset (Fin p) × V),
      P.map (fun x => (x.1, ContextCalculus.SRIQD.vt atom x.2)) = S ∧ (P.map Prod.snd).Nodup ∧
      ∀ u v, d u (f b) v ↔ ∃ x ∈ P, u ∈ x.1 ∧ x.2 = v) :
    ∃ val : Fin k → Nat → Val, ∀ w S, gs w = some S →
      (∀ i j, i < S.length → j < S.length → val w i = val w j → i = j) ∧
      (∀ i (hi : i < S.length) (j : Fin q),
        (dsp j).ext (owl2MapP pat) dtype (val w i) ↔ j ∈ (S[i]).2) ∧
      (∀ name x, dprop name (f w) x ↔
        ∃ u : Fin p, dpn u = name ∧ ∃ i, ∃ hi : i < S.length, u ∈ (S[i]).1 ∧ x = val w i) := by
  classical
  have hP : ∀ b, ∃ P : List (Finset (Fin p) × V), ∀ S, gs b = some S →
      P.map (fun x => (x.1, ContextCalculus.SRIQD.vt atom x.2)) = S ∧ (P.map Prod.snd).Nodup ∧
      ∀ u v, d u (f b) v ↔ ∃ x ∈ P, u ∈ x.1 ∧ x.2 = v := by
    intro b
    cases hb : gs b with
    | none => exact ⟨[], fun S h => by cases h⟩
    | some S =>
      obtain ⟨P, h1, h2, h3⟩ := hdat b S hb
      exact ⟨P, fun S' h => by cases h; exact ⟨h1, h2, h3⟩⟩
  choose PP hPP using hP
  refine ⟨fun w i => ((PP w)[i]?.map fun x => eqv x.2).getD (.num 0), fun w S hS => ?_⟩
  obtain ⟨hmap, hnd, hd⟩ := hPP w S hS
  have hlen : (PP w).length = S.length := by rw [← hmap, List.length_map]
  have hval : ∀ i (hi : i < S.length), ((PP w)[i]?.map fun x => eqv x.2).getD (.num 0) =
      eqv ((PP w)[i]'(hlen ▸ hi)).2 := by
    intro i hi
    rw [List.getElem?_eq_getElem (hlen ▸ hi)]
    rfl
  have hSi : ∀ i (hi : i < S.length), S[i] = (((PP w)[i]'(hlen ▸ hi)).1,
      ContextCalculus.SRIQD.vt atom ((PP w)[i]'(hlen ▸ hi)).2) := by
    intro i hi
    simp only [← hmap, List.getElem_map]
  refine ⟨fun i j hi hj he => ?_, fun i hi j => ?_, fun name x => ?_⟩
  · beta_reduce at he
    rw [hval i hi, hval j hj] at he
    have he' := eqv.injective he
    have hnd' := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j)
      (hi := by rw [List.length_map]; exact hlen ▸ hi) (hj := by rw [List.length_map]; exact hlen ▸ hj))
    exact hnd'.1 (by simpa using he')
  · beta_reduce
    rw [hval i hi, hSi i hi, ← hat]
    exact ContextCalculus.SRIQD.mem_vt.symm
  · beta_reduce
    rw [hdp]
    constructor
    · rintro ⟨u, hu, hdu⟩
      obtain ⟨e, he, hue, hev⟩ := (hd u _).1 hdu
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      refine ⟨u, hu, i, hlen ▸ hi, ?_, ?_⟩
      · rw [hSi i (hlen ▸ hi)]; exact hue
      · rw [hval i (hlen ▸ hi)]
        rw [hev]; simp
    · rintro ⟨u, hu, i, hi, hui, rfl⟩
      refine ⟨u, hu, (hd u _).2 ⟨(PP w)[i]'(hlen ▸ hi), List.getElem_mem _, ?_, ?_⟩⟩
      · rw [hSi i hi] at hui; exact hui
      · rw [hval i hi]; simp

/-- **The role and data facts of the chain route.** -/
theorem wTabCore_dfacts (pat : String → String → Prop) {X : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabCore X req hint = some W) : WDF pat X W := by
  intro _
  unfold wTabCore at hw
  split_ifs at hw with hX
  split at hw
  · cases hw
  next T hT =>
    split at hw
    · cases hw
    next E hE =>
      dsimp only at hw
      split_ifs at hw with hok
      split at hw
      · cases hw
      next h hh =>
        split_ifs at hw with hp
        rw [SRIQN.HF.lookSplit_eq, cellSizeS_f, owlES_f] at hp
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [sroiqHOK, Bool.and_eq_true] at hok
        obtain ⟨⟨-, h1⟩, h3⟩ := hok
        obtain ⟨Dom, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur, hdat⟩ :=
          SRIQN.hintPartsP_modelD (cellSpec _) (le_refl _) ContextCalculus.SRIQD.splitCell_ok.1
          ContextCalculus.SRIQD.splitCell_ok.2 (SROIQ.Proc.isSHIQD_encChainDN _) (le_refl _) hp
        have hAs : SRI.IsALCHI (SRIQ.sriPart (ContextCalculus.SRIQD.objPart (dbase (encC T (nomNames (roleOff X) req) E)))) := by
          refine SRIQ.isALCHI_sriPart ?_
          rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
          exact SROIQ.Proc.encChain_isALCHIQ _
        rw [← owlTheory_eq pat h3] at hΘ
        obtain ⟨K, hK, hKn, hKc, hKr, hKg, hKd⟩ := chainDownD (SROIQ.Proc.condC_of_condB h1) hJ hn
        rw [dbase_dosnC, models_append_obj] at hK
        rw [dnoms_dosnC] at hKn
        haveI := hD
        obtain ⟨I, hI, hC, hcl, hind, eqv, hat, hdp⟩ :=
          downWD pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hKn
        have hM : OWL.Model X I := (model_roleOff hX I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩
        have hlab' := hlab hAs
        refine ⟨Dom, hD, I, f, hM, hinj, fun s x hs w => ?_, fun a x ha w => ?_, fun r R hr w v => ?_,
          fun b c R => adj_spec h b c R, fun r R hr w v word hg hpth => ?_,
          fun hfl r R hr w v hrv => ?_, fun hfl => hsur (List.isEmpty_iff.1 hfl), ?_⟩
        · obtain ⟨s', hs', hsx⟩ := List.mem_filterMap.1 hs
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hsx
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          rw [← hty, ← hKc, hyv]
          have := hcl y.val hi (hnm ▸ hs') (f w)
          rw [hnm] at this
          exact this.symm
        · obtain ⟨⟨a', j⟩, hp', hax⟩ := List.mem_filterMap.1 ha
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hax
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOfA_spec hy
          obtain ⟨hmem, hnmOf⟩ := nmOf_eq (req := req) hp'
          rw [← hty, ← hKc, hyv]
          exact (hind _ hmem y.val hi (hnm.trans hnmOf.symm) (f w)).symm
        · obtain ⟨hb, hs, k, hk, hR⟩ := mem_propsOf hr
          have hsim : SROIQ.SimpleC (ContextCalculus.SRIQD.objPart (dbase (dosnC T (nomNames (roleOff X) req) E))) R :=
            selfSimple_of (SC := [.selfL R []]) hs R [] List.mem_cons_self
          exact ((hC r hb k hk R hR (f w) (f v)).symm.trans (hKr R _ _ hsim)).trans (hlab' R w v)
        · obtain ⟨hb, k, hk, hR⟩ := mem_rpropsOf hr
          refine (hC r hb k hk R hR (f w) (f v)).1 ((hKg R _ _).2 ⟨word, hg, ?_⟩)
          exact path_of_lpath J.toInterp f _ hlab' word w v hpth
        · obtain ⟨hb, k, hk, hR⟩ := mem_rpropsOf hr
          obtain ⟨word, hg, hpth⟩ := (hKg R _ _).1 ((hC r hb k hk R hR (f w) (f v)).2 hrv)
          exact ⟨word, hg, lpath_of_path J.toInterp f _ hlab' (hsur (List.isEmpty_iff.1 hfl)) hinj
            word w v hpth⟩
        · -- the data facts
          have hdpn : ∀ u : Fin T.dps.length, (T.dps.toArray[u.val]?.getD "") = T.dps[u] := by
            intro u; simp
          have hdsp : ∀ j : Fin T.tab.length,
              ((T.tab.map (·.R)).toArray[j.val]?.getD (.datatype "")) = spec T.tab j := by
            intro j; simp [spec]
          refine wdat_of (atom := atom) eqv (fun u : Fin T.dps.length => T.dps.toArray[u.val]?.getD "")
            (fun j : Fin T.tab.length => (T.tab.map (·.R)).toArray[j.val]?.getD (.datatype ""))
            I.dtype I.dprop K.d f _ pat (fun j v => ?_) (fun name y x => ?_) (fun b S hS => ?_)
          · beta_reduce
            rw [hdsp]; exact hat j v
          · beta_reduce
            simp only [hdpn]; exact hdp name y x
          · rw [hKd]
            exact hdat b S hS

/-- **The role and data facts of the route choice.** -/
theorem wCoreA_dfacts (pat : String → String → Prop) {X : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wCoreA X req hint = some W) : WDF pat X W := by
  unfold wCoreA at hw
  split_ifs at hw
  · intro hc; rw [wTabSCore_chainR hw] at hc; cases hc
  · split at hw
    next W' hW' =>
      cases hw
      exact wTabCore_dfacts pat hW'
    next =>
      intro hc; rw [wTabSCore_chainR hw] at hc; cases hc

/-- **The role and data facts on the hint route**, for an ontology without
datatype definitions. -/
theorem wTabA_dfacts (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W)
    (hdt : (splitDef O.axioms).isNone = true) : WDF pat O W := by
  intro hcr
  unfold wTabA at hw
  have hwd : wDT O = some O := by
    unfold wDT
    rw [if_neg (by simpa using hdt)]
  rw [hwd] at hw
  dsimp only at hw
  split_ifs at hw with hk2
  rw [Bool.and_eq_true] at hk2
  obtain ⟨hk, hkX⟩ := hk2
  obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, hrole, hadj, hpos, hneg, hsur, hdat⟩ :=
    wCoreA_dfacts pat hW0 hcr
  haveI := hD
  set g := anonG [] (duOff (edgeP O))
  have hM1 : OWL.Model O (J.indMap g) := model_of_edgeP ((model_duOff _ _).1 (model_of_anonOff' hk hJ))
  have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
  have hgprop : (J.indMap g).prop = J.prop := by cases J; rfl
  have hgdp : (J.indMap g).dprop = J.dprop := by cases J; rfl
  have hgdt : (J.indMap g).dtype = J.dtype := by cases J; rfl
  refine ⟨Dom, hD, J.indMap g, f, hM1, hinj, fun s x hs w => ?_, fun a x hax w => ?_,
    fun r R hr w v => by rw [hgprop]; exact hrole r R hr w v, hadj,
    fun r R hr w v word hg hpth => by rw [hgprop]; exact hpos r R hr w v word hg hpth,
    fun hfl r R hr w v h => hneg hfl r R hr w v (by rw [← hgprop]; exact h), hsur, ?_⟩
  · rw [hgcls]; exact hcls s x hs w
  · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
    have ha : a ∈ (duOff (edgeP O)).namedIndividuals := by
      simpa [Std.HashSet.contains_ofList] using hc
    have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
      simp only [List.nil_append]; exact ha))
    have : (J.indMap g).ind (.named a) = J.ind (.named a) := by
      cases J; simp only [Interp.indMap, hfix]
    rw [this]
    exact hind a x hax w
  · obtain ⟨val, hv⟩ := hdat
    refine ⟨val, fun w S hS => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hv w S hS
    refine ⟨h1, fun i hi j => ?_, fun name x => ?_⟩
    · rw [hgdt]; exact h2 i hi j
    · rw [hgdp]; exact h3 name x

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.chainDownD
#print axioms ContextCalculus.OWLFrontend.downWD
#print axioms ContextCalculus.OWLFrontend.wdat_of
#print axioms ContextCalculus.OWLFrontend.wTabCore_dfacts
#print axioms ContextCalculus.OWLFrontend.wCoreA_dfacts
#print axioms ContextCalculus.OWLFrontend.wTabA_dfacts
