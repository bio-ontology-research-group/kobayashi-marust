import ContextCalculus.OWLFrontend.HintWitnessA
import ContextCalculus.SRIQN.HintModelFlat
import ContextCalculus.SROIQ.CoreReach

/-!
# Role facts of the witness model (stage H4, item 1)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 12. On the chain route the model
of an accepted witness hint gives every named property `r` (role term `R`
in the normal form) the relation "some path spells a word of `R`'s
language" over the model of the chain encoding (`downC_rt`). Over the
core this is decided by the product of the label graph with the role's
automaton (`SROIQ.Proc.succOf`):

* `WRF pat X W` (the role facts): with `W.chainR`, a model of `X` with the
  core inside it in which
  - a path of the label graph along a word of `R` from `w` to `v` gives
    `r(f w, f v)` (every hint);
  - for a flat hint (`W.flat`: no `kid` lines), `r(f w, f v)` gives such a
    path, and every element of the model is a core element;
  - for a simple property (`W.props`), `r(f w, f v)` iff `R ∈ lab w v`, for
    every pair of core elements, the same element included.
* `wTabCore_rfacts`, `wCoreA_rfacts`, `wTabA_rfacts`: the facts for the
  chain route, the route choice and every preparation step. On the Self
  and `ObjectHasSelf` routes `W.chainR` is false and nothing is claimed.

Hints with `kid` lines: the forest of `SRIQN/Forest.lean` gives a tree node
an edge to every core element its record's chosen support lists, and the
support is picked by choice, so a path through tree nodes can join two
core elements that the hint's labels do not join. Only the positive
direction (a path of the labels gives the edge) holds for them; the
negative direction needs a flat hint (or simple properties).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.SRIQN (dbase dnoms NomAt)
open ContextCalculus.SROIQ (Gen)
open ContextCalculus.SROIQ.Proc (LPath)

/-! ## Chain elimination, with every role -/

theorem chainDownR {n m p q : Nat} {Dom V : Type}
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
      ∀ R x y, J'.rt R x y ↔
        ∃ w, Gen (ContextCalculus.SRIQD.objPart (dbase X)) w R ∧ J.toInterp.path w x y := by
  rw [SROIQ.Proc.dbase_encChainDN] at hJ
  have hJo : SRIQ.models J.toInterp (SROIQ.Proc.encChain (ContextCalculus.SRIQD.objPart (dbase X))) := by
    have := (ContextCalculus.SRIQD.models_iff.1 hJ).1
    rwa [SROIQ.Proc.objPart_encChainQD] at this
  refine ⟨_, SROIQ.Proc.models_encChainQD_down hC hJ, fun a ha => ?_, fun a y => Iff.rfl,
    fun R x y hs => SROIQ.Proc.downC_rt_simple hJo hs x y, fun R x y => SROIQ.Proc.downC_rt R x y⟩
  exact hn (Fin.castAdd _ a) (by rw [SROIQ.Proc.dnoms_encChainDN]; exact List.mem_map_of_mem ha)

/-! ## Paths over the core -/

section Paths

variable {Dom C : Type} {M K : Nat}

theorem path_of_lpath (J : SRI.Interp Dom C (Fin M)) (f : Fin K → Dom)
    (lab : Fin K → Fin K → Finset (SRI.RoleT (Fin M)))
    (hlab : ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ lab b c) :
    ∀ (w : List (SRI.RoleT (Fin M))) (b c : Fin K), LPath lab w b c → J.path w (f b) (f c)
  | [], b, c, h => by cases h; rfl
  | R :: w, b, c, ⟨z, hz, hp⟩ => ⟨f z, (hlab R b z).2 hz, path_of_lpath J f lab hlab w z c hp⟩

theorem lpath_of_path (J : SRI.Interp Dom C (Fin M)) (f : Fin K → Dom)
    (lab : Fin K → Fin K → Finset (SRI.RoleT (Fin M)))
    (hlab : ∀ R b c, J.rt R (f b) (f c) ↔ R ∈ lab b c) (hsur : ∀ y, ∃ b, f b = y)
    (hinj : Function.Injective f) :
    ∀ (w : List (SRI.RoleT (Fin M))) (b c : Fin K), J.path w (f b) (f c) → LPath lab w b c
  | [], b, c, h => hinj h
  | R :: w, b, c, ⟨y, hy, hp⟩ => by
    obtain ⟨z, rfl⟩ := hsur y
    exact ⟨z, (hlab R b z).1 hy, lpath_of_path J f lab hlab hsur hinj w z c hp⟩

end Paths

/-! ## The role facts -/

/-- **The role facts of a witness model.** -/
def WRF (pat : String → String → Prop) (X : Ontology) (W : WTab) : Prop :=
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
    (W.flat = true → ∀ y, ∃ w, f w = y)

theorem adj_spec {n m : Nat} (h : SRIQN.HF.HintS n m) (b c : Fin h.k) (R : SRI.RoleT (Fin m)) :
    R ∈ h.toN.lab b c ↔ ∃ e ∈ ContextCalculus.SRIQ.Fast.getL h.adj b.val, e.1 = c ∧ R ∈ e.2 := by
  rw [← SRIQN.HF.labOf_adj h b c, SRIQN.HF.mem_labOf]

/-- **The role facts of the chain route.** -/
theorem wTabCore_rfacts (pat : String → String → Prop) {X : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabCore X req hint = some W) : WRF pat X W := by
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
        simp only [Option.some.injEq] at hw
        subst hw
        simp only [sroiqHOK, Bool.and_eq_true] at hok
        obtain ⟨⟨-, h1⟩, h3⟩ := hok
        obtain ⟨Dom, V, hD, atom, hΘ, J, f, hJ, hn, hinj, hty, hlab, hsur⟩ := SRIQN.hintPartsP_model'
          (cellSpec _) (le_refl _) ContextCalculus.SRIQD.splitCell_ok.1
          ContextCalculus.SRIQD.splitCell_ok.2 (SROIQ.Proc.isSHIQD_encChainDN _) (le_refl _) hp
        have hAs : SRI.IsALCHI (SRIQ.sriPart (ContextCalculus.SRIQD.objPart (dbase (encC T (nomNames (roleOff X) req) E)))) := by
          refine SRIQ.isALCHI_sriPart ?_
          rw [SROIQ.Proc.dbase_encChainDN, SROIQ.Proc.objPart_encChainQD]
          exact SROIQ.Proc.encChain_isALCHIQ _
        rw [← owlTheory_eq pat h3] at hΘ
        obtain ⟨K, hK, hKn, hKc, hKr, hKg⟩ := chainDownR (SROIQ.Proc.condC_of_condB h1) hJ hn
        rw [dbase_dosnC, models_append_obj] at hK
        rw [dnoms_dosnC] at hKn
        haveI := hD
        obtain ⟨I, hI, hC, hcl, hind⟩ := downW pat hT hΘ K (by rw [dbase_dosn]; exact hK.1) hKn
        have hM : OWL.Model X I := (model_roleOff hX I).2 ⟨hI, (sat_roleCls hC hE).1 hK.2⟩
        have hlab' := hlab hAs
        refine ⟨Dom, hD, I, f, hM, hinj, fun s x hs w => ?_, fun a x ha w => ?_, fun r R hr w v => ?_,
          fun b c R => adj_spec h b c R, fun r R hr w v word hg hpth => ?_,
          fun hfl r R hr w v hrv => ?_, fun hfl => hsur (List.isEmpty_iff.1 hfl)⟩
        · obtain ⟨s', hs', hsx⟩ := List.mem_filterMap.1 hs
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hsx
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOf_spec hy
          rw [← hty, ← hKc, hyv]
          have := hcl y.val hi (hnm ▸ hs') (f w)
          rw [hnm] at this
          exact this.symm
        · obtain ⟨⟨a', j⟩, hp', hax⟩ := List.mem_filterMap.1 ha
          obtain ⟨y, hy, hyx⟩ := Option.map_eq_some_iff.1 hax
          simp only [Prod.mk.injEq] at hyx
          obtain ⟨rfl, rfl⟩ := hyx
          obtain ⟨hi, hnm, hyv⟩ := ixOf_spec hy
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

theorem wTabSCore_chainR {X : Ontology} {P : List (IRI × ObjProp)} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabSCore X P req hint = some W) : W.chainR = false := by
  unfold wTabSCore at hw
  split_ifs at hw
  dsimp only at hw
  split at hw
  · cases hw
  next T hT =>
    split at hw
    next E SC PC hE hS hP =>
      split_ifs at hw
      split at hw
      · cases hw
      next h hh =>
        split_ifs at hw
        simp only [Option.some.injEq] at hw
        subst hw
        rfl
    next => cases hw

/-- **The role facts of the route choice.** -/
theorem wCoreA_rfacts (pat : String → String → Prop) {X : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wCoreA X req hint = some W) : WRF pat X W := by
  unfold wCoreA at hw
  split_ifs at hw
  · intro hc; rw [wTabSCore_chainR hw] at hc; cases hc
  · split at hw
    next W' hW' =>
      cases hw
      exact wTabCore_rfacts pat hW'
    next =>
      intro hc; rw [wTabSCore_chainR hw] at hc; cases hc

/-- **The role facts on every route of the hint route.** -/
theorem wTabA_rfacts (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) : WRF pat O W := by
  intro hcr
  unfold wTabA at hw
  split at hw
  · cases hw
  next O1 hO1 =>
    dsimp only at hw
    split_ifs at hw with hk2
    rw [Bool.and_eq_true] at hk2
    obtain ⟨hk, hkX⟩ := hk2
    obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, hrole, hadj, hpos, hneg, hsur⟩ :=
      wCoreA_rfacts pat hW0 hcr
    haveI := hD
    set g := anonG [] (duOff (edgeP O1))
    have hM1 : OWL.Model O1 (J.indMap g) := model_of_edgeP ((model_duOff _ _).1 (model_of_anonOff' hk hJ))
    have hM : ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = (J.indMap g).cls ∧
        J'.ind = (J.indMap g).ind ∧ J'.prop = (J.indMap g).prop := by
      unfold wDT at hO1
      split_ifs at hO1
      · exact model_of_dtLoop hO1 _ hM1
      · cases hO1; exact ⟨_, hM1, rfl, rfl, rfl⟩
    obtain ⟨I, hI, hIc, hIi, hIp⟩ := hM
    have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
    have hgprop : (J.indMap g).prop = J.prop := by cases J; rfl
    have hp : I.prop = J.prop := hIp.trans hgprop
    refine ⟨Dom, hD, I, f, hI, hinj, fun s x hs w => ?_, fun a x hax w => ?_,
      fun r R hr w v => by rw [hp]; exact hrole r R hr w v, hadj,
      fun r R hr w v word hg hpth => by rw [hp]; exact hpos r R hr w v word hg hpth,
      fun hfl r R hr w v h => hneg hfl r R hr w v (by rw [← hp]; exact h), hsur⟩
    · rw [hIc, hgcls]; exact hcls s x hs w
    · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
      have ha : a ∈ (duOff (edgeP O1)).namedIndividuals := by
        simpa [Std.HashSet.contains_ofList] using hc
      have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
        simp only [List.nil_append]; exact ha))
      have : I.ind (.named a) = J.ind (.named a) := by
        rw [hIi]; cases J; simp only [Interp.indMap, hfix]
      rw [this]
      exact hind a x hax w

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.chainDownR
#print axioms ContextCalculus.OWLFrontend.wTabCore_rfacts
#print axioms ContextCalculus.OWLFrontend.wTabA_rfacts
