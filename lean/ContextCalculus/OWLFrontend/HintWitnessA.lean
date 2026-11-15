import ContextCalculus.OWLFrontend.HintWitnessS
import ContextCalculus.OWLFrontend.KeyRules
import ContextCalculus.OWLFrontend.DatatypeDef

/-!
# The witness row on every route of `sroiq-hint` (stage H2, item 1)

`wTabA O req hint` is the witness row on the inputs the hint route takes
(`hintP`): datatype definitions unfolded, the strengthening of asymmetric
and disjoint properties, disjoint unions rewritten, anonymous individuals
renamed, then the route with `ObjectHasSelf` (on `hsOff`), the chain
route, or the Self route. `wTabR R req hint` adds keys and DL-safe rules
(`rulesOntoK`: keys as rules, rules grounded over the named individuals).
Each preparation step keeps the classes and the named individuals of a
model (`model_of_dtLoop`, `modelR_of_encRules`, `model_hsOff_down`, the
renaming), so `wTabA_model` and `wTabR_model` give a model of the input
with the core inside it; `hintWitnessA_sound` and `hintWitnessR_sound` are
the rows for the class expressions of the requested IRIs.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes SHIQD SHOIQ
open ContextCalculus.OWL.Parse (owlThing owlNothing owlNs)

/-! ## Datatype definitions down -/

section DT

variable {pat : String → String → Prop}

theorem model_of_dtStep {O O' : Ontology} (h : dtStep O = some O') {Dom : Type}
    (J : Interp (owl2MapP pat) Dom) (hJ : OWL.Model O' J) :
    ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = J.cls ∧ J'.ind = J.ind := by
  unfold dtStep at h
  split at h
  · cases h
  next t R l hs =>
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not, List.all_eq_true] at hc
  obtain ⟨⟨⟨hk, hkind⟩, hR⟩, hl⟩ := hc
  have hmem := mem_splitDef hs
  have hkO : ∀ ax ∈ O.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  have hf3 := facet_none (pat := pat) hkind
  let J' := J.withDT (Function.update J.dtype t (J.drExt R))
  have hJJ : J'.withDT J.dtype = J := rfl
  have hf : ∀ r, (J'.withDT J.dtype).drExt (DataRange.substDT t R r) = J'.drExt r :=
    ext_substDT (fun u hu => (dtExt_upd hu _ _).symm)
      (by
        rw [dtExt_none pat hkind]
        show Function.update J.dtype t (J.drExt R) t = DataRange.ext (owl2MapP pat) J.dtype R
        rw [Function.update_self]; rfl) hf3
  refine ⟨J', fun ax hax => ?_, rfl, rfl⟩
  rw [sat_N_noKey _ (hkO ax hax) _ []]
  rcases (hmem ax).1 hax with rfl | hax'
  · intro v
    have h1 : J'.dt t v ↔ J.drExt R v := by
      show (owl2MapP pat).dtExt (Function.update J.dtype t (J.drExt R)) t v ↔ _
      rw [dtExt_none pat hkind, Function.update_self]
    have h2 : J'.drExt R = J.drExt R := by
      rw [← hf R, substDT_of_not_mem t R R hR]; rfl
    rw [h1, h2]
  · have hs := hJ _ (List.mem_map_of_mem hax')
    rw [sat_N_noKey _ (by rw [noKey_mapDR]; exact hkO ax hax) _ []] at hs
    refine (sat_mapDR J' J.dtype hf ?_ _).1 hs
    rintro u r rfl
    have hu : u ≠ t := by simpa [notDefOf] using hl _ hax'
    funext v
    exact congrFun (dtExt_upd hu _ _).symm v


theorem model_of_dtLoop : ∀ {k : Nat} {O O' : Ontology}, dtLoop k O = some O' → ∀ {Dom : Type}
    (J : Interp (owl2MapP pat) Dom), OWL.Model O' J →
    ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = J.cls ∧ J'.ind = J.ind
  | 0, O, O', h, Dom, J, hJ => by
    simp only [dtLoop] at h
    split_ifs at h
    cases h; exact ⟨J, hJ, rfl, rfl⟩
  | k + 1, O, O', h, Dom, J, hJ => by
    simp only [dtLoop] at h
    split_ifs at h
    · cases h; exact ⟨J, hJ, rfl, rfl⟩
    · obtain ⟨O1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨J1, hJ1, hc1, hi1⟩ := model_of_dtLoop h2 J hJ
      obtain ⟨J2, hJ2, hc2, hi2⟩ := model_of_dtStep h1 J1 hJ1
      exact ⟨J2, hJ2, hc2.trans hc1, hi2.trans hi1⟩

end DT

/-! ## Rules and keys down -/

section Rules

variable {DM : DatatypeMap}

theorem modelR_of_encRules [hv : Nonempty DM.Val] (bi : BuiltIns DM) {O : OntologyR}
    {O' : Ontology} (h : encRules O = some O') {Dom : Type} (J : Interp DM Dom)
    (hJ : OWL.Model O' J) : ModelR bi O J := by
  classical
  unfold encRules at h
  simp only at h
  split_ifs at h with hc
  obtain ⟨ras, hras, rfl⟩ := Option.map_eq_some_iff.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hk, -⟩ := hc
  have hk' : ∀ ax ∈ O.onto.axioms, ax.noKey = true := by
    simpa [Ontology.noKey, List.all_eq_true] using hk
  set N := O.named.eraseDups with hN
  set u := ruleU O with hu
  set h0 := ruleH O with hh0
  have hfu : u ∉ O.roleNames := freshOf_not_mem _ _
  have hu_ax : ∀ ax ∈ O.onto.axioms, u ∉ ax.objectPropertyNames := fun ax hax hm =>
    hfu (List.mem_append_left _ (List.mem_flatMap.2 ⟨ax, hax, hm⟩))
  have hu_at : ∀ ρ ∈ O.rules, ∀ a ∈ ρ.body ++ ρ.head, u ∉ a.roleNames := fun ρ hρ a ha hm =>
    hfu (List.mem_append_right _ (List.mem_flatMap.2 ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, hm⟩⟩))
  -- the instance axioms of a rule
  have hinst : ∀ ρ ∈ O.rules, ∀ g ∈ assigns N ρ.ivars.eraseDups, ∃ ax,
      instAx u h0 ρ g = some ax ∧ ax ∈ ras.flatten := by
    intro ρ hρ g hg
    obtain ⟨L, hL, hrL⟩ := mapM_some_fwd hras ρ hρ
    obtain ⟨ax, hax, hia⟩ := mapM_some_fwd hrL g hg
    exact ⟨ax, hia, List.mem_flatten.2 ⟨L, hL, hax⟩⟩
  -- a model of the encoding is a model with rules
  refine ⟨fun ax hax => ?_, fun ρ hρ σ δ hnm hbody a ha => ?_⟩
  · rw [sat_N_noKey J (hk' ax hax) _ (Ontology.namedIndividuals _)]
    exact hJ ax (List.mem_append_left _ (List.mem_append_left _ hax))
  · -- the instance of the assignment
    let f : IRI → IRI := fun v => if hv' : v ∈ ρ.ivars then (hnm v hv').choose else v
    have hf : ∀ v ∈ ρ.ivars, f v ∈ O.named ∧ σ v = J.ind (.named (f v)) := fun v hv' => by
      simp only [f, dif_pos hv']
      exact (hnm v hv').choose_spec
    obtain ⟨g, hg, hgl⟩ := mem_assigns f (N := N) (V := ρ.ivars.eraseDups) fun v hv' =>
      List.mem_eraseDups.2 (hf v (List.mem_eraseDups.1 hv')).1
    have hag : Agrees J g σ := fun v b hl => by
      have hvV := key_of_assigns hg v b hl
      rw [hgl v hvV] at hl
      cases hl
      exact (hf v (List.mem_eraseDups.1 hvV)).2
    obtain ⟨ax, hia, haxm⟩ := hinst ρ hρ g hg
    have hJax := hJ ax (List.mem_append_right _ haxm)
    unfold instAx at hia
    obtain ⟨bs, hbs, hia⟩ := Option.bind_eq_some_iff.1 hia
    obtain ⟨hs, hhs, rfl⟩ := Option.map_eq_some_iff.1 hia
    let x0 := J.ind (.named h0)
    -- `u`-edges from `x0` to the ground individuals
    have hux : ∀ b ∈ N, J.prop (.named u) x0 (J.ind (.named b)) := fun b hb =>
      hJ _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨b, hb, rfl⟩)))
    have hua : ∀ a ∈ ρ.body ++ ρ.head, ∀ t ∈ a.iargs, ∀ b, gI g t = some b →
        J.prop (.named u) x0 (J.ind (.named b)) := by
      intro a ha t ht b hb
      refine hux b ?_
      cases t with
      | var v =>
        have hvV : v ∈ ρ.ivars.eraseDups := List.mem_eraseDups.2
          (List.mem_flatMap.2 ⟨a, ha, mem_iargs_vars ht rfl⟩)
        obtain ⟨c, hc, hl⟩ := lookup_assigns hg v hvV
        simp only [gI] at hb
        rw [hl] at hb; cases hb; exact hc
      | ind i =>
        cases i with
        | named b' =>
          simp only [gI, Option.some.injEq] at hb; subst hb
          refine List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_flatMap.2
            ⟨ρ, hρ, List.mem_flatMap.2 ⟨a, ha, mem_iargs_named ht rfl⟩⟩))
        | anon _ => cases hb
    have hx0 : J.ext (.and (.oneOf [.named h0] :: bs)) x0 := by
      rw [ext_andL]
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact (ext_oneOf1 J _ _).2 rfl
      · obtain ⟨a', ha', hca⟩ := mapM_some_bwd hbs c hc
        exact (bodyCE_iff bi u δ hag (hua a' (List.mem_append_left _ ha')) hca).2 (hbody a' ha')
    have hh := hJax x0 hx0
    rw [ext_andL] at hh
    obtain ⟨c, hc, hca⟩ := mapM_some_fwd hhs a ha
    exact (headCE_iff bi u δ hag (hua a (List.mem_append_right _ ha)) hca).1 (hh c hc)


theorem modelR_of_rulesOnto [Nonempty DM.Val] (bi : BuiltIns DM) {O : OntologyR} {O' : Ontology}
    (h : rulesOnto O = some O') {Dom : Type} (J : Interp DM Dom) (hJ : OWL.Model O' J) :
    ModelR bi O J := by
  unfold rulesOnto at h
  split_ifs at h with he
  · cases h
    have hr : O.rules = [] := List.isEmpty_iff.1 he
    have hO : O = ⟨O.onto, []⟩ := by cases O; simp_all
    rw [hO]
    exact (modelR_nil bi O.onto J).2 hJ
  · exact modelR_of_encRules bi h J hJ

theorem modelR_of_rulesOntoK [Nonempty DM.Val] (bi : BuiltIns DM) {R : OntologyR} {O' : Ontology}
    (h : rulesOntoK R = some O') {Dom : Type} (J : Interp DM Dom) (hJ : OWL.Model O' J) :
    ModelR bi R J := by
  unfold rulesOntoK at h
  split_ifs at h
  · exact modelR_of_rulesOnto bi h J hJ
  · obtain ⟨R', hR', h'⟩ := Option.bind_eq_some_iff.1 h
    exact (modelR_keyOff bi hR' J).2 (modelR_of_rulesOnto bi h' J hJ)

end Rules

/-! ## The route choice -/

/-- The route with `ObjectHasSelf` when the ontology uses it, otherwise the
chain route, and the Self route when the chain route declines. -/
def wCoreA (X : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  if !(selfPairs X).isEmpty then wTabSCore (hsOff X) (selfPairs X) req hint
  else match wTabCore X req hint with
    | some W => some W
    | none => wTabSCore X [] req hint

theorem wCoreA_facts (pat : String → String → Prop) {X : Ontology} (hk : X.noKey = true)
    {req : List IRI} {hint : RawHint} {W : WTab} (hw : wCoreA X req hint = some W) :
    WF pat X (fun _ => True) W := by
  unfold wCoreA at hw
  split_ifs at hw
  · obtain ⟨Dom, hD, I, f, hM, hP, hinj, hc, hi⟩ := wTabSCore_facts pat hw
    exact ⟨Dom, hD, I, f, model_hsOff_down hk hM hP, trivial, hinj, hc, hi⟩
  · split at hw
    next W' hW' =>
      cases hw
      obtain ⟨Dom, hD, I, f, hM, hinj, hc, hi⟩ := (wTabCore_facts pat hW').model
      exact ⟨Dom, hD, I, f, hM, trivial, hinj, hc, fun a x h w => (hi a x h).2 w⟩
    next =>
      obtain ⟨Dom, hD, I, f, hM, -, hinj, hc, hi⟩ := wTabSCore_facts pat hw
      exact ⟨Dom, hD, I, f, hM, trivial, hinj, hc, hi⟩

/-- The ontology after unfolding datatype definitions (`none`: they do not unfold). -/
def wDT (O : Ontology) : Option Ontology :=
  if (splitDef O.axioms).isSome then dtLoop O.axioms.length O else some O

/-- **The witness row on every route of the hint route.** -/
def wTabA (O : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  match wDT O with
  | none => none
  | some O1 =>
    let Pre := duOff (edgeP O1)
    if Pre.noKey && (anonOff [] Pre).noKey then
      let H := Std.HashSet.ofList Pre.namedIndividuals
      (wCoreA (anonOff [] Pre) req hint).map fun W =>
        { W with inds := W.inds.filter fun p => H.contains p.1 }
    else none

theorem model_of_anonOff' {DM : DatatypeMap} {Pre : Ontology} (hk : Pre.noKey = true) {Dom : Type}
    {J : Interp DM Dom} (hJ : OWL.Model (anonOff [] Pre) J) :
    OWL.Model Pre (J.indMap (anonG [] Pre)) :=
  (model_anonOff (W := []) hk (J.indMap (anonG [] Pre))).1 (by
    rw [indMap_indMap J (anonG_inv [] _)]; exact hJ)

/-- **The model of an accepted witness hint**, on every route. -/
theorem wTabA_model (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
      OWL.Model O I ∧ Function.Injective f ∧
      (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
      (∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) := by
  unfold wTabA at hw
  split at hw
  · cases hw
  next O1 hO1 =>
    dsimp only at hw
    split_ifs at hw with hk2
    rw [Bool.and_eq_true] at hk2
    obtain ⟨hk, hkX⟩ := hk2
    obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨Dom, hD, J, f, hJ, -, hinj, hcls, hind⟩ := wCoreA_facts pat hkX hW0
    haveI := hD
    set g := anonG [] (duOff (edgeP O1))
    have hM1 : OWL.Model O1 (J.indMap g) := model_of_edgeP ((model_duOff _ _).1 (model_of_anonOff' hk hJ))
    have hM : ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = (J.indMap g).cls ∧
        J'.ind = (J.indMap g).ind := by
      unfold wDT at hO1
      split_ifs at hO1
      · exact model_of_dtLoop hO1 _ hM1
      · cases hO1; exact ⟨_, hM1, rfl, rfl⟩
    obtain ⟨I, hI, hIc, hIi⟩ := hM
    have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
    refine ⟨Dom, hD, I, f, hI, hinj, fun s x hs w => ?_, fun a x hax w => ?_⟩
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

/-! ## The rows -/

/-- **The witness row on every route**, for the class expressions of the
requested IRIs (`owl:Thing` and `owl:Nothing` as in `hintWitnessC_sound`). -/
theorem hintWitnessA_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) :
    ConsistentAt (owl2MapP pat) O ∧
    (∀ (A B : IRI) (iA iB : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → (B, iB) ∈ W.cls →
      isBuiltinCls A = false → isBuiltinCls B = false → iA ∈ W.ty w → iB ∉ W.ty w →
      ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf B)) ∧
    (∀ (A : IRI) (iA : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → isBuiltinCls A = false →
      iA ∈ W.ty w → ¬ EntailsSubCE (owl2MapP pat) O (clsOf A) (clsOf owlNothing)) ∧
    (∀ (B : IRI) (iB : Fin W.N) (w : Fin W.k), (B, iB) ∈ W.cls → isBuiltinCls B = false →
      iB ∉ W.ty w → ¬ EntailsSubCE (owl2MapP pat) O (clsOf owlThing) (clsOf B)) ∧
    (∀ (a C : IRI) (ia iC : Fin W.N) (w : Fin W.k), (a, ia) ∈ W.inds → (C, iC) ∈ W.cls →
      isBuiltinCls C = false → ia ∈ W.ty w → iC ∉ W.ty w →
      ¬ EntailsAt (owl2MapP pat) O (.classAssertion (clsOf C) (.named a))) ∧
    (∀ (a b : IRI) (ia ib : Fin W.N) (w v : Fin W.k), (a, ia) ∈ W.inds → (b, ib) ∈ W.inds →
      ia ∈ W.ty w → ib ∈ W.ty v → w ≠ v →
      ¬ EntailsAt (owl2MapP pat) O (.sameIndividual [.named a, .named b])) := by
  obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind⟩ := wTabA_model pat hw
  haveI := hD
  have hN : clsOf owlNothing = .nothing := by simp [clsOf, owlThing, owlNothing, owlNs]
  have hT : clsOf owlThing = .thing := by simp [clsOf]
  refine ⟨⟨Dom, hD, I, hM⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B iA iB w hA hB hbA hbB hiA hiB he
    rw [clsOf_of_not_builtin hbA, clsOf_of_not_builtin hbB] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro A iA w hA hbA hiA he
    rw [clsOf_of_not_builtin hbA, hN] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simp [Interp.ext] at this
  · intro B iB w hB hbB hiB he
    rw [clsOf_of_not_builtin hbB, hT] at he
    have := he Dom I hM (f w) (by simp [Interp.ext])
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro a C ia iC w ha hC hbC hia hiC he
    have h1 := he Dom I hM
    rw [clsOf_of_not_builtin hbC] at h1
    simp only [Interp.sat, Interp.ext] at h1
    rw [← (hind a ia ha w).2 hia] at h1
    exact hiC ((hcls C iC hC w).1 h1)
  · intro a b ia ib w v ha hb hia hib hwv he
    have h1 := (sat_same I _ a b).1 (he Dom I hM)
    rw [← (hind a ia ha w).2 hia, ← (hind b ib hb v).2 hib] at h1
    exact hwv (hinj h1)

/-! ## Keys and rules -/

/-- Subsumption between class expressions over an ontology with rules. -/
def EntailsSubCER (DM : DatatypeMap) (bi : BuiltIns DM) (R : OntologyR) (C D : ClassExpr) : Prop :=
  ∀ (Dom : Type) [Nonempty Dom] (I : Interp DM Dom), ModelR bi R I → ∀ x, I.ext C x → I.ext D x

/-- An axiom holds in every model of an ontology with rules. -/
def EntailsAtR (DM : DatatypeMap) (bi : BuiltIns DM) (R : OntologyR) (ax : Axiom) : Prop :=
  ∀ (Dom : Type) [Nonempty Dom] (I : Interp DM Dom), ModelR bi R I → I.sat ax.namedIndividuals ax

/-- **The witness row with keys and DL-safe rules.** -/
def wTabR (R : OntologyR) (req : List IRI) (hint : RawHint) : Option WTab :=
  (rulesOntoK R).bind fun O' => wTabA O' req hint

/-- **Soundness of the witness row with keys and rules**, for every reading
of the built-ins. -/
theorem hintWitnessR_sound (pat : String → String → Prop) (bi : BuiltIns (owl2MapP pat))
    {R : OntologyR} {req : List IRI} {hint : RawHint} {W : WTab} (hw : wTabR R req hint = some W) :
    ConsistentAtR (owl2MapP pat) bi R ∧
    (∀ (A B : IRI) (iA iB : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → (B, iB) ∈ W.cls →
      isBuiltinCls A = false → isBuiltinCls B = false → iA ∈ W.ty w → iB ∉ W.ty w →
      ¬ EntailsSubCER (owl2MapP pat) bi R (clsOf A) (clsOf B)) ∧
    (∀ (A : IRI) (iA : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → isBuiltinCls A = false →
      iA ∈ W.ty w → ¬ EntailsSubCER (owl2MapP pat) bi R (clsOf A) (clsOf owlNothing)) ∧
    (∀ (B : IRI) (iB : Fin W.N) (w : Fin W.k), (B, iB) ∈ W.cls → isBuiltinCls B = false →
      iB ∉ W.ty w → ¬ EntailsSubCER (owl2MapP pat) bi R (clsOf owlThing) (clsOf B)) ∧
    (∀ (a C : IRI) (ia iC : Fin W.N) (w : Fin W.k), (a, ia) ∈ W.inds → (C, iC) ∈ W.cls →
      isBuiltinCls C = false → ia ∈ W.ty w → iC ∉ W.ty w →
      ¬ EntailsAtR (owl2MapP pat) bi R (.classAssertion (clsOf C) (.named a))) ∧
    (∀ (a b : IRI) (ia ib : Fin W.N) (w v : Fin W.k), (a, ia) ∈ W.inds → (b, ib) ∈ W.inds →
      ia ∈ W.ty w → ib ∈ W.ty v → w ≠ v →
      ¬ EntailsAtR (owl2MapP pat) bi R (.sameIndividual [.named a, .named b])) := by
  obtain ⟨O', hO', hw'⟩ := Option.bind_eq_some_iff.1 hw
  obtain ⟨Dom, hD, I, f, hM0, hinj, hcls, hind⟩ := wTabA_model pat hw'
  haveI := hD
  have hM : ModelR bi R I := modelR_of_rulesOntoK bi hO' I hM0
  have hN : clsOf owlNothing = .nothing := by simp [clsOf, owlThing, owlNothing, owlNs]
  have hT : clsOf owlThing = .thing := by simp [clsOf]
  refine ⟨⟨Dom, hD, I, hM⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B iA iB w hA hB hbA hbB hiA hiB he
    rw [clsOf_of_not_builtin hbA, clsOf_of_not_builtin hbB] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro A iA w hA hbA hiA he
    rw [clsOf_of_not_builtin hbA, hN] at he
    have := he Dom I hM (f w) (by simp only [Interp.ext]; exact (hcls A iA hA w).2 hiA)
    simp [Interp.ext] at this
  · intro B iB w hB hbB hiB he
    rw [clsOf_of_not_builtin hbB, hT] at he
    have := he Dom I hM (f w) (by simp [Interp.ext])
    simp only [Interp.ext] at this
    exact hiB ((hcls B iB hB w).1 this)
  · intro a C ia iC w ha hC hbC hia hiC he
    have h1 := he Dom I hM
    rw [clsOf_of_not_builtin hbC] at h1
    simp only [Interp.sat, Interp.ext] at h1
    rw [← (hind a ia ha w).2 hia] at h1
    exact hiC ((hcls C iC hC w).1 h1)
  · intro a b ia ib w v ha hb hia hib hwv he
    have h1 := (sat_same I _ a b).1 (he Dom I hM)
    rw [← (hind a ia ha w).2 hia, ← (hind b ib hb v).2 hib] at h1
    exact hwv (hinj h1)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_of_dtLoop
#print axioms ContextCalculus.OWLFrontend.modelR_of_encRules
#print axioms ContextCalculus.OWLFrontend.wTabA_model
#print axioms ContextCalculus.OWLFrontend.hintWitnessA_sound
#print axioms ContextCalculus.OWLFrontend.hintWitnessR_sound
