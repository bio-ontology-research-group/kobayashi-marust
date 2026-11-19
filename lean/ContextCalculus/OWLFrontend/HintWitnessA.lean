import ContextCalculus.OWLFrontend.HintWitnessS
import ContextCalculus.OWLFrontend.KeyRules
import ContextCalculus.OWLFrontend.DatatypeDef
import ContextCalculus.SRIQN.HintModelFlat
import ContextCalculus.SROIQ.CoreReach

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
    ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = J.cls ∧ J'.ind = J.ind ∧
      J'.prop = J.prop := by
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
  refine ⟨J', fun ax hax => ?_, rfl, rfl, rfl⟩
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
    ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = J.cls ∧ J'.ind = J.ind ∧
      J'.prop = J.prop
  | 0, O, O', h, Dom, J, hJ => by
    simp only [dtLoop] at h
    split_ifs at h
    cases h; exact ⟨J, hJ, rfl, rfl, rfl⟩
  | k + 1, O, O', h, Dom, J, hJ => by
    simp only [dtLoop] at h
    split_ifs at h
    · cases h; exact ⟨J, hJ, rfl, rfl, rfl⟩
    · obtain ⟨O1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨J1, hJ1, hc1, hi1, hp1⟩ := model_of_dtLoop h2 J hJ
      obtain ⟨J2, hJ2, hc2, hi2, hp2⟩ := model_of_dtStep h1 J1 hJ1
      exact ⟨J2, hJ2, hc2.trans hc1, hi2.trans hi1, hp2.trans hp1⟩

end DT

/-! ## Rules and keys down -/

section Rules

variable {DM : DatatypeMap}

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
  · obtain ⟨Dom, hD, I, f, hM, hP, hinj, hc, hi, hr⟩ := wTabSCore_facts pat hw
    exact ⟨Dom, hD, I, f, model_hsOff_down hk hM hP, trivial, hinj, hc, hi, hr⟩
  · split at hw
    next W' hW' =>
      cases hw
      obtain ⟨Dom, hD, I, f, hM, hinj, hc, hi, hr⟩ := (wTabCore_facts pat hW').model
      exact ⟨Dom, hD, I, f, hM, trivial, hinj, hc, fun a x h w => (hi a x h).2 w,
        fun r R h w v _ => hr r R h w v⟩
    next =>
      obtain ⟨Dom, hD, I, f, hM, -, hinj, hc, hi, hr⟩ := wTabSCore_facts pat hw
      exact ⟨Dom, hD, I, f, hM, trivial, hinj, hc, hi, hr⟩

open ContextCalculus.SRIQN (dbase dnoms NomAt)
open ContextCalculus.SROIQ (Gen)
open ContextCalculus.SROIQ.Proc (LPath)

/-! ## Exact check for asymmetric and disjoint object properties -/

/-- `⊓ [∃r.⊤, ∃s.⊤] ⊑ ⊤`: interns `r` and `s` with the same concept and
role indices as `noBoth r s`, without forbidding elements that have both. -/
def keepBoth (r s : ObjProp) : Axiom := .subClassOf (.and [.some r .thing, .some s .thing]) .thing

/-- Replace asymmetric and disjoint object-property axioms by `keepBoth`,
keeping disjoint data-property axioms as `noBothD`. -/
def edgeKeepAx : Axiom → List Axiom
  | .asymmetric r => [keepBoth r (opInv r)]
  | .disjointObjectProperties rs => (pairsOf rs).map fun p => keepBoth p.1 p.2
  | .disjointDataProperties ps => (pairsOf ps).map fun p => noBothD p.1 p.2
  | ax => [ax]

/-- **The index-preserving relaxed ontology for `edgeOK`.** -/
def edgeKeep (O : Ontology) : Ontology := ⟨O.axioms.flatMap edgeKeepAx⟩

theorem named_edgeKeepAx (ax : Axiom) :
    (edgeKeepAx ax).flatMap Axiom.namedIndividuals = ax.namedIndividuals := by
  cases ax <;> simp [edgeKeepAx, keepBoth, noBothD, Axiom.namedIndividuals,
    ClassExpr.namedIndividuals, List.flatMap_map]

theorem named_edgeKeep (O : Ontology) : (edgeKeep O).namedIndividuals = O.namedIndividuals := by
  simp only [Ontology.namedIndividuals, edgeKeep, List.flatMap_assoc, named_edgeKeepAx]

/-- The value of the first entry with key `p`. -/
def findR {α β : Type} [BEq α] (L : List (α × β)) (p : α) : Option β :=
  (L.find? fun e => e.1 == p).map Prod.snd

theorem findR_mem {α β : Type} [BEq α] [LawfulBEq α] {L : List (α × β)} {p : α} {b : β}
    (h : findR L p = some b) : (p, b) ∈ L := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some he
  have hp := List.find?_some he
  rw [beq_iff_eq] at hp
  rw [← hp]
  exact hm

def hasEdgeW (W : WTab) (R : SRI.RoleT (Fin W.M)) (b c : Fin W.k) : Bool :=
  (W.adj b).any fun e => e.1 == c && decide (R ∈ e.2)

theorem hasEdgeW_iff {W : WTab}
    (hadj : ∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2)
    (R : SRI.RoleT (Fin W.M)) (b c : Fin W.k) :
    hasEdgeW W R b c = true ↔ R ∈ W.lab b c := by
  unfold hasEdgeW
  rw [hadj, List.any_eq_true]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

def hasPropW (W : WTab) : ObjProp → Option (Fin W.k → Fin W.k → Bool)
  | .named a => (findR W.props (.named a)).map fun R w v => hasEdgeW W R w v
  | .inv a => (findR W.props (.named a)).map fun R w v => hasEdgeW W R v w
  | .top => some fun _ _ => true
  | .bot => some fun _ _ => false

theorem hasPropW_spec {DM : DatatypeMap} {Dom : Type} {W : WTab} {I : Interp DM Dom}
    {f : Fin W.k → Dom}
    (hrole : ∀ r R, (r, R) ∈ W.props → ∀ w v, I.prop r (f w) (f v) ↔ R ∈ W.lab w v)
    (hadj : ∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2)
    {r : ObjProp} {P : Fin W.k → Fin W.k → Bool} (hP : hasPropW W r = some P)
    (w v : Fin W.k) : I.prop r (f w) (f v) ↔ P w v = true := by
  cases r with
  | named a =>
    simp only [hasPropW, Option.map_eq_some_iff] at hP
    obtain ⟨R, hR, rfl⟩ := hP
    exact (hrole (.named a) R (findR_mem hR) w v).trans (hasEdgeW_iff hadj R w v).symm
  | inv a =>
    simp only [hasPropW, Option.map_eq_some_iff] at hP
    obtain ⟨R, hR, rfl⟩ := hP
    show I.prop (.named a) (f v) (f w) ↔ hasEdgeW W R v w = true
    exact (hrole (.named a) R (findR_mem hR) v w).trans (hasEdgeW_iff hadj R v w).symm
  | top =>
    simp only [hasPropW, Option.some.injEq] at hP
    subst hP
    simp [Interp.prop]
  | bot =>
    simp only [hasPropW, Option.some.injEq] at hP
    subst hP
    simp [Interp.prop]

def noSharedEdgeW (W : WTab) (r1 : ObjProp) (P2 : Fin W.k → Fin W.k → Bool) : Bool :=
  match r1 with
  | .named a =>
    match findR W.props (.named a) with
    | some R => (List.finRange W.k).all fun w => (W.adj w).all fun e => !(decide (R ∈ e.2) && P2 w e.1)
    | none => false
  | .inv a =>
    match findR W.props (.named a) with
    | some R => (List.finRange W.k).all fun v => (W.adj v).all fun e => !(decide (R ∈ e.2) && P2 e.1 v)
    | none => false
  | .top => (List.finRange W.k).all fun w => (List.finRange W.k).all fun v => !P2 w v
  | .bot => true

theorem noSharedEdgeW_sound {DM : DatatypeMap} {Dom : Type} {W : WTab} {I : Interp DM Dom}
    {f : Fin W.k → Dom}
    (hrole : ∀ r R, (r, R) ∈ W.props → ∀ w v, I.prop r (f w) (f v) ↔ R ∈ W.lab w v)
    (hadj : ∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2)
    {r1 r2 : ObjProp} {P2 : Fin W.k → Fin W.k → Bool}
    (hP2 : hasPropW W r2 = some P2) (hno : noSharedEdgeW W r1 P2 = true)
    (w v : Fin W.k) : ¬ (I.prop r1 (f w) (f v) ∧ I.prop r2 (f w) (f v)) := by
  rintro ⟨h1, h2⟩
  have hP2v : P2 w v = true := (hasPropW_spec hrole hadj hP2 w v).1 h2
  cases r1 with
  | named a =>
    simp only [noSharedEdgeW] at hno
    cases hR : findR W.props (.named a) with
    | none => rw [hR] at hno; cases hno
    | some R =>
      rw [hR] at hno
      obtain ⟨e, he, rfl, hRe⟩ := (hadj w v R).1 ((hrole (.named a) R (findR_mem hR) w v).1 h1)
      have hall := List.all_eq_true.1 (List.all_eq_true.1 hno w (List.mem_finRange w)) e he
      simp [hRe, hP2v] at hall
  | inv a =>
    simp only [noSharedEdgeW] at hno
    cases hR : findR W.props (.named a) with
    | none => rw [hR] at hno; cases hno
    | some R =>
      rw [hR] at hno
      have h1' : I.prop (.named a) (f v) (f w) := h1
      obtain ⟨e, he, rfl, hRe⟩ := (hadj v w R).1 ((hrole (.named a) R (findR_mem hR) v w).1 h1')
      have hall := List.all_eq_true.1 (List.all_eq_true.1 hno v (List.mem_finRange v)) e he
      simp [hRe, hP2v] at hall
  | top =>
    simp only [noSharedEdgeW] at hno
    have hall := List.all_eq_true.1 (List.all_eq_true.1 hno w (List.mem_finRange w)) v (List.mem_finRange v)
    simp [hP2v] at hall
  | bot => exact h1

def edgeAxOK (W : WTab) : Axiom → Bool
  | .asymmetric r =>
    match hasPropW W r with
    | some P => noSharedEdgeW W (opInv r) P
    | none => false
  | .disjointObjectProperties rs =>
    (pairsOf rs).all fun p =>
      match hasPropW W p.2 with
      | some P2 => noSharedEdgeW W p.1 P2
      | none => false
  | _ => true

def edgeOK (O : Ontology) (W : WTab) : Bool :=
  W.chainR && W.flat && O.axioms.all (edgeAxOK W)

theorem model_of_edgeKeep {DM : DatatypeMap} {Dom : Type} {O : Ontology} {W : WTab}
    {I : Interp DM Dom} {f : Fin W.k → Dom}
    (hrole : ∀ r R, (r, R) ∈ W.props → ∀ w v, I.prop r (f w) (f v) ↔ R ∈ W.lab w v)
    (hadj : ∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2)
    (hsur : W.flat = true → ∀ y, ∃ w, f w = y)
    (hok : edgeOK O W = true) (h : OWL.Model (edgeKeep O) I) :
    OWL.Model O I := by
  simp only [edgeOK, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨-, hfl⟩, haxs⟩ := hok
  have hsur' := hsur hfl
  intro ax hax
  have hin : ∀ b ∈ edgeKeepAx ax, I.sat O.namedIndividuals b := fun b hb => by
    have := h b (List.mem_flatMap.2 ⟨ax, hax, hb⟩)
    rwa [named_edgeKeep] at this
  have haxOK := haxs ax hax
  cases ax with
  | asymmetric r =>
    simp only [edgeAxOK] at haxOK
    cases hP : hasPropW W r with
    | none => rw [hP] at haxOK; cases haxOK
    | some P =>
      rw [hP] at haxOK
      intro x y hxy hyx
      obtain ⟨w, rfl⟩ := hsur' x
      obtain ⟨v, rfl⟩ := hsur' y
      exact noSharedEdgeW_sound hrole hadj hP haxOK w v ⟨(prop_opInv I r (f w) (f v)).2 hyx, hxy⟩
  | disjointObjectProperties rs =>
    simp only [edgeAxOK, List.all_eq_true] at haxOK
    simp only [Interp.sat]
    refine pairwise_of_pairsOf fun p hp x y ⟨h1, h2⟩ => ?_
    have hpOK := haxOK p hp
    cases hP2 : hasPropW W p.2 with
    | none => rw [hP2] at hpOK; cases hpOK
    | some P2 =>
      rw [hP2] at hpOK
      obtain ⟨w, rfl⟩ := hsur' x
      obtain ⟨v, rfl⟩ := hsur' y
      exact noSharedEdgeW_sound hrole hadj hP2 hpOK w v ⟨h1, h2⟩
  | disjointDataProperties ps =>
    simp only [Interp.sat]
    exact pairwise_of_pairsOf fun p hp x v hv =>
      sat_noBothD I _ p.1 p.2 (hin _ (List.mem_map_of_mem hp)) x v hv
  | _ => exact hin _ (List.mem_singleton_self _)

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
        rw [SRIQN.HF.lookSplit_eq, cellSizeS_f, owlES_f] at hp
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

/-- The ontology after unfolding datatype definitions (`none`: they do not unfold). -/
def wDT (O : Ontology) : Option Ontology :=
  if (splitDef O.axioms).isSome then dtLoop O.axioms.length O else some O

theorem model_of_anonOff' {DM : DatatypeMap} {Pre : Ontology} (hk : Pre.noKey = true) {Dom : Type}
    {J : Interp DM Dom} (hJ : OWL.Model (anonOff [] Pre) J) :
    OWL.Model Pre (J.indMap (anonG [] Pre)) :=
  (model_anonOff (W := []) hk (J.indMap (anonG [] Pre))).1 (by
    rw [indMap_indMap J (anonG_inv [] _)]; exact hJ)

/-- Try `edgeKeep O1` when `hasEdgeAx O1` and `edgeOK O1 W` holds; otherwise fall back to `edgeP O1`. -/
def wTabEdge (O1 : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  let H := Std.HashSet.ofList O1.namedIndividuals
  let tryKeep : Option WTab :=
    if hasEdgeAx O1 then
      let PreK := duOff (edgeKeep O1)
      if PreK.noKey && (anonOff [] PreK).noKey then
        match wCoreA (anonOff [] PreK) req hint with
        | some W0 =>
          if edgeOK O1 W0 then some { W0 with inds := W0.inds.filter fun p => H.contains p.1 }
          else none
        | none => none
      else none
    else none
  match tryKeep with
  | some W => some W
  | none =>
    let Pre := duOff (edgeP O1)
    if Pre.noKey && (anonOff [] Pre).noKey then
      (wCoreA (anonOff [] Pre) req hint).map fun W0 =>
        { W0 with inds := W0.inds.filter fun p => H.contains p.1 }
    else none

/-- **The witness row on every route of the hint route.** -/
def wTabA (O : Ontology) (req : List IRI) (hint : RawHint) : Option WTab :=
  match wDT O with
  | none => none
  | some O1 => wTabEdge O1 req hint

theorem wTabEdge_cases {O1 : Ontology} {req : List IRI} {hint : RawHint} {W : WTab}
    (hw : wTabEdge O1 req hint = some W) :
    (∃ W0, (duOff (edgeKeep O1)).noKey = true ∧ (anonOff [] (duOff (edgeKeep O1))).noKey = true ∧
      wCoreA (anonOff [] (duOff (edgeKeep O1))) req hint = some W0 ∧ edgeOK O1 W0 = true ∧
      W = { W0 with inds := W0.inds.filter fun p => (Std.HashSet.ofList O1.namedIndividuals).contains p.1 }) ∨
    (∃ W0, (duOff (edgeP O1)).noKey = true ∧ (anonOff [] (duOff (edgeP O1))).noKey = true ∧
      wCoreA (anonOff [] (duOff (edgeP O1))) req hint = some W0 ∧
      W = { W0 with inds := W0.inds.filter fun p => (Std.HashSet.ofList O1.namedIndividuals).contains p.1 }) := by
  unfold wTabEdge at hw
  dsimp only at hw
  split at hw
  next W' htk =>
    cases hw
    left
    split_ifs at htk with he hk2
    rw [Bool.and_eq_true] at hk2
    split at htk
    next W0 hW0 =>
      split_ifs at htk with hok
      cases htk
      exact ⟨W0, hk2.1, hk2.2, hW0, hok, rfl⟩
    next => cases htk
  next =>
    right
    split_ifs at hw with hk2
    rw [Bool.and_eq_true] at hk2
    obtain ⟨W0, hW0, rfl⟩ := Option.map_eq_some_iff.1 hw
    exact ⟨W0, hk2.1, hk2.2, hW0, rfl⟩

theorem wTabEdge_model {DM : DatatypeMap} {Dom : Type} {O1 E : Ontology} {W0 : WTab}
    {I : Interp DM Dom} {f : Fin W0.k → Dom}
    (hrole : ∀ r R, (r, R) ∈ W0.props → ∀ w v, I.prop r (f w) (f v) ↔ R ∈ W0.lab w v)
    (hadj : ∀ b c R, R ∈ W0.lab b c ↔ ∃ e ∈ W0.adj b, e.1 = c ∧ R ∈ e.2)
    (hsur : W0.flat = true → ∀ y, ∃ w, f w = y)
    (hE : (E = edgeKeep O1 ∧ edgeOK O1 W0 = true) ∨ E = edgeP O1)
    (hM : OWL.Model E I) : OWL.Model O1 I := by
  rcases hE with ⟨rfl, hok⟩ | rfl
  · exact model_of_edgeKeep hrole hadj hsur hok hM
  · exact model_of_edgeP hM

theorem wTabEdge_cases' {O1 : Ontology} {req : List IRI} {hint : RawHint} {W : WTab}
    (hw : wTabEdge O1 req hint = some W) :
    ∃ E W0, ((E = edgeKeep O1 ∧ edgeOK O1 W0 = true) ∨ E = edgeP O1) ∧
      E.namedIndividuals = O1.namedIndividuals ∧
      (duOff E).noKey = true ∧ (anonOff [] (duOff E)).noKey = true ∧
      wCoreA (anonOff [] (duOff E)) req hint = some W0 ∧
      W = { W0 with inds := W0.inds.filter fun p => (Std.HashSet.ofList O1.namedIndividuals).contains p.1 } := by
  rcases wTabEdge_cases hw with ⟨W0, hk, hkX, hW0, hok, rfl⟩ | ⟨W0, hk, hkX, hW0, rfl⟩
  · exact ⟨edgeKeep O1, W0, Or.inl ⟨rfl, hok⟩, named_edgeKeep O1, hk, hkX, hW0, rfl⟩
  · exact ⟨edgeP O1, W0, Or.inr rfl, named_edgeP O1, hk, hkX, hW0, rfl⟩

/-- **The model of an accepted witness hint**, on every route. -/
theorem wTabA_model (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom),
      OWL.Model O I ∧ Function.Injective f ∧
      (∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w) ∧
      (∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w) ∧
      (∀ r R, (r, R) ∈ W.props → ∀ w v, w ≠ v → (I.prop r (f w) (f v) ↔ R ∈ W.lab w v)) := by
  unfold wTabA at hw
  split at hw
  · cases hw
  next O1 hO1 =>
    rcases wTabEdge_cases hw with ⟨W0, hk, hkX, hW0, hok, rfl⟩ | ⟨W0, hk, hkX, hW0, rfl⟩
    · have hcr : W0.chainR = true := by
        simp only [edgeOK, Bool.and_eq_true] at hok; exact hok.1.1
      obtain ⟨Dom, hD, J, f, hJ, hinj, hcls, hind, hrole, hadj, -, -, hsur⟩ := wCoreA_rfacts pat hW0 hcr
      haveI := hD
      set g := anonG [] (duOff (edgeKeep O1))
      have hgprop : (J.indMap g).prop = J.prop := by cases J; rfl
      have hM1 : OWL.Model O1 (J.indMap g) :=
        model_of_edgeKeep (fun r R hr w v => by rw [hgprop]; exact hrole r R hr w v) hadj hsur hok
          ((model_duOff _ _).1 (model_of_anonOff' hk hJ))
      have hM : ∃ J' : Interp (owl2MapP pat) Dom, OWL.Model O J' ∧ J'.cls = (J.indMap g).cls ∧
          J'.ind = (J.indMap g).ind ∧ J'.prop = (J.indMap g).prop := by
        unfold wDT at hO1
        split_ifs at hO1
        · exact model_of_dtLoop hO1 _ hM1
        · cases hO1; exact ⟨_, hM1, rfl, rfl, rfl⟩
      obtain ⟨I, hI, hIc, hIi, hIp⟩ := hM
      have hgcls : (J.indMap g).cls = J.cls := by cases J; rfl
      refine ⟨Dom, hD, I, f, hI, hinj, fun s x hs w => ?_, fun a x hax w => ?_,
        fun r R hr w v _ => by rw [hIp, hgprop]; exact hrole r R hr w v⟩
      · rw [hIc, hgcls]; exact hcls s x hs w
      · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
        have ha : a ∈ (duOff (edgeKeep O1)).namedIndividuals := by
          rw [mem_namedIndividuals_duOff, named_edgeKeep]
          simpa [Std.HashSet.contains_ofList] using hc
        have hfix : g (.named a) = .named a := anonF_short (anonBase_long (by
          simp only [List.nil_append]; exact ha))
        have : I.ind (.named a) = J.ind (.named a) := by
          rw [hIi]; cases J; simp only [Interp.indMap, hfix]
        rw [this]
        exact hind a x hax w
    · obtain ⟨Dom, hD, J, f, hJ, -, hinj, hcls, hind, hrole⟩ := wCoreA_facts pat hkX hW0
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
      refine ⟨Dom, hD, I, f, hI, hinj, fun s x hs w => ?_, fun a x hax w => ?_,
        fun r R hr w v hwv => by rw [hIp, hgprop]; exact hrole r R hr w v hwv⟩
      · rw [hIc, hgcls]; exact hcls s x hs w
      · obtain ⟨hax, hc⟩ := List.mem_filter.1 hax
        have ha : a ∈ (duOff (edgeP O1)).namedIndividuals := by
          rw [mem_namedIndividuals_duOff, named_edgeP]
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
  obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind, -⟩ := wTabA_model pat hw
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
  obtain ⟨Dom, hD, I, f, hM0, hinj, hcls, hind, -⟩ := wTabA_model pat hw'
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

/-! ## More rows from the model: disjointness, difference, role assertions -/

/-- **More rows of the witness model** (stage H2): `A ⊓ B` satisfiable when
one core element holds both; `a` and `b` not entailed different when they
sit on one core element; `r(a, b)` not entailed for a named property `r`
whose role term is simple in the normal form, when `a` and `b` sit on
different core elements whose label has no `r`. -/
theorem hintWitnessMore_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) :
    (∀ (A B : IRI) (iA iB : Fin W.N) (w : Fin W.k), (A, iA) ∈ W.cls → (B, iB) ∈ W.cls →
      isBuiltinCls A = false → isBuiltinCls B = false → iA ∈ W.ty w → iB ∈ W.ty w →
      ¬ EntailsAt (owl2MapP pat) O (.disjointClasses [clsOf A, clsOf B])) ∧
    (∀ (a b : IRI) (ia ib : Fin W.N) (w : Fin W.k), (a, ia) ∈ W.inds → (b, ib) ∈ W.inds →
      ia ∈ W.ty w → ib ∈ W.ty w →
      ¬ EntailsAt (owl2MapP pat) O (.differentIndividuals [.named a, .named b])) ∧
    (∀ (a b : IRI) (ia ib : Fin W.N) (w v : Fin W.k) (r : ObjProp) (R : SRI.RoleT (Fin W.M)),
      (a, ia) ∈ W.inds → (b, ib) ∈ W.inds → ia ∈ W.ty w → ib ∈ W.ty v → w ≠ v →
      (r, R) ∈ W.props → R ∉ W.lab w v →
      ¬ EntailsAt (owl2MapP pat) O (.objectPropertyAssertion r (.named a) (.named b))) := by
  obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind, hrole⟩ := wTabA_model pat hw
  haveI := hD
  refine ⟨?_, ?_, ?_⟩
  · intro A B iA iB w hA hB hbA hbB hiA hiB he
    have h1 := he Dom I hM
    rw [clsOf_of_not_builtin hbA, clsOf_of_not_builtin hbB] at h1
    simp only [Interp.sat, List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
      List.Pairwise.nil, and_true, Interp.ext] at h1
    exact h1.1 (f w) ⟨(hcls A iA hA w).2 hiA, (hcls B iB hB w).2 hiB⟩
  · intro a b ia ib w ha hb hia hib he
    have h1 := he Dom I hM
    simp only [Interp.sat, List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
      List.Pairwise.nil, and_true] at h1
    exact h1.1 (((hind a ia ha w).2 hia).symm.trans ((hind b ib hb w).2 hib))
  · intro a b ia ib w v r R ha hb hia hib hwv hr hR he
    have h1 := he Dom I hM
    simp only [Interp.sat] at h1
    rw [← (hind a ia ha w).2 hia, ← (hind b ib hb v).2 hib] at h1
    exact hR ((hrole r R hr w v hwv).1 h1)

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.model_of_dtLoop
#print axioms ContextCalculus.OWLFrontend.modelR_of_encRules
#print axioms ContextCalculus.OWLFrontend.wTabA_model
#print axioms ContextCalculus.OWLFrontend.hintWitnessA_sound
#print axioms ContextCalculus.OWLFrontend.hintWitnessR_sound
#print axioms ContextCalculus.OWLFrontend.hintWitnessMore_sound
