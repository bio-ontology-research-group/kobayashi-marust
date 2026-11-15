import ContextCalculus.OWLFrontend.HintRows
import ContextCalculus.OWLFrontend.HintEvalD
import ContextCalculus.OWLFrontend.HintData

/-!
# The data rows of the witness model (stage H5, item 2)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 13. `ckOfD W fuel dOK` is `ckOf`
with the data of the given data stars:

* the values of a named data property `P` at a core element `w` with a
  given star `S` are the entry numbers `i` whose label holds a data
  property with IRI `P`; the list is exact;
* a data range `R` at value `i` of `w` is evaluated on the entry's atom set
  `τ` (`evR`): an atom whose data range is `R` answers by membership in `τ`;
  a `DataOneOf` atom of one value in `τ` pins the value to that literal,
  and a data range without free datatypes is then evaluated at the point;
  `DataOneOf` of literals is decided when the literal has no value, when
  the value is pinned, or when some atom without free datatypes answers on
  the literal differently from `τ`; `and`, `or`, `not` and `rdfs:Literal`
  as usual.

`dOK` switches the data on: the rows below take
`dOK = (splitDef O.axioms).isNone` (no datatype definitions), and the data
is used on the chain route only.

* `evR_sound`: a value whose atom set is `τ` (every atom holds at it iff
  it is in `τ`) lies in `R` iff `evR` says so, when it says anything.
* `ckOfD_spec`: the table is true of a model of `O`.
* `hintRefuteD_sound`, `hintRefuteSubD_sound`: `refuteD (ckOfD W fuel
  (splitDef O.axioms).isNone) ax = true` certifies that `O` does not entail
  `ax` (resp. the subsumption).
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes
open ContextCalculus.SROIQ (Gen Stack)
open ContextCalculus.SROIQ.Proc (LPath succOf succOf_sound succOf_complete)

/-! ## Data ranges on an atom set -/

section EvR

variable {q : Nat} (sp : Fin q → DataRange) (τ : Finset (Fin q))

/-- The point of a `DataOneOf` of literals of one value. -/
def litsPt : DataRange → Option (ValOf ℚ)
  | .oneOf (l :: ls) =>
    match litVal l with
    | some w => if ls.all (fun l' => litVal l' == some w) then some w else none
    | none => none
  | _ => none

/-- The value is pinned to a point by an atom of `τ`. -/
def pinPt : Option (ValOf ℚ) :=
  (List.finRange q).findSome? fun j => if j ∈ τ then litsPt (sp j) else none

/-- A data range without free datatypes, at a point. -/
def ptEval (R : DataRange) (w0 : ValOf ℚ) : Option Bool :=
  if drSupported R && (drFrees R).isEmpty then some (drEval (fun a => evalPt a w0) (fun _ => false) R)
  else none

/-- The atom whose data range is `R`. -/
def findAtom (R : DataRange) : Option (Fin q) :=
  (List.finRange q).find? fun j => decide (sp j = R)

/-- What an atom or the pinned point says. -/
def preR (R : DataRange) : Option Bool :=
  match findAtom sp R with
  | some j => some (decide (j ∈ τ))
  | none =>
    match pinPt sp τ with
    | some w0 => ptEval R w0
    | none => none

/-- Is the value the value of the literal `l`? -/
def litEval (l : Literal) : Option Bool :=
  match litVal l with
  | none => some false
  | some w =>
    match pinPt sp τ with
    | some w0 => some (w0 == w)
    | none =>
      if (List.finRange q).any (fun j => match ptEval (sp j) w with
          | some b => b != decide (j ∈ τ)
          | none => false) then some false
      else none

def evLits : List Literal → Option Bool
  | [] => some false
  | l :: ls => orV (litEval sp τ l) (evLits ls)

mutual

/-- **A data range on an atom set.** -/
def evR : DataRange → Option Bool
  | .and rs => match preR sp τ (.and rs) with
    | some b => some b
    | none => evRAnd rs
  | .or rs => match preR sp τ (.or rs) with
    | some b => some b
    | none => evROr rs
  | .not r => match preR sp τ (.not r) with
    | some b => some b
    | none => (evR r).map (!·)
  | .oneOf ls => match preR sp τ (.oneOf ls) with
    | some b => some b
    | none => evLits sp τ ls
  | .datatype t => match preR sp τ (.datatype t) with
    | some b => some b
    | none => if t = rdfsLiteral then some true else none
  | .restriction t fs => preR sp τ (.restriction t fs)

def evRAnd : List DataRange → Option Bool
  | [] => some true
  | r :: rs => andV (evR r) (evRAnd rs)

def evROr : List DataRange → Option Bool
  | [] => some false
  | r :: rs => orV (evR r) (evROr rs)

end

variable {pat : String → String → Prop} {dtype : IRI → Val → Prop} {v : Val}
variable {sp τ}

theorem litsPt_sound {R : DataRange} {w0 : ValOf ℚ} (h : litsPt R = some w0)
    (hR : R.ext (owl2MapP pat) dtype v) : v = toVal w0 := by
  unfold litsPt at h
  split at h
  next l ls =>
    split at h
    next w hw =>
      split_ifs at h with hall
      cases h
      rw [DataRange.ext] at hR
      obtain ⟨l', hl', he⟩ := hR
      rw [owl2MapP_literal] at he
      rcases List.mem_cons.1 hl' with rfl | hl'
      · rw [hw] at he; exact (Option.some.inj (he : some (toVal w0) = some v)).symm
      · have := List.all_eq_true.1 hall l' hl'
        rw [beq_iff_eq] at this
        rw [this] at he; exact (Option.some.inj (he : some (toVal w0) = some v)).symm
    next => cases h
  next => cases h

theorem pinPt_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) {w0 : ValOf ℚ}
    (h : pinPt sp τ = some w0) : v = toVal w0 := by
  unfold pinPt at h
  obtain ⟨-, j, -, -, hj, -⟩ := List.findSome?_eq_some_iff.1 h
  split_ifs at hj with hjτ
  exact litsPt_sound hj ((hτ j).2 hjτ)

theorem ptEval_sound {R : DataRange} {w0 : ValOf ℚ} {b : Bool} (h : ptEval R w0 = some b) :
    (R.ext (owl2MapP pat) dtype (toVal w0) ↔ b = true) := by
  unfold ptEval at h
  split_ifs at h with hs
  cases h
  rw [Bool.and_eq_true, List.isEmpty_iff] at hs
  refine ext_iff_drEval pat dtype (toVal w0) _ _ R hs.1 (fun a ha => ?_) (fun t ht => ?_)
  · exact evalPt_correct (supported_of_drBases R hs.1 a ha) w0
  · rw [hs.2] at ht; cases ht

theorem preR_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) {R : DataRange} {b : Bool}
    (h : preR sp τ R = some b) : (R.ext (owl2MapP pat) dtype v ↔ b = true) := by
  unfold preR at h
  split at h
  next j hj =>
    cases h
    have he := List.find?_some hj
    rw [decide_eq_true_eq] at he
    rw [← he, hτ j, decide_eq_true_iff]
  next =>
    split at h
    next w0 hw =>
      rw [pinPt_sound hτ hw]
      exact ptEval_sound h
    next => cases h

theorem litEval_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) {l : Literal} {b : Bool}
    (h : litEval sp τ l = some b) : ((owl2MapP pat).literal l = some v ↔ b = true) := by
  rw [owl2MapP_literal]
  unfold litEval at h
  split at h
  next hl => cases h; rw [hl]; simp
  next w hl =>
    rw [hl]
    split at h
    next w0 hw =>
      cases h
      rw [pinPt_sound hτ hw]
      show some (toVal w) = some (toVal w0) ↔ (w0 == w) = true
      rw [Option.some.injEq, beq_iff_eq]
      exact ⟨fun he => (toVal_injective he).symm, fun he => by rw [he]⟩
    next =>
      split_ifs at h with hany
      cases h
      show some (toVal w) = some v ↔ false = true
      simp only [Bool.false_eq_true, iff_false]
      intro he
      obtain ⟨j, -, hj⟩ := List.any_eq_true.1 hany
      split at hj
      next b' hb' =>
        have h1 := ptEval_sound (pat := pat) (dtype := dtype) hb'
        have hv : toVal w = v := Option.some.inj he
        rw [hv, hτ j] at h1
        rw [bne_iff_ne, ne_eq] at hj
        apply hj
        by_cases hjτ : j ∈ τ
        · rw [decide_eq_true hjτ]; exact h1.1 hjτ
        · rw [decide_eq_false hjτ]
          cases b' with
          | false => rfl
          | true => exact absurd (h1.2 rfl) hjτ
      next => cases hj

theorem evLits_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) :
    ∀ (ls : List Literal) {b : Bool}, evLits sp τ ls = some b →
      ((∃ l ∈ ls, (owl2MapP pat).literal l = some v) ↔ b = true)
  | [], b, h => by cases h; simp
  | l :: ls, b, h => by
    rw [evLits] at h
    have h1 := fun b => litEval_sound (l := l) (b := b) hτ
    have h2 := fun b => evLits_sound hτ ls (b := b)
    cases b with
    | true =>
      simp only [iff_true]
      rcases orV_true h with ha | hb
      · exact ⟨l, List.mem_cons_self, (h1 true ha).2 rfl⟩
      · obtain ⟨l', hl', he⟩ := (h2 true hb).2 rfl
        exact ⟨l', List.mem_cons_of_mem _ hl', he⟩
    | false =>
      simp only [Bool.false_eq_true, iff_false, not_exists, not_and]
      obtain ⟨ha, hb⟩ := orV_false h
      intro l' hl' he
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact absurd ((h1 false ha).1 he) (by simp)
      · exact absurd ((h2 false hb).1 ⟨l', hl', he⟩) (by simp)

mutual

/-- **Soundness of the evaluation on an atom set.** -/
theorem evR_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) :
    ∀ (R : DataRange) {b : Bool}, evR sp τ R = some b → (R.ext (owl2MapP pat) dtype v ↔ b = true)
  | .and rs, b, h => by
    rw [evR] at h
    split at h
    next b' hb => cases h; exact preR_sound hτ hb
    next =>
      rw [DataRange.ext]
      have := evRAnd_sound hτ rs (b := b) h
      exact ⟨fun hall => this.1 fun r hr => hall r hr, fun hb r hr => this.2 hb r hr⟩
  | .or rs, b, h => by
    rw [evR] at h
    split at h
    next b' hb => cases h; exact preR_sound hτ hb
    next =>
      rw [DataRange.ext]
      have := evROr_sound hτ rs (b := b) h
      exact ⟨fun ⟨r, hr, he⟩ => this.1 ⟨r, hr, he⟩, fun hb => by
        obtain ⟨r, hr, he⟩ := this.2 hb; exact ⟨r, hr, he⟩⟩
  | .not r, b, h => by
    rw [evR] at h
    split at h
    next b' hb => cases h; exact preR_sound hτ hb
    next =>
      rw [DataRange.ext]
      cases hv : evR sp τ r with
      | none => rw [hv] at h; cases h
      | some b' =>
        rw [hv] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        have := evR_sound hτ r hv
        cases b' <;> simp_all
  | .oneOf ls, b, h => by
    rw [evR] at h
    split at h
    next b' hb => cases h; exact preR_sound hτ hb
    next =>
      rw [DataRange.ext]
      exact evLits_sound hτ ls h
  | .datatype t, b, h => by
    rw [evR] at h
    split at h
    next b' hb => cases h; exact preR_sound hτ hb
    next =>
      split_ifs at h with ht
      cases h
      rw [DataRange.ext]
      simp [DatatypeMap.dtExt, ht]
  | .restriction t fs, b, h => by
    rw [evR] at h
    exact preR_sound hτ h

theorem evRAnd_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) :
    ∀ (rs : List DataRange) {b : Bool}, evRAnd sp τ rs = some b →
      ((∀ r ∈ rs, r.ext (owl2MapP pat) dtype v) ↔ b = true)
  | [], b, h => by cases h; simp
  | r :: rs, b, h => by
    rw [evRAnd] at h
    cases b with
    | true =>
      obtain ⟨ha, hb⟩ := andV_true h
      have h1 := (evR_sound hτ r ha).2 rfl
      have h2 := (evRAnd_sound hτ rs hb).2 rfl
      simp only [iff_true]
      intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact h1
      · exact h2 r' hr'
    | false =>
      simp only [Bool.false_eq_true, iff_false]
      intro hall
      rcases andV_false h with ha | hb
      · exact absurd ((evR_sound hτ r ha).1 (hall r List.mem_cons_self)) (by simp)
      · exact absurd ((evRAnd_sound hτ rs hb).1 fun r' hr' => hall r' (List.mem_cons_of_mem _ hr'))
          (by simp)

theorem evROr_sound (hτ : ∀ j, (sp j).ext (owl2MapP pat) dtype v ↔ j ∈ τ) :
    ∀ (rs : List DataRange) {b : Bool}, evROr sp τ rs = some b →
      ((∃ r ∈ rs, r.ext (owl2MapP pat) dtype v) ↔ b = true)
  | [], b, h => by cases h; simp
  | r :: rs, b, h => by
    rw [evROr] at h
    cases b with
    | true =>
      simp only [iff_true]
      rcases orV_true h with ha | hb
      · exact ⟨r, List.mem_cons_self, (evR_sound hτ r ha).2 rfl⟩
      · obtain ⟨r', hr', he⟩ := (evROr_sound hτ rs hb).2 rfl
        exact ⟨r', List.mem_cons_of_mem _ hr', he⟩
    | false =>
      simp only [Bool.false_eq_true, iff_false, not_exists, not_and]
      obtain ⟨ha, hb⟩ := orV_false h
      intro r' hr' he
      rcases List.mem_cons.1 hr' with rfl | hr'
      · exact absurd ((evR_sound hτ _ ha).1 he) (by simp)
      · exact absurd ((evROr_sound hτ rs hb).1 ⟨r', hr', he⟩) (by simp)

end

end EvR

/-! ## The knowledge with data -/

/-- The value numbers of a data property at a core element. -/
def ckDv (W : WTab) (dOK : Bool) : DataProp → Fin W.k → List Nat × Bool
  | .bot, _ => ([], true)
  | .top, _ => ([], false)
  | .named P, w =>
    if dOK && W.chainR then
      match W.dst w with
      | some S =>
        let us := (List.finRange W.p).filter fun u => W.dpn u == P
        ((List.range S.length).filter fun i => match S[i]? with
          | some e => us.any fun u => decide (u ∈ e.1)
          | none => false, true)
      | none => ([], false)
    else ([], false)

/-- A data range at value `i` of a core element. -/
def ckDr (W : WTab) (dOK : Bool) (R : DataRange) (w : Fin W.k) (i : Nat) : Option Bool :=
  if dOK && W.chainR then
    match W.dst w with
    | some S =>
      match S[i]? with
      | some e => evR W.dsp e.2 R
      | none => none
    | none => none
  else none

/-- **The core knowledge with data of a witness table.** -/
def ckOfD (W : WTab) (fuel : Nat) (dOK : Bool) : CKX W.k :=
  { toCK := ckOf W fuel, dv := ckDv W dOK, dr := ckDr W dOK }

section Spec

variable {DM : DatatypeMap} {Dom : Type}

/-- The object part of `ckOf` from the role facts of one model. -/
theorem ckSpec_of_facts {W : WTab} {I : Interp DM Dom} {f : Fin W.k → Dom} (fuel : Nat)
    (hc : W.chainR = true) (hinj : Function.Injective f)
    (hcls : ∀ s x, (s, x) ∈ W.cls → ∀ w, I.cls s (f w) ↔ x ∈ W.ty w)
    (hind : ∀ a x, (a, x) ∈ W.inds → ∀ w, f w = I.ind (.named a) ↔ x ∈ W.ty w)
    (hrole : ∀ r R, (r, R) ∈ W.props → ∀ w v, (I.prop r (f w) (f v) ↔ R ∈ W.lab w v))
    (hadj : ∀ b c R, R ∈ W.lab b c ↔ ∃ e ∈ W.adj b, e.1 = c ∧ R ∈ e.2)
    (hpos : ∀ r R, (r, R) ∈ W.rprops → ∀ w v word, Gen W.ob word R → LPath W.lab word w v →
      I.prop r (f w) (f v))
    (hneg : W.flat = true → ∀ r R, (r, R) ∈ W.rprops → ∀ w v, I.prop r (f w) (f v) →
      ∃ word, Gen W.ob word R ∧ LPath W.lab word w v)
    (hsur : W.flat = true → ∀ y, ∃ w, f w = y) : CKSpec (ckOf W fuel) I f := by
  have hsc : ∀ st l st', (l, st') ∈ scOf W.ob st ↔ SROIQ.Move W.ob st l st' := by
    intro st l st'; rw [scOf_eq]; exact SROIQ.Proc.mem_succs
  have hck : ckOf W fuel = CK.mk (ckSucc W (scOf W.ob) fuel) (ckCls W) (ckInd W)
      (W.chainR && W.flat) := rfl
  rw [hck]
  have hB : ∀ (p : ObjProp) (w v : Fin W.k),
      (v ∈ (ckSuccB W (scOf W.ob) fuel p w).1 → I.prop p (f w) (f v)) ∧
      ((ckSuccB W (scOf W.ob) fuel p w).2 = true → I.prop p (f w) (f v) →
        v ∈ (ckSuccB W (scOf W.ob) fuel p w).1) := by
    intro p w v
    unfold ckSuccB
    rw [if_pos hc]
    cases hp : findR W.props p with
    | some R =>
      have hr := hrole p R (findR_mem hp) w v
      refine ⟨fun h => ?_, fun _ h => ?_⟩
      · obtain ⟨e, he, hev⟩ := List.mem_filterMap.1 h
        split_ifs at hev with hR
        cases hev
        exact hr.2 ((hadj w e.1 R).2 ⟨e, he, rfl, hR⟩)
      · obtain ⟨e, he, rfl, hR⟩ := (hadj w v R).1 (hr.1 h)
        exact List.mem_filterMap.2 ⟨e, he, by simp [hR]⟩
    | none =>
      cases hq : findR W.rprops p with
      | none => exact ⟨fun h => absurd h List.not_mem_nil, fun h => (nomatch h)⟩
      | some R =>
        have hmem := findR_mem hq
        dsimp only
        refine ⟨fun h => ?_, fun h h2 => ?_⟩
        · obtain ⟨word, hg, hpth⟩ := succOf_sound (O := W.ob) (lab := W.lab)
            (fun st l st' h => (hsc st l st').1 h)
            (fun x e he R hR => (hadj x e.1 R).2 ⟨e, he, rfl, hR⟩) h
          exact hpos p R hmem w v word hg hpth
        · rw [Bool.and_eq_true] at h
          obtain ⟨word, hg, hpth⟩ := hneg h.2 p R hmem w v h2
          exact succOf_complete (O := W.ob) (lab := W.lab) (fun st l st' h => (hsc st l st').2 h)
            (fun x z R hR => (hadj x z R).1 hR) h.1 hg hpth
  refine ⟨hinj, fun p w v h => ?_, fun p w v hex h => ?_,
    fun A w => (ckCls_spec hcls A w).1, fun A w => (ckCls_spec hcls A w).2,
    fun a w h => ckInd_spec hind a w h, fun h => hsur (by simp_all)⟩
  · cases p with
    | top => trivial
    | bot => exact absurd h List.not_mem_nil
    | named e => exact (hB _ w v).1 h
    | inv e => exact (hB _ w v).1 h
  · cases p with
    | top => exact List.mem_finRange _
    | bot => exact h.elim
    | named e => exact (hB _ w v).2 hex h
    | inv e => exact (hB _ w v).2 hex h

/-- With the data switched off, the data part says nothing. -/
theorem ckxSpec_off {W : WTab} {I : Interp DM Dom} {f : Fin W.k → Dom} {fuel : Nat} {dOK : Bool}
    (hoff : (dOK && W.chainR) = false) (hb : CKSpec (ckOf W fuel) I f) (val : Fin W.k → Nat → DM.Val) :
    CKXSpec (ckOfD W fuel dOK) I f val := by
  have hdv : ∀ P w, ckDv W dOK (.named P) w = ([], false) := fun P w => by
    simp [ckDv, hoff]
  have hdr : ∀ R w i, ckDr W dOK R w i = none := fun R w i => by simp [ckDr, hoff]
  refine ⟨hb, fun p w i hi => ?_, fun p w x hex hx => ?_, fun p p' w i j hi hj _ => ?_,
    fun R w i b h _ => ?_⟩
  · cases p with
    | named P => simp [ckOfD, hdv] at hi
    | top => simp [ckOfD, ckDv] at hi
    | bot => simp [ckOfD, ckDv] at hi
  · cases p with
    | named P => simp [ckOfD, hdv] at hex
    | top => simp [ckOfD, ckDv] at hex
    | bot => exact hx.elim
  · cases p with
    | named P => simp [ckOfD, hdv] at hi
    | top => simp [ckOfD, ckDv] at hi
    | bot => simp [ckOfD, ckDv] at hi
  · simp [ckOfD, hdr] at h

/-- **The core knowledge with data is true of a model of `O`**, for an
ontology without datatype definitions when the data is on. -/
theorem ckOfD_spec (pat : String → String → Prop) {O : Ontology} {req : List IRI} {hint : RawHint}
    {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (dOK : Bool)
    (hd : dOK = true → (splitDef O.axioms).isNone = true) :
    ∃ (Dom : Type) (_ : Nonempty Dom) (I : Interp (owl2MapP pat) Dom) (f : Fin W.k → Dom)
      (val : Fin W.k → Nat → Val), OWL.Model O I ∧ CKXSpec (ckOfD W fuel dOK) I f val := by
  by_cases hon : (dOK && W.chainR) = true
  · rw [Bool.and_eq_true] at hon
    obtain ⟨Dom, hD, I, f, hM, hinj, hcls, hind, hrole, hadj, hpos, hneg, hsur, val, hdat⟩ :=
      wTabA_dfacts pat hw (hd hon.1) hon.2
    have hb := ckSpec_of_facts fuel hon.2 hinj hcls hind hrole hadj hpos hneg hsur
    have hon' : (dOK && W.chainR) = true := by rw [hon.1, hon.2]; rfl
    -- the value lists
    have hdvS : ∀ P w S, W.dst w = some S → ckDv W dOK (.named P) w =
        ((List.range S.length).filter fun i => match S[i]? with
          | some e => ((List.finRange W.p).filter fun u => W.dpn u == P).any fun u => decide (u ∈ e.1)
          | none => false, true) := by
      intro P w S hS
      simp only [ckDv, hon', if_true, hS]
    have hdvN : ∀ P w, W.dst w = none → ckDv W dOK (.named P) w = ([], false) := by
      intro P w hS
      simp only [ckDv, hon', if_true, hS]
    have hmemS : ∀ P w S i, W.dst w = some S → (i ∈ (ckDv W dOK (.named P) w).1 ↔
        ∃ hi : i < S.length, ∃ u : Fin W.p, W.dpn u = P ∧ u ∈ (S[i]).1) := by
      intro P w S i hS
      rw [hdvS P w S hS]
      simp only [List.mem_filter, List.mem_range]
      constructor
      · rintro ⟨hi, h⟩
        rw [List.getElem?_eq_getElem hi] at h
        obtain ⟨u, hu, hue⟩ := List.any_eq_true.1 h
        obtain ⟨-, hu'⟩ := List.mem_filter.1 hu
        exact ⟨hi, u, beq_iff_eq.1 hu', of_decide_eq_true hue⟩
      · rintro ⟨hi, u, hu, hue⟩
        refine ⟨hi, ?_⟩
        rw [List.getElem?_eq_getElem hi]
        exact List.any_eq_true.2 ⟨u, List.mem_filter.2 ⟨List.mem_finRange u, beq_iff_eq.2 hu⟩,
          decide_eq_true hue⟩
    have hlen : ∀ p w i, i ∈ (ckDv W dOK p w).1 → ∃ S, W.dst w = some S ∧ i < S.length := by
      intro p w i hi
      cases p with
      | named P =>
        cases hS : W.dst w with
        | none => rw [hdvN P w hS] at hi; cases hi
        | some S => exact ⟨S, rfl, ((hmemS P w S i hS).1 hi).1⟩
      | top => simp [ckDv] at hi
      | bot => simp [ckDv] at hi
    refine ⟨Dom, hD, I, f, val, hM, ⟨hb, fun p w i hi => ?_, fun p w x hex hx => ?_,
      fun p p' w i j hi hj he => ?_, fun R w i b h hi => ?_⟩⟩
    · cases p with
      | named P =>
        obtain ⟨S, hS, -⟩ := hlen _ w i hi
        obtain ⟨hi', u, hu, hue⟩ := (hmemS P w S i hS).1 hi
        exact ((hdat w S hS).2.2 P (val w i)).2 ⟨u, hu, i, hi', hue, rfl⟩
      | top => simp [ckOfD, ckDv] at hi
      | bot => simp [ckOfD, ckDv] at hi
    · cases p with
      | named P =>
        cases hS : W.dst w with
        | none => simp [ckOfD, hdvN P w hS] at hex
        | some S =>
          obtain ⟨u, hu, i, hi, hue, rfl⟩ := ((hdat w S hS).2.2 P x).1 hx
          exact ⟨i, (hmemS P w S i hS).2 ⟨hi, u, hu, hue⟩, rfl⟩
      | top => simp [ckOfD, ckDv] at hex
      | bot => exact hx.elim
    · obtain ⟨S, hS, hiS⟩ := hlen p w i hi
      obtain ⟨S', hS', hjS⟩ := hlen p' w j hj
      rw [hS] at hS'
      cases hS'
      exact (hdat w S hS).1 i j hiS hjS he
    · obtain ⟨P, hP⟩ := hi
      obtain ⟨S, hS, hiS⟩ := hlen P w i hP
      have h' : ckDr W dOK R w i = some b := h
      simp only [ckDr, hon', if_true, hS, List.getElem?_eq_getElem hiS] at h'
      exact evR_sound (fun j => (hdat w S hS).2.1 i hiS j) R h'
  · rw [Bool.not_eq_true] at hon
    obtain ⟨Dom, hD, I, f, hM, hb⟩ := ckOf_spec pat hw fuel
    exact ⟨Dom, hD, I, f, fun _ _ => .num 0, hM, ckxSpec_off hon hb _⟩

end Spec

/-! ## The rows -/

/-- **A refuted axiom is not entailed** (with data and counting). -/
theorem hintRefuteD_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (ax : Axiom)
    (h : refuteD (ckOfD W fuel (splitDef O.axioms).isNone) ax = true) :
    ¬ EntailsAt (owl2MapP pat) O ax := by
  obtain ⟨Dom, hD, I, f, val, hM, hK⟩ := ckOfD_spec pat hw fuel _ id
  haveI := hD
  exact fun he => refuteD_sound hK _ ax h (he Dom I hM)

/-- **A refuted subsumption between class expressions is not entailed**
(with data and counting). -/
theorem hintRefuteSubD_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (C D : ClassExpr)
    (h : refuteD (ckOfD W fuel (splitDef O.axioms).isNone) (.subClassOf C D) = true) :
    ¬ EntailsSubCE (owl2MapP pat) O C D := by
  obtain ⟨Dom, hD, I, f, val, hM, hK⟩ := ckOfD_spec pat hw fuel _ id
  haveI := hD
  exact fun he => refuteD_sound hK [] _ h (he Dom I hM)

/-- `ckOfD` with the successor tables of `ckMemo` (for the command line). -/
def ckOfDM (W : WTab) (fuel : Nat) (dOK : Bool) (ps : List ObjProp) : CKX W.k :=
  { ckOfD W fuel dOK with toCK := ckMemo (ckOf W fuel) ps }

theorem ckOfDM_eq (W : WTab) (fuel : Nat) (dOK : Bool) (ps : List ObjProp) :
    ckOfDM W fuel dOK ps = ckOfD W fuel dOK := by
  simp only [ckOfDM, ckMemo_eq]
  rfl

/-- **A refuted axiom is not entailed** (with the tables of `ckMemo`). -/
theorem hintRefuteDM_sound (pat : String → String → Prop) {O : Ontology} {req : List IRI}
    {hint : RawHint} {W : WTab} (hw : wTabA O req hint = some W) (fuel : Nat) (ps : List ObjProp)
    (ax : Axiom) (h : refuteD (ckOfDM W fuel (splitDef O.axioms).isNone ps) ax = true) :
    ¬ EntailsAt (owl2MapP pat) O ax := by
  rw [ckOfDM_eq] at h
  exact hintRefuteD_sound pat hw fuel ax h

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.evR_sound
#print axioms ContextCalculus.OWLFrontend.ckOfD_spec
#print axioms ContextCalculus.OWLFrontend.hintRefuteD_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteSubD_sound
#print axioms ContextCalculus.OWLFrontend.hintRefuteDM_sound
