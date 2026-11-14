import ContextCalculus.OWL.Datatypes.CellsSpec

/-!
# Base atoms are constant on cells (v1.7.0 stage C4, part C)

`evalCell_correct`: a supported base atom of the list `as` holds at a
value iff `evalCell` says so on the value's cell.
-/

namespace ContextCalculus.OWL.Datatypes

/-! ## Points -/

theorem isInt_cast (q : ℚ) : (∃ z : ℤ, (q : ℝ) = z) ↔ q.den = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    have : q = z := by exact_mod_cast hz
    rw [this]; rfl
  · intro h
    refine ⟨q.num, ?_⟩
    have : q = q.num := by
      rw [← Rat.num_div_den q, h]; simp
    rw [this]; simp

theorem decQ_iff_real (q : ℚ) : decQ q = true ↔ IsDecimalR (q : ℝ) := by
  rw [isDecimalR_cast, isDecimalQ_iff]

theorem exists_int_cast_eq (q : ℚ) (P : ℤ → Prop) :
    (∃ z : ℤ, (q : ℝ) = z ∧ P z) ↔ q.den = 1 ∧ P q.num := by
  constructor
  · rintro ⟨z, hz, hP⟩
    have : q = z := by exact_mod_cast hz
    subst this
    simpa using hP
  · rintro ⟨h, hP⟩
    refine ⟨q.num, ?_, hP⟩
    have : q = q.num := by
      rw [← Rat.num_div_den q, h]; simp
    conv_lhs => rw [this]
    simp

theorem num_le_iff {q : ℚ} (h : q.den = 1) (l : ℤ) : l ≤ q.num ↔ (l : ℚ) ≤ q := by
  have : q = q.num := by rw [← Rat.num_div_den q, h]; simp
  conv_rhs => rw [this]
  exact_mod_cast Iff.rfl

theorem le_num_iff {q : ℚ} (h : q.den = 1) (l : ℤ) : q.num ≤ l ↔ q ≤ (l : ℚ) := by
  have : q = q.num := by rw [← Rat.num_div_den q, h]; simp
  conv_rhs => rw [this]
  exact_mod_cast Iff.rfl

theorem kindPt_integer (lo hi : Option ℤ) (q : ℚ) :
    kindSem (.integer lo hi) (toVal (.num q)) ↔ kindPt (.integer lo hi) (.num q) = true := by
  show (∃ z : ℤ, ValOf.num (q : ℝ) = .num (z : ℝ) ∧ _) ↔ _
  simp only [ValOf.num.injEq, kindPt, Bool.and_eq_true, beq_iff_eq]
  rw [exists_int_cast_eq q (fun z => (∀ l ∈ lo, l ≤ z) ∧ ∀ h ∈ hi, z ≤ h)]
  constructor
  · rintro ⟨hd, h1, h2⟩
    refine ⟨⟨hd, ?_⟩, ?_⟩
    · rcases lo with _ | l
      · rfl
      · simpa [Option.all, ← num_le_iff hd] using h1 l rfl
    · rcases hi with _ | h
      · rfl
      · simpa [Option.all, ← le_num_iff hd] using h2 h rfl
  · rintro ⟨⟨hd, h1⟩, h2⟩
    refine ⟨hd, fun l hl => ?_, fun h hh => ?_⟩
    · cases hl
      simpa [Option.all, ← num_le_iff hd] using h1
    · cases hh
      simpa [Option.all, ← le_num_iff hd] using h2

/-- The kind check on points is `kindSem`. -/
theorem kindPt_correct (k : Kind) (w : ValOf ℚ) : kindSem k (toVal w) ↔ kindPt k w = true := by
  cases k
  case integer lo hi =>
    rcases w with q | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, _ | z⟩ | s | n
    · exact kindPt_integer lo hi q
    all_goals simp [kindSem, kindPt, toVal, ValOf.map]
  all_goals rcases w with q | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, _ | z⟩ | s | n <;>
    simp [kindSem, kindPt, toVal, ValOf.map, strSem, ← decQ_iff_real, ← isDecimalQ_iff, and_assoc, offOK]

theorem boundRel_cast (b : Bool × Bool) (q y : ℚ) :
    boundRel b (q : ℝ) (y : ℝ) ↔ boundB b q y = true := by
  rcases b with ⟨_ | _, _ | _⟩ <;> simp [boundRel, boundB]

theorem kindPt_num_false {k : Kind} (hk : numKind k = true) {w : ValOf ℚ} (hw : ∀ q, w ≠ .num q) :
    kindPt k w = false := by
  cases k <;> simp [numKind] at hk <;> cases w <;> simp_all [kindPt]

theorem kindSem_num_of {k : Kind} (hk : numKind k = true) {v : Val} (h : kindSem k v) :
    ∃ x, v = .num x := by
  cases k <;> simp [numKind] at hk
  · obtain ⟨x, rfl⟩ := h; exact ⟨x, rfl⟩
  · obtain ⟨x, rfl, -⟩ := h; exact ⟨x, rfl⟩
  · obtain ⟨z, rfl, -⟩ := h; exact ⟨_, rfl⟩

/-- **Points.** A supported atom at a point. -/
theorem evalPt_correct {a : BAtom} (hs : a.supported = true) (w : ValOf ℚ) :
    a.sem (toVal w) ↔ evalPt a w = true := by
  cases a with
  | kind k => exact kindPt_correct k w
  | numR k bs =>
    simp only [BAtom.supported] at hs
    simp only [BAtom.sem, evalPt, Bool.and_eq_true]
    rw [kindPt_correct]
    cases w with
    | num q =>
      simp only [List.all_eq_true]
      refine and_congr_right fun _ => forall₂_congr fun b _ => ?_
      rw [← boundRel_cast]
      constructor
      · rintro ⟨x, hx, hr⟩
        have : (q : ℝ) = x := by simpa [toVal, ValOf.map] using hx
        rw [this]; exact hr
      · intro h; exact ⟨q, rfl, h⟩
    | _ =>
      rw [kindPt_num_false hs (by intro q h; cases h)]
      simp
  | empty => simp [BAtom.sem, evalPt]
  | lit w' =>
    simp only [BAtom.sem, evalPt, beq_iff_eq]
    exact toVal_injective.eq_iff

/-! ## Gaps -/

section GapEval

variable {P : List ℚ} {x : ℝ}

theorem lt_iff_ptBelow {p : ℚ} (hp : p ∈ P) :
    (p : ℝ) < x ↔ ptBelow (maxBelow P x) p = true := by
  constructor
  · intro h
    cases hm : maxBelow P x with
    | none => exact absurd h (maxBelow_none hm p hp)
    | some a =>
      simp only [ptBelow, decide_eq_true_eq]
      exact (maxBelow_some hm).2.2 p hp h
  · intro h
    cases hm : maxBelow P x with
    | none => rw [hm] at h; simp [ptBelow] at h
    | some a =>
      rw [hm] at h
      simp only [ptBelow, decide_eq_true_eq] at h
      have h1 : (p : ℝ) ≤ a := by exact_mod_cast h
      exact lt_of_le_of_lt h1 (maxBelow_some hm).2.1

theorem gt_iff_ptAbove {p : ℚ} (hp : p ∈ P) :
    x < (p : ℝ) ↔ ptAbove (minAbove P x) p = true := by
  constructor
  · intro h
    cases hm : minAbove P x with
    | none => exact absurd h (minAbove_none hm p hp)
    | some b =>
      simp only [ptAbove, decide_eq_true_eq]
      exact (minAbove_some hm).2.2 p hp h
  · intro h
    cases hm : minAbove P x with
    | none => rw [hm] at h; simp [ptAbove] at h
    | some b =>
      rw [hm] at h
      simp only [ptAbove, decide_eq_true_eq] at h
      have h1 : (b : ℝ) ≤ p := by exact_mod_cast h
      exact lt_of_lt_of_le (minAbove_some hm).2.1 h1

theorem isDecimalR_iff_class (x : ℝ) : IsDecimalR x ↔ numClass x ≠ 2 := by
  constructor
  · intro h h2
    exact (numClass_two.1 h2).2 h
  · intro h
    by_cases h0 : numClass x = 0
    · obtain ⟨z, rfl⟩ := numClass_zero.1 h0
      exact ⟨z, 0, by simp⟩
    · have h1 : numClass x = 1 := by
        have := numClass x |>.isLt
        generalize hc : numClass x = c at h h0 ⊢
        fin_cases c <;> simp_all
      exact (numClass_one.1 h1).2

/-- A kind at a real off the points. -/
theorem kindGap_correct {k : Kind} (hk : supportedKind k = true) (hP : ∀ p ∈ intBounds k, p ∈ P)
    (hx : ∀ q ∈ P, (q : ℝ) ≠ x) :
    kindSem k (.num x) ↔ kindGap k (maxBelow P x) (minAbove P x) (numClass x) = true := by
  cases k <;> simp [supportedKind] at hk <;> simp only [kindSem, kindGap]
  · simp
  · simp only [ValOf.num.injEq, exists_eq_left', bne_iff_ne, ne_eq]
    rw [isDecimalR_iff_class]
  · rename_i lo hi
    simp only [ValOf.num.injEq, Bool.and_eq_true, beq_iff_eq]
    have hl : ∀ l ∈ lo, (l : ℚ) ∈ P := fun l hl => hP _ (by
      simp only [intBounds, List.mem_append, List.mem_map, Option.mem_toList]; exact Or.inl ⟨l, hl, rfl⟩)
    have hh : ∀ h ∈ hi, (h : ℚ) ∈ P := fun h hh => hP _ (by
      simp only [intBounds, List.mem_append, List.mem_map, Option.mem_toList]; exact Or.inr ⟨h, hh, rfl⟩)
    constructor
    · rintro ⟨z, rfl, h1, h2⟩
      refine ⟨⟨numClass_zero.2 ⟨z, rfl⟩, ?_⟩, ?_⟩
      · rcases lo with _ | l
        · rfl
        · simp only [Option.all]
          refine (lt_iff_ptBelow (hl l rfl)).1 (lt_of_le_of_ne ?_ (hx _ (hl l rfl)))
          exact_mod_cast h1 l rfl
      · rcases hi with _ | h
        · rfl
        · simp only [Option.all]
          refine (gt_iff_ptAbove (hh h rfl)).1 (lt_of_le_of_ne ?_ (hx _ (hh h rfl)).symm)
          exact_mod_cast h2 h rfl
    · rintro ⟨⟨h0, h1⟩, h2⟩
      obtain ⟨z, rfl⟩ := numClass_zero.1 h0
      refine ⟨z, rfl, fun l hlo => ?_, fun h hhi => ?_⟩
      · cases hlo
        simp only [Option.all] at h1
        have := (lt_iff_ptBelow (hl l rfl)).2 h1
        exact_mod_cast this.le
      · cases hhi
        simp only [Option.all] at h2
        have := (gt_iff_ptAbove (hh h rfl)).2 h2
        exact_mod_cast this.le
  all_goals simp [strSem]

theorem boundGap_correct {b : Bool × Bool} {y : ℚ} (hy : y ∈ P) (hx : ∀ q ∈ P, (q : ℝ) ≠ x) :
    boundRel b x (y : ℝ) ↔ boundGap b y (maxBelow P x) (minAbove P x) = true := by
  rcases b with ⟨_ | _, _ | _⟩ <;> simp only [boundRel, boundGap]
  · rw [← gt_iff_ptAbove hy, le_iff_lt_or_eq, or_iff_left (hx y hy).symm]
  · rw [← gt_iff_ptAbove hy]
  · rw [← lt_iff_ptBelow hy, le_iff_lt_or_eq, or_iff_left (hx y hy)]
  · rw [← lt_iff_ptBelow hy]

end GapEval

/-! ## The rest cells -/

theorem kindRest_correct {k : Kind} (hk : supportedKind k = true) {v : Val}
    (hn : ∀ x, v ≠ .num x) (hb : ∀ b, v ≠ .bool b) :
    kindSem k v ↔ kindRest k (restCell v) = true := by
  rcases v with x | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, _ | z⟩ | s | n
  · exact absurd rfl (hn x)
  all_goals try exact absurd rfl (hb _)
  all_goals cases k <;> simp [supportedKind] at hk <;>
    simp only [kindSem, restCell, strSem] <;> (try split_ifs) <;>
    simp_all [kindRest, isDecimalQ_iff, offOK]

theorem evalCell_restCell (a : BAtom) (v : Val) :
    evalCell a (restCell v) = match a with
      | .kind k => kindRest k (restCell v)
      | _ => false := by
  have h1 := restCell_ne_pt v
  have h2 := restCell_ne_gap v
  generalize restCell v = c at h1 h2 ⊢
  cases c with
  | pt w => exact absurd rfl (h1 w)
  | gap lo hi k => exact absurd rfl (h2 lo hi k)
  | _ => cases a <;> rfl

/-! ## The atoms of a list on the cells -/

section Main

variable {as : List BAtom}

theorem nums_sub {a : BAtom} (ha : a ∈ as) {p : ℚ} (hp : p ∈ a.nums) : p ∈ numPts as :=
  List.mem_dedup.2 (List.mem_flatMap.2 ⟨a, ha, hp⟩)

theorem lit_pt {w : ValOf ℚ} (ha : BAtom.lit w ∈ as) : w ∈ allPts as := by
  cases w with
  | num q => exact List.mem_append_left _ (List.mem_map_of_mem (nums_sub ha (by simp [BAtom.nums])))
  | _ => exact List.mem_append_right _ (List.mem_dedup.2 (List.mem_append_left _
      (List.mem_flatMap.2 ⟨_, ha, by simp [BAtom.others]⟩)))

theorem bool_pt (b : Bool) : ValOf.bool b ∈ allPts as := by
  refine List.mem_append_right _ (List.mem_dedup.2 (List.mem_append_right _ ?_))
  cases b <;> simp

/-- **Base atoms are constant on cells.** -/
theorem evalCell_correct {a : BAtom} (ha : a ∈ as) (hs : a.supported = true) (v : Val) :
    a.sem v ↔ evalCell a (cellOf as v) = true := by
  classical
  by_cases hv : ∃ w ∈ allPts as, toVal w = v
  · obtain ⟨w, hw, rfl⟩ := hv
    rw [cellOf_pt hw]
    exact evalPt_correct hs w
  · cases v with
    | num x =>
      have hx : ∀ q ∈ numPts as, (q : ℝ) ≠ x := fun q hq he => hv (num_pt_iff.2 ⟨q, hq, he⟩)
      rw [cellOf_num_gap hx]
      cases a with
      | kind k =>
        exact kindGap_correct hs (fun p hp => nums_sub ha (by simpa [BAtom.nums] using hp)) hx
      | numR k bs =>
        simp only [BAtom.supported] at hs
        have hk : supportedKind k = true := by cases k <;> simp_all [numKind, supportedKind]
        simp only [BAtom.sem, evalCell, Bool.and_eq_true, List.all_eq_true]
        rw [kindGap_correct hk (fun p hp => nums_sub ha (by simp [BAtom.nums, hp])) hx]
        refine and_congr_right fun _ => forall₂_congr fun b hb => ?_
        have hy : b.2 ∈ numPts as := nums_sub ha (by
          simp only [BAtom.nums, List.mem_append, List.mem_map]
          exact Or.inr ⟨b, hb, rfl⟩)
        rw [← boundGap_correct hy hx]
        constructor
        · rintro ⟨x', hx', hr⟩
          cases hx'
          exact hr
        · intro h; exact ⟨x, rfl, h⟩
      | empty => simp [BAtom.sem, evalCell]
      | lit w =>
        simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
        intro he
        exact hv ⟨w, lit_pt ha, he.symm⟩
    | _ =>
      rw [cellOf_rest hv (by intro x h; cases h), evalCell_restCell]
      cases a with
      | kind k =>
        refine kindRest_correct hs (by intro x h; cases h) ?_
        intro b hb
        exact hv ⟨.bool b, bool_pt b, by rw [hb]; rfl⟩
      | numR k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem, Bool.false_eq_true, iff_false]
        rintro ⟨h1, -⟩
        obtain ⟨x, hx⟩ := kindSem_num_of hs h1
        cases hx
      | empty => simp [BAtom.sem]
      | lit w =>
        simp only [BAtom.sem, Bool.false_eq_true, iff_false]
        intro he
        exact hv ⟨w, lit_pt ha, he.symm⟩

end Main

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.evalCell_correct
