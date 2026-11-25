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
  · obtain ⟨q, rfl⟩ := h; exact ⟨_, rfl⟩
  · obtain ⟨x, rfl, -⟩ := h; exact ⟨x, rfl⟩
  · obtain ⟨z, rfl, -⟩ := h; exact ⟨_, rfl⟩

theorem boundI_iff (b : Bool × Bool) (x y : Int) : boundI b x y = true ↔ boundRel b x y := by
  rcases b with ⟨_ | _, _ | _⟩ <;> simp [boundI, boundRel]

theorem kindSem_dbl (k : Kind) (x : FloatV 11 52) : kindSem k (.dbl x) ↔ kindF k true = true := by
  cases k <;> simp [kindSem, kindF, strSem]

theorem kindSem_flt (k : Kind) (x : FloatV 8 23) : kindSem k (.flt x) ↔ kindF k false = true := by
  cases k <;> simp [kindSem, kindF, strSem]

theorem fltSem_dbl (b : Bool × Bool) (y : ValOf ℚ) (x : FloatV 11 52) :
    fltSem b y (.dbl x) ↔ x ≠ .nan ∧ (fpOrd true y).any (fun w => boundI b x.ord w) = true := by
  rcases y with q | y | y | ⟨s, _ | t⟩ | c | bs | bs | s | ⟨t, z⟩ | s | n <;>
    simp only [fltSem, fpOrd, Option.any_none, Bool.false_eq_true, and_false, reduceCtorEq,
      false_and, exists_false]
  simp only [ValOf.dbl.injEq, exists_eq_left', FloatV.floatRel_iff (by norm_num : 1 ≤ 11)]
  split_ifs with hy
  · simp [hy]
  · simp [hy, boundI_iff]

theorem fltSem_flt (b : Bool × Bool) (y : ValOf ℚ) (x : FloatV 8 23) :
    fltSem b y (.flt x) ↔ x ≠ .nan ∧ (fpOrd false y).any (fun w => boundI b x.ord w) = true := by
  rcases y with q | y | y | ⟨s, _ | t⟩ | c | bs | bs | s | ⟨t, z⟩ | s | n <;>
    simp only [fltSem, fpOrd, Option.any_none, Bool.false_eq_true, and_false, reduceCtorEq,
      false_and, exists_false]
  simp only [ValOf.flt.injEq, exists_eq_left', FloatV.floatRel_iff (by norm_num : 1 ≤ 8)]
  split_ifs with hy
  · simp [hy]
  · simp [hy, boundI_iff]

theorem kindF_num {k : Kind} (hk : fltKind k = true) (x : ℝ) : ¬ kindSem k (.num x) := by
  cases k <;> simp [fltKind] at hk <;> simp [kindSem]

theorem timeRelB_iff (b : Bool × Bool) (t' : ℚ) (z' : Option Int) (y : ℚ × Option Int) :
    timeRelB b z'.isSome t' y = true ↔ timeRel b (t', z') y := by
  rcases y with ⟨t, _ | z⟩ <;> rcases z' with _ | z' <;> rcases b with ⟨_ | _, _ | _⟩ <;>
    simp [timeRelB, timeRel, timeLt, timeEq, boundB, le_iff_lt_or_eq, @eq_comm ℚ t' t]

theorem kindSem_time (k : Kind) {t : ℚ} {z : Option Int} (h : (decQ t && offOK z) = true) :
    kindSem k (.time t z) ↔ kindT k z.isSome = true := by
  simp only [Bool.and_eq_true] at h
  have hd : IsDecimalQ t := (isDecimalQ_iff t).2 h.1
  rcases z with _ | z <;> cases k <;> simp_all [kindSem, kindT, strSem, offOK]

theorem timeSem_time (b : Bool × Bool) (y : ℚ × Option Int) (t' : ℚ) (z' : Option Int) :
    (∃ t'' z'', (ValOf.time t' z' : Val) = .time t'' z'' ∧ timeRel b (t'', z'') y) ↔
      timeRelB b z'.isSome t' y = true := by
  simp [← timeRelB_iff]

theorem kindT_not_time {k : Kind} (hk : timeKind k = true) {v : Val} (hv : ∀ t z, v ≠ .time t z) :
    ¬ kindSem k v := by
  cases k <;> simp [timeKind] at hk
  · rintro ⟨t, z, h, -⟩; exact hv t z h
  · rintro ⟨t, z, h, -⟩; exact hv t (some z) h

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
  | fltB k bs =>
    simp only [BAtom.supported] at hs
    simp only [BAtom.sem, evalPt, Bool.and_eq_true]
    rw [kindPt_correct]
    refine and_congr_right fun hk => ?_
    rcases w with q | x | x | ⟨s, _ | t⟩ | c | bs' | bs' | s | ⟨t, z⟩ | s | n
    · exact absurd ((kindPt_correct k (.num q)).2 hk) (kindF_num hs _)
    · simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact forall₂_congr fun b _ => fltSem_dbl b.1 b.2 x
    · simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact forall₂_congr fun b _ => fltSem_flt b.1 b.2 x
    all_goals
      exfalso
      cases k <;> simp [fltKind] at hs <;> simp [kindPt] at hk
  | timeB k bs =>
    simp only [BAtom.supported] at hs
    simp only [BAtom.sem, evalPt, Bool.and_eq_true]
    rw [kindPt_correct]
    refine and_congr_right fun hk => ?_
    cases w with
    | time t z =>
      simp only [List.all_eq_true, toVal, ValOf.map]
      exact forall₂_congr fun b _ => timeSem_time b.1 b.2 t z
    | _ =>
      exfalso
      exact kindT_not_time hs (by intro t' z' h; cases h) ((kindPt_correct k _).2 hk)

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

theorem isDecimalR_iff_class (x : ℝ) : IsDecimalR x ↔ numClass x = 0 ∨ numClass x = 1 := by
  constructor
  · intro h
    by_cases h0 : numClass x = 0
    · exact Or.inl h0
    · refine Or.inr (numClass_one.2 ⟨fun hz => h0 (numClass_zero.2 hz), h⟩)
  · rintro (h0 | h1)
    · obtain ⟨z, rfl⟩ := numClass_zero.1 h0
      exact ⟨z, 0, by simp⟩
    · exact (numClass_one.1 h1).2

theorem isRat_iff_class (x : ℝ) : (∃ q : ℚ, x = q) ↔ numClass x ≠ 3 := by
  constructor
  · intro h h3
    exact (numClass_three.1 h3).2.2 h
  · intro h
    by_contra hq
    refine h (numClass_three.2 ⟨fun ⟨z, hz⟩ => hq ⟨z, by rw [hz]; push_cast; rfl⟩,
      fun hd => hq (rat_of_isDecimalR hd), hq⟩)

/-- A kind at a real off the points. -/
theorem kindGap_correct {k : Kind} (hk : supportedKind k = true) (hP : ∀ p ∈ intBounds k, p ∈ P)
    (hx : ∀ q ∈ P, (q : ℝ) ≠ x) :
    kindSem k (.num x) ↔ kindGap k (maxBelow P x) (minAbove P x) (numClass x) = true := by
  cases k <;> simp [supportedKind] at hk <;> simp only [kindSem, kindGap]
  · simp
  · simp only [ValOf.num.injEq, bne_iff_ne, ne_eq]
    exact isRat_iff_class x
  · simp only [ValOf.num.injEq, exists_eq_left', Bool.or_eq_true, beq_iff_eq]
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

theorem boundGapT_correct {b : Bool × Bool} {tz' : Bool} {t' : ℚ} {y : ℚ × Option Int}
    (hy : timeThresh tz' b.1 y ∈ P) (hx : ∀ q ∈ P, (q : ℝ) ≠ (t' : ℝ)) :
    timeRelB b tz' t' y = true ↔
      boundGapT b tz' y (maxBelow P (t' : ℝ)) (minAbove P (t' : ℝ)) = true := by
  unfold boundGapT
  rw [← boundGap_correct hy hx, boundRel_cast]
  have hne : timeThresh tz' b.1 y ≠ t' := fun h => hx _ hy (by exact_mod_cast h)
  unfold timeRelB timeThresh at hne ⊢
  by_cases h1 : (tz' == y.2.isSome) = true
  · simp [h1]
  · rcases b with ⟨_ | _, _ | _⟩ <;> simp only [h1, ↓reduceIte, Bool.false_eq_true, boundB, decide_eq_true_eq] at hne ⊢
    · exact ⟨fun h => by linarith, fun h => by have := lt_of_le_of_ne h hne.symm; linarith⟩
    · exact ⟨fun h => by linarith, fun h => by linarith⟩
    · exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h hne⟩

end GapEval

/-! ## The rest cells -/

theorem kindRest_correct {k : Kind} (hk : supportedKind k = true) {v : Val}
    (hn : ∀ x, v ≠ .num x) (hb : ∀ b, v ≠ .bool b) (hf : ∀ x, v ≠ .dbl x) (hg : ∀ x, v ≠ .flt x)
    (ht : ∀ t z, v ≠ .time t z) :
    kindSem k v ↔ kindRest k (restCell v) = true := by
  rcases v with x | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n
  · exact absurd rfl (hn x)
  · exact absurd rfl (hf x)
  · exact absurd rfl (hg x)
  all_goals try exact absurd rfl (hb _)
  all_goals try exact absurd rfl (ht _ _)
  all_goals cases k <;> simp [supportedKind] at hk <;>
    simp only [kindSem, restCell, strSem] <;> (try split_ifs) <;>
    simp_all [kindRest, isDecimalQ_iff, offOK]

theorem kindSem_invalid_time {k : Kind} (hk : supportedKind k = true) {t : ℚ} {z : Option Int}
    (hok : ¬ (decQ t && offOK z) = true) :
    kindSem k (.time t z) ↔ kindRest k .other = true := by
  simp only [Bool.and_eq_true, ← isDecimalQ_iff, not_and] at hok
  rcases z with _ | z <;> cases k <;> simp [supportedKind] at hk <;>
    simp_all [kindSem, kindRest, strSem, offOK]

theorem evalCell_restCell (a : BAtom) {v : Val} (hf : ∀ x, v ≠ .dbl x) (hg : ∀ x, v ≠ .flt x) :
    evalCell a (restCell v) = match a with
      | .kind k => kindRest k (restCell v)
      | _ => false := by
  have h1 := restCell_ne_pt v
  have h2 := restCell_ne_gap v
  have h3 := restCell_mem hf hg
  generalize restCell v = c at h1 h2 h3 ⊢
  cases c with
  | pt w => exact absurd rfl (h1 w)
  | gap lo hi k => exact absurd rfl (h2 lo hi k)
  | fN d => simp [restCells] at h3
  | fA d p => simp [restCells] at h3
  | fI d lo hi => simp [restCells] at h3
  | tA tz p => simp [restCells] at h3
  | tI tz lo hi => simp [restCells] at h3
  | _ => cases a <;> rfl

/-- A bound facet at an index off the points is a bound on its interval. -/
theorem boundI_gap {P : List Int} {N y z : Int} (hy : y ∈ P) (hzP : z ∉ P) (hz : -N ≤ z ∧ z ≤ N)
    (b : Bool × Bool) : boundI b z y = boundGapI b y (fBelow P N z) (fAbove P N z) := by
  obtain ⟨-, b2, b3⟩ := fBelow_spec (P := P) (N := N) (z := z) (by omega)
  obtain ⟨-, a2, a3⟩ := fAbove_spec (P := P) (N := N) (z := z) (by omega)
  have hne : y ≠ z := fun h => hzP (h ▸ hy)
  rcases b with ⟨_ | _, _ | _⟩ <;> simp only [boundI, boundGapI] <;> rw [Bool.eq_iff_iff] <;>
    simp only [decide_eq_true_eq]
  · constructor
    · intro h; have := a3 y hy (lt_of_le_of_ne h (Ne.symm hne)); exact this
    · intro h; omega
  · constructor
    · intro h; exact a3 y hy h
    · intro h; omega
  · constructor
    · intro h; exact b3 y hy (lt_of_le_of_ne h hne)
    · intro h; omega
  · constructor
    · intro h; exact b3 y hy h
    · intro h; omega

/-! ## The atoms of a list on the cells -/

section Main

variable {as : List BAtom}

theorem nums_sub {a : BAtom} (ha : a ∈ as) {p : ℚ} (hp : p ∈ a.nums) : p ∈ numPts as :=
  List.mem_dedup.2 (List.mem_flatMap.2 ⟨a, ha, hp⟩)

theorem timeThresh_mem_times {k : Kind} {bs : List ((Bool × Bool) × (ℚ × Option Int))}
    {b : (Bool × Bool) × (ℚ × Option Int)} (hb : b ∈ bs) (tz' : Bool) :
    timeThresh tz' b.1.1 b.2 ∈ (BAtom.timeB k bs).times := by
  simp only [BAtom.times, List.mem_flatMap]
  refine ⟨b, hb, ?_⟩
  unfold timeThresh
  split_ifs <;> simp

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
      | fltB k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
        rintro ⟨h1, -⟩
        exact kindF_num hs x h1
      | timeB k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
        rintro ⟨h1, -⟩
        exact kindT_not_time hs (by intro t z h; cases h) h1
    | dbl x =>
      rw [cellOf_dbl hv]
      cases a with
      | kind k =>
        simp only [BAtom.sem]
        rw [kindSem_dbl]
        unfold fCell; split_ifs <;> rfl
      | numR k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
          exact fun h => by obtain ⟨y, hy⟩ := kindSem_num_of hs h.1; cases hy
      | empty => unfold fCell; split_ifs <;> simp [BAtom.sem, evalCell]
      | lit w =>
        have hno : ¬ (ValOf.dbl x = toVal w) := fun he => hv ⟨w, lit_pt ha, he.symm⟩
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;> exact hno
      | fltB k bs =>
        simp only [BAtom.sem, kindSem_dbl, fltSem_dbl]
        unfold fCell
        split_ifs with h1 h2
        · have hx : x = .nan := of_decide_eq_true h1
          simp only [evalCell, Bool.and_eq_true, List.isEmpty_iff]
          refine and_congr_right fun _ => ?_
          constructor
          · intro h
            rcases bs with _ | ⟨b, bs⟩
            · rfl
            · exact absurd hx (h b List.mem_cons_self).1
          · rintro rfl b hb
            cases hb
        · have hx : x ≠ .nan := fun h => h1 (decide_eq_true h)
          simp only [evalCell, Bool.and_eq_true, List.all_eq_true]
          refine and_congr_right fun _ => forall₂_congr fun b _ => ?_
          simp [hx]
        · have hx : x ≠ .nan := fun h => h1 (decide_eq_true h)
          simp only [evalCell, Bool.and_eq_true, List.all_eq_true]
          refine and_congr_right fun _ => forall₂_congr fun b hb => ?_
          rw [and_iff_right hx]
          rcases hy : fpOrd true b.2 with _ | y
          · simp
          · simp only [Option.any_some]
            have hmem : b.2 ∈ (BAtom.fltB k bs).others :=
              List.mem_filter.2 ⟨List.mem_map_of_mem hb, by simp [hy]⟩
            have hop : b.2 ∈ otherPts as :=
              List.mem_dedup.2 (List.mem_append_left _ (List.mem_flatMap.2 ⟨_, ha, hmem⟩))
            have hyP : y ∈ fOrds true as := List.mem_dedup.2 (List.mem_filterMap.2 ⟨b.2, hop, hy⟩)
            rw [boundI_gap hyP h2 (fIdx_mem (d := true) (v := .dbl x) (by simp [fIdx, hx]))]
      | timeB k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
          exact fun h => kindT_not_time hs (by intro t z h; cases h) h.1
    | flt x =>
      rw [cellOf_flt hv]
      cases a with
      | kind k =>
        simp only [BAtom.sem]
        rw [kindSem_flt]
        unfold fCell; split_ifs <;> rfl
      | numR k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
          exact fun h => by obtain ⟨y, hy⟩ := kindSem_num_of hs h.1; cases hy
      | empty => unfold fCell; split_ifs <;> simp [BAtom.sem, evalCell]
      | lit w =>
        have hno : ¬ (ValOf.flt x = toVal w) := fun he => hv ⟨w, lit_pt ha, he.symm⟩
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;> exact hno
      | fltB k bs =>
        simp only [BAtom.sem, kindSem_flt, fltSem_flt]
        unfold fCell
        split_ifs with h1 h2
        · have hx : x = .nan := of_decide_eq_true h1
          simp only [evalCell, Bool.and_eq_true, List.isEmpty_iff]
          refine and_congr_right fun _ => ?_
          constructor
          · intro h
            rcases bs with _ | ⟨b, bs⟩
            · rfl
            · exact absurd hx (h b List.mem_cons_self).1
          · rintro rfl b hb
            cases hb
        · have hx : x ≠ .nan := fun h => h1 (decide_eq_true h)
          simp only [evalCell, Bool.and_eq_true, List.all_eq_true]
          refine and_congr_right fun _ => forall₂_congr fun b _ => ?_
          simp [hx]
        · have hx : x ≠ .nan := fun h => h1 (decide_eq_true h)
          simp only [evalCell, Bool.and_eq_true, List.all_eq_true]
          refine and_congr_right fun _ => forall₂_congr fun b hb => ?_
          rw [and_iff_right hx]
          rcases hy : fpOrd false b.2 with _ | y
          · simp
          · simp only [Option.any_some]
            have hmem : b.2 ∈ (BAtom.fltB k bs).others :=
              List.mem_filter.2 ⟨List.mem_map_of_mem hb, by simp [hy]⟩
            have hop : b.2 ∈ otherPts as :=
              List.mem_dedup.2 (List.mem_append_left _ (List.mem_flatMap.2 ⟨_, ha, hmem⟩))
            have hyP : y ∈ fOrds false as := List.mem_dedup.2 (List.mem_filterMap.2 ⟨b.2, hop, hy⟩)
            rw [boundI_gap hyP h2 (fIdx_mem (d := false) (v := .flt x) (by simp [fIdx, hx]))]
      | timeB k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem]
        unfold fCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
          exact fun h => kindT_not_time hs (by intro t z h; cases h) h.1
    | time t z =>
      by_cases hok : (decQ t && offOK z) = true
      · rw [cellOf_time hv hok]
        cases a with
        | kind k =>
          simp only [BAtom.sem]
          rw [kindSem_time k hok]
          unfold tCell; split_ifs <;> rfl
        | numR k bs =>
          simp only [BAtom.supported] at hs
          simp only [BAtom.sem]
          unfold tCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
            exact fun h => by obtain ⟨y, hy⟩ := kindSem_num_of hs h.1; cases hy
        | empty => unfold tCell; split_ifs <;> simp [BAtom.sem, evalCell]
        | lit w =>
          have hno : ¬ (ValOf.time t z = toVal w) := fun he => hv ⟨w, lit_pt ha, he.symm⟩
          simp only [BAtom.sem]
          unfold tCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;> exact hno
        | fltB k bs =>
          simp only [BAtom.supported] at hs
          simp only [BAtom.sem]
          unfold tCell; split_ifs <;> simp only [evalCell, Bool.false_eq_true, iff_false] <;>
            (rintro ⟨h1, -⟩; cases k <;> simp [fltKind] at hs <;> simp [kindSem] at h1)
        | timeB k bs =>
          simp only [BAtom.sem, kindSem_time k hok, timeSem_time]
          unfold tCell
          split_ifs with h1
          · simp [evalCell]
          · simp only [evalCell, Bool.and_eq_true, List.all_eq_true]
            refine and_congr_right fun _ => forall₂_congr fun b hb => ?_
            have hx : ∀ q ∈ timePts as, (q : ℝ) ≠ (t : ℝ) := fun q hq h => h1 (by
              have : q = t := by exact_mod_cast h
              exact this ▸ hq)
            have hy : timeThresh z.isSome b.1.1 b.2 ∈ timePts as :=
              List.mem_dedup.2 (List.mem_flatMap.2 ⟨_, ha, timeThresh_mem_times hb z.isSome⟩)
            exact boundGapT_correct hy hx
      · have hht : isValidTime (.time t z) = false := Bool.eq_false_iff.2 hok
        rw [cellOf_rest hv (by intro x h; cases h) (by intro x h; cases h) (by intro x h; cases h) hht]
        simp only [restCell]
        cases a with
        | kind k => exact kindSem_invalid_time hs hok
        | numR k bs =>
          simp only [BAtom.supported] at hs
          simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
          rintro ⟨h1, -⟩
          obtain ⟨x, hx⟩ := kindSem_num_of hs h1
          cases hx
        | empty => simp [BAtom.sem, evalCell]
        | lit w =>
          simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
          intro he
          exact hv ⟨w, lit_pt ha, he.symm⟩
        | fltB k bs =>
          simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
          rintro ⟨h1, -⟩
          simp only [BAtom.supported] at hs
          cases k <;> simp [fltKind] at hs <;> simp [kindSem] at h1
        | timeB k bs =>
          simp only [BAtom.sem, evalCell, Bool.false_eq_true, iff_false]
          rintro ⟨h1, -⟩
          simp only [BAtom.supported] at hs
          have hk : supportedKind k = true := by cases k <;> simp_all [timeKind, supportedKind]
          have hf := (kindSem_invalid_time hk hok).1 h1
          cases k <;> simp [timeKind] at hs <;> simp [kindRest] at hf
    | _ =>
      rw [cellOf_rest hv (by intro x h; cases h) (by intro x h; cases h) (by intro x h; cases h) rfl,
        evalCell_restCell _ (by intro x h; cases h) (by intro x h; cases h)]
      cases a with
      | kind k =>
        refine kindRest_correct hs (by intro x h; cases h) ?_
          (by intro x h; cases h) (by intro x h; cases h) (by intro t z h; cases h)
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
      | fltB k bs =>
        simp only [BAtom.sem, Bool.false_eq_true, iff_false]
        rintro ⟨h1, -⟩
        simp only [BAtom.supported] at hs
        cases k <;> simp [fltKind] at hs <;> simp [kindSem] at h1
      | timeB k bs =>
        simp only [BAtom.supported] at hs
        simp only [BAtom.sem, Bool.false_eq_true, iff_false]
        rintro ⟨h1, -⟩
        exact kindT_not_time hs (by intro t z h; cases h) h1

end Main

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.evalCell_correct
