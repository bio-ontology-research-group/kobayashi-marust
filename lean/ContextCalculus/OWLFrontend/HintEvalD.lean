import ContextCalculus.OWLFrontend.HintEval

/-!
# Evaluating data and counting constructors over the core (stage H5, item 2)

`docs/V1.7.0-C5-HINT-ROUTE.md`, section 13. `CKX k` extends the core
knowledge `CK k` by the data of the core elements: for a data property and
a core element a list of value numbers and a flag (the list is exact), and
for a data range, a core element and a value number a three-valued
membership. `CKXSpec K I f val` states that the table is true of the model
`I`, with `val w i` the value number `i` of core element `w`: the listed
values are values of the property, an exact list holds every value,
different numbers listed at one element are different values, and the
membership answers are right.

* `evD K C w`: `ev` extended by `ObjectMinCardinality`,
  `ObjectMaxCardinality`, `ObjectExactCardinality` (counting the listed
  successors, which are distinct elements), `DataSomeValuesFrom`,
  `DataAllValuesFrom`, `DataHasValue`, `DataMinCardinality`,
  `DataMaxCardinality`, `DataExactCardinality`. `evD_sound`.
* `refuteD K ax`: `refute`, or a violation found with `evD` (class axioms,
  domains, ranges, class assertions) or on the data: `SubDataPropertyOf`,
  `EquivalentDataProperties`, `DisjointDataProperties`,
  `DataPropertyDomain`, `DataPropertyRange`, `FunctionalDataProperty`,
  `DataPropertyAssertion`, `NegativeDataPropertyAssertion`.
  `refuteD_sound`.
-/

namespace ContextCalculus.OWLFrontend

open ContextCalculus.OWL ContextCalculus.OWL.Datatypes

/-- The core knowledge with data. -/
structure CKX (k : Nat) extends CK k where
  /-- the value numbers of a data property at a core element, and whether
  the list is exact -/
  dv : DataProp → Fin k → List Nat × Bool
  /-- three-valued membership of value number `i` of `w` in a data range -/
  dr : DataRange → Fin k → Nat → Option Bool

variable {k : Nat}

/-- The table with data is true of `I`, with `val w i` the value number `i`
of the core element `w`. -/
structure CKXSpec {DM : DatatypeMap} {Dom : Type} (K : CKX k) (I : Interp DM Dom) (f : Fin k → Dom)
    (val : Fin k → Nat → DM.Val) : Prop where
  base : CKSpec K.toCK I f
  dpos : ∀ p w i, i ∈ (K.dv p w).1 → I.dp p (f w) (val w i)
  dneg : ∀ p w x, (K.dv p w).2 = true → I.dp p (f w) x → ∃ i ∈ (K.dv p w).1, x = val w i
  dinj : ∀ p p' w i j, i ∈ (K.dv p w).1 → j ∈ (K.dv p' w).1 → val w i = val w j → i = j
  dr : ∀ R w i b, K.dr R w i = some b → (∃ p, i ∈ (K.dv p w).1) →
    (I.drExt R (val w i) ↔ b = true)

/-! ## Counting -/

/-- At least `n`: `t` items hold, at most `nf` may hold, `ex`: the count is exact. -/
def minV (n t nf : Nat) (ex : Bool) : Option Bool :=
  if n ≤ t then some true else if ex && decide (nf < n) then some false else none

def maxV (n t nf : Nat) (ex : Bool) : Option Bool :=
  if ex && decide (nf ≤ n) then some true else if n < t then some false else none

theorem atLeast_of_filter {α β : Type} (L : List α) (hL : L.Nodup) (φ : α → β)
    (hφ : ∀ a ∈ L, ∀ b ∈ L, φ a = φ b → a = b) (good : α → Bool) (P : β → Prop)
    (hP : ∀ a ∈ L, good a = true → P (φ a)) (n : Nat) (hn : n ≤ (L.filter good).length) :
    AtLeast n P := by
  have hnd : ((L.filter good).map φ).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb he => hφ a (List.mem_of_mem_filter ha) b
      (List.mem_of_mem_filter hb) he) (hL.filter _)
  refine ⟨((L.filter good).map φ).take n, hnd.sublist (List.take_sublist _ _), ?_, fun y hy => ?_⟩
  · rw [List.length_take, List.length_map]; omega
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hy)
    exact hP a (List.mem_of_mem_filter ha) (List.mem_filter.1 ha).2

theorem atMost_of_cover {α β : Type} (L : List α) (φ : α → β) (good : α → Bool) (P : β → Prop)
    (hcov : ∀ y, P y → ∃ a ∈ L, good a = true ∧ φ a = y) : AtMost (L.filter good).length P := by
  intro l hl hP
  have hsub : l ⊆ (L.filter good).map φ := by
    intro y hy
    obtain ⟨a, ha, hg, rfl⟩ := hcov y (hP y hy)
    exact List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, hg⟩, rfl⟩
  have := (hl.subperm hsub).length_le
  rwa [List.length_map] at this

/-- The two directions of a count. -/
theorem minV_sound {α β : Type} (L : List α) (hL : L.Nodup) (φ : α → β)
    (hφ : ∀ a ∈ L, ∀ b ∈ L, φ a = φ b → a = b) (gt gnf : α → Bool) (P : β → Prop)
    (hP : ∀ a ∈ L, gt a = true → P (φ a)) (ex : Bool)
    (hcov : ex = true → ∀ y, P y → ∃ a ∈ L, gnf a = true ∧ φ a = y) (n : Nat) :
    (minV n (L.filter gt).length (L.filter gnf).length ex = some true → AtLeast n P) ∧
    (minV n (L.filter gt).length (L.filter gnf).length ex = some false → ¬ AtLeast n P) := by
  unfold minV
  split_ifs with h1 h2
  · exact ⟨fun _ => atLeast_of_filter L hL φ hφ gt P hP n h1, fun h => (nomatch h)⟩
  · refine ⟨fun h => (nomatch h), fun _ ⟨l, hl, hlen, hlP⟩ => ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at h2
    have := atMost_of_cover L φ gnf P (hcov h2.1) l hl hlP
    omega
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem maxV_sound {α β : Type} (L : List α) (hL : L.Nodup) (φ : α → β)
    (hφ : ∀ a ∈ L, ∀ b ∈ L, φ a = φ b → a = b) (gt gnf : α → Bool) (P : β → Prop)
    (hP : ∀ a ∈ L, gt a = true → P (φ a)) (ex : Bool)
    (hcov : ex = true → ∀ y, P y → ∃ a ∈ L, gnf a = true ∧ φ a = y) (n : Nat) :
    (maxV n (L.filter gt).length (L.filter gnf).length ex = some true → AtMost n P) ∧
    (maxV n (L.filter gt).length (L.filter gnf).length ex = some false → ¬ AtMost n P) := by
  unfold maxV
  split_ifs with h1 h2
  · refine ⟨fun _ l hl hlP => ?_, fun h => (nomatch h)⟩
    rw [Bool.and_eq_true, decide_eq_true_eq] at h1
    have := atMost_of_cover L φ gnf P (hcov h1.1) l hl hlP
    omega
  · refine ⟨fun h => (nomatch h), fun _ hm => ?_⟩
    obtain ⟨l, hl, hlen, hlP⟩ := atLeast_of_filter L hL φ hφ gt P hP (n + 1) h2
    have := hm l hl hlP
    omega
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem andV_sound {a b : Option Bool} {P Q : Prop} (ha : (a = some true → P) ∧ (a = some false → ¬ P))
    (hb : (b = some true → Q) ∧ (b = some false → ¬ Q)) :
    (andV a b = some true → P ∧ Q) ∧ (andV a b = some false → ¬ (P ∧ Q)) := by
  refine ⟨fun h => ?_, fun h hpq => ?_⟩
  · obtain ⟨h1, h2⟩ := andV_true h; exact ⟨ha.1 h1, hb.1 h2⟩
  · rcases andV_false h with h1 | h2
    · exact ha.2 h1 hpq.1
    · exact hb.2 h2 hpq.2

/-! ## Evaluation with data and counting -/

/-- The successors of `p` at `w` without repetitions, the count of those
where `e` is true and of those where it is not false. -/
def cntO (K : CKX k) (p : ObjProp) (w : Fin k) (e : Fin k → Option Bool) : Nat × Nat × Bool :=
  let s := K.succ p w
  let L := s.1.dedup
  ((L.filter fun v => e v == some true).length, (L.filter fun v => e v != some false).length,
    s.2 && K.surj)

/-- The same for the values of a data property in a data range. -/
def cntD (K : CKX k) (p : DataProp) (R : DataRange) (w : Fin k) : Nat × Nat × Bool :=
  let s := K.dv p w
  let L := s.1.dedup
  ((L.filter fun i => K.dr R w i == some true).length,
    (L.filter fun i => K.dr R w i != some false).length, s.2)

/-- Some value of `p` at `w` lies in `R` / every value lies in `R`. -/
def dsomeV (K : CKX k) (p : DataProp) (R : DataRange) (w : Fin k) : Option Bool :=
  let s := K.dv p w
  if s.1.any (fun i => K.dr R w i == some true) then some true
  else if s.2 && s.1.all (fun i => K.dr R w i == some false) then some false
  else none

def dallV (K : CKX k) (p : DataProp) (R : DataRange) (w : Fin k) : Option Bool :=
  let s := K.dv p w
  if s.1.any (fun i => K.dr R w i == some false) then some false
  else if s.2 && s.1.all (fun i => K.dr R w i == some true) then some true
  else none

mutual

/-- **Three-valued evaluation with data and counting.** -/
def evD (K : CKX k) : ClassExpr → Fin k → Option Bool
  | .and cs, w => evDAnd K cs w
  | .or cs, w => evDOr K cs w
  | .not c, w => (evD K c w).map (!·)
  | .some p c, w =>
    let s := K.succ p w
    if s.1.any (fun v => evD K c v == some true) then some true
    else if s.2 && K.surj && s.1.all (fun v => evD K c v == some false) then some false
    else none
  | .all p c, w =>
    let s := K.succ p w
    if s.1.any (fun v => evD K c v == some false) then some false
    else if s.2 && K.surj && s.1.all (fun v => evD K c v == some true) then some true
    else none
  | .min n p c, w =>
    let t := cntO K p w (fun v => evD K c v)
    minV n t.1 t.2.1 t.2.2
  | .max n p c, w =>
    let t := cntO K p w (fun v => evD K c v)
    maxV n t.1 t.2.1 t.2.2
  | .exact n p c, w =>
    let t := cntO K p w (fun v => evD K c v)
    andV (minV n t.1 t.2.1 t.2.2) (maxV n t.1 t.2.1 t.2.2)
  | .dataSome p R, w => dsomeV K p R w
  | .dataAll p R, w => dallV K p R w
  | .dataHasValue p l, w => dsomeV K p (.oneOf [l]) w
  | .dataMin n p R, w => let t := cntD K p R w; minV n t.1 t.2.1 t.2.2
  | .dataMax n p R, w => let t := cntD K p R w; maxV n t.1 t.2.1 t.2.2
  | .dataExact n p R, w =>
    let t := cntD K p R w
    andV (minV n t.1 t.2.1 t.2.2) (maxV n t.1 t.2.1 t.2.2)
  | .cls A, w => ev K.toCK (.cls A) w
  | .thing, w => ev K.toCK .thing w
  | .nothing, w => ev K.toCK .nothing w
  | .oneOf as, w => ev K.toCK (.oneOf as) w
  | .hasValue p a, w => ev K.toCK (.hasValue p a) w
  | .hasSelf p, w => ev K.toCK (.hasSelf p) w

def evDAnd (K : CKX k) : List ClassExpr → Fin k → Option Bool
  | [], _ => some true
  | c :: cs, w => andV (evD K c w) (evDAnd K cs w)

def evDOr (K : CKX k) : List ClassExpr → Fin k → Option Bool
  | [], _ => some false
  | c :: cs, w => orV (evD K c w) (evDOr K cs w)

end

section Sound

variable {DM : DatatypeMap} {Dom : Type} {K : CKX k} {I : Interp DM Dom} {f : Fin k → Dom}
  {val : Fin k → Nat → DM.Val}

theorem cntO_sound (hK : CKXSpec K I f val) (p : ObjProp) (c : ClassExpr) (w : Fin k)
    (e : Fin k → Option Bool)
    (ih : ∀ v, (e v = some true → I.ext c (f v)) ∧ (e v = some false → ¬ I.ext c (f v))) (n : Nat) :
    (minV n (cntO K p w e).1 (cntO K p w e).2.1 (cntO K p w e).2.2 = some true →
        AtLeast n fun y => I.prop p (f w) y ∧ I.ext c y) ∧
    (minV n (cntO K p w e).1 (cntO K p w e).2.1 (cntO K p w e).2.2 = some false →
        ¬ AtLeast n fun y => I.prop p (f w) y ∧ I.ext c y) ∧
    (maxV n (cntO K p w e).1 (cntO K p w e).2.1 (cntO K p w e).2.2 = some true →
        AtMost n fun y => I.prop p (f w) y ∧ I.ext c y) ∧
    (maxV n (cntO K p w e).1 (cntO K p w e).2.1 (cntO K p w e).2.2 = some false →
        ¬ AtMost n fun y => I.prop p (f w) y ∧ I.ext c y) := by
  have hb := hK.base
  have hP : ∀ v ∈ (K.succ p w).1.dedup, (e v == some true) = true →
      I.prop p (f w) (f v) ∧ I.ext c (f v) := fun v hv he =>
    ⟨hb.pos p w v (List.mem_dedup.1 hv), (ih v).1 (beq_iff_eq.1 he)⟩
  have hcov : ((K.succ p w).2 && K.surj) = true → ∀ y, (I.prop p (f w) y ∧ I.ext c y) →
      ∃ v ∈ (K.succ p w).1.dedup, (e v != some false) = true ∧ f v = y := by
    intro hs y ⟨hy, hc⟩
    rw [Bool.and_eq_true] at hs
    obtain ⟨v, rfl⟩ := hb.surj hs.2 y
    refine ⟨v, List.mem_dedup.2 (hb.neg p w v hs.1 hy), ?_, rfl⟩
    rw [bne_iff_ne, ne_eq]
    exact fun h => (ih v).2 h hc
  have hφ : ∀ a ∈ (K.succ p w).1.dedup, ∀ b ∈ (K.succ p w).1.dedup, f a = f b → a = b :=
    fun a _ b _ h => hb.inj h
  obtain ⟨m1, m2⟩ := minV_sound _ (List.nodup_dedup _) f hφ _ _ _ hP _ hcov n
  obtain ⟨x1, x2⟩ := maxV_sound _ (List.nodup_dedup _) f hφ _ _ _ hP _ hcov n
  exact ⟨m1, m2, x1, x2⟩

theorem cntD_sound (hK : CKXSpec K I f val) (p : DataProp) (R : DataRange) (w : Fin k) (n : Nat) :
    (minV n (cntD K p R w).1 (cntD K p R w).2.1 (cntD K p R w).2.2 = some true →
        AtLeast n fun x => I.dp p (f w) x ∧ I.drExt R x) ∧
    (minV n (cntD K p R w).1 (cntD K p R w).2.1 (cntD K p R w).2.2 = some false →
        ¬ AtLeast n fun x => I.dp p (f w) x ∧ I.drExt R x) ∧
    (maxV n (cntD K p R w).1 (cntD K p R w).2.1 (cntD K p R w).2.2 = some true →
        AtMost n fun x => I.dp p (f w) x ∧ I.drExt R x) ∧
    (maxV n (cntD K p R w).1 (cntD K p R w).2.1 (cntD K p R w).2.2 = some false →
        ¬ AtMost n fun x => I.dp p (f w) x ∧ I.drExt R x) := by
  have hP : ∀ i ∈ (K.dv p w).1.dedup, (K.dr R w i == some true) = true →
      I.dp p (f w) (val w i) ∧ I.drExt R (val w i) := fun i hi he =>
    ⟨hK.dpos p w i (List.mem_dedup.1 hi),
      (hK.dr R w i true (beq_iff_eq.1 he) ⟨p, List.mem_dedup.1 hi⟩).2 rfl⟩
  have hcov : (K.dv p w).2 = true → ∀ x, (I.dp p (f w) x ∧ I.drExt R x) →
      ∃ i ∈ (K.dv p w).1.dedup, (K.dr R w i != some false) = true ∧ val w i = x := by
    intro hs x ⟨hx, hr⟩
    obtain ⟨i, hi, rfl⟩ := hK.dneg p w x hs hx
    refine ⟨i, List.mem_dedup.2 hi, ?_, rfl⟩
    rw [bne_iff_ne, ne_eq]
    intro h
    exact absurd ((hK.dr R w i false h ⟨p, hi⟩).1 hr) (by simp)
  have hφ : ∀ a ∈ (K.dv p w).1.dedup, ∀ b ∈ (K.dv p w).1.dedup, val w a = val w b → a = b :=
    fun a ha b hb h => hK.dinj p p w a b (List.mem_dedup.1 ha) (List.mem_dedup.1 hb) h
  obtain ⟨m1, m2⟩ := minV_sound _ (List.nodup_dedup _) (val w) hφ _ _ _ hP _ hcov n
  obtain ⟨x1, x2⟩ := maxV_sound _ (List.nodup_dedup _) (val w) hφ _ _ _ hP _ hcov n
  exact ⟨m1, m2, x1, x2⟩

theorem dsomeV_sound (hK : CKXSpec K I f val) (p : DataProp) (R : DataRange) (w : Fin k) :
    (dsomeV K p R w = some true → ∃ x, I.dp p (f w) x ∧ I.drExt R x) ∧
    (dsomeV K p R w = some false → ¬ ∃ x, I.dp p (f w) x ∧ I.drExt R x) := by
  unfold dsomeV
  dsimp only
  split_ifs with h1 h2
  · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
    obtain ⟨i, hi, he⟩ := List.any_eq_true.1 h1
    exact ⟨_, hK.dpos p w i hi, (hK.dr R w i true (beq_iff_eq.1 he) ⟨p, hi⟩).2 rfl⟩
  · refine ⟨fun h => (nomatch h), fun _ ⟨x, hx, hr⟩ => ?_⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    obtain ⟨i, hi, rfl⟩ := hK.dneg p w x h2.1 hx
    exact absurd ((hK.dr R w i false (beq_iff_eq.1 (h2.2 i hi)) ⟨p, hi⟩).1 hr) (by simp)
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem dallV_sound (hK : CKXSpec K I f val) (p : DataProp) (R : DataRange) (w : Fin k) :
    (dallV K p R w = some true → ∀ x, I.dp p (f w) x → I.drExt R x) ∧
    (dallV K p R w = some false → ¬ ∀ x, I.dp p (f w) x → I.drExt R x) := by
  unfold dallV
  dsimp only
  split_ifs with h1 h2
  · refine ⟨fun h => (nomatch h), fun _ hall => ?_⟩
    obtain ⟨i, hi, he⟩ := List.any_eq_true.1 h1
    exact absurd ((hK.dr R w i false (beq_iff_eq.1 he) ⟨p, hi⟩).1 (hall _ (hK.dpos p w i hi)))
      (by simp)
  · refine ⟨fun _ x hx => ?_, fun h => (nomatch h)⟩
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    obtain ⟨i, hi, rfl⟩ := hK.dneg p w x h2.1 hx
    exact (hK.dr R w i true (beq_iff_eq.1 (h2.2 i hi)) ⟨p, hi⟩).2 rfl
  · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem drExt_oneOf_single (l : Literal) (x : DM.Val) :
    I.drExt (.oneOf [l]) x ↔ DM.literal l = some x := by
  show DataRange.ext DM I.dtype (.oneOf [l]) x ↔ _
  rw [DataRange.ext]
  simp

theorem ev_of_evD_default (hK : CKXSpec K I f val) (c : ClassExpr) (w : Fin k) :
    (ev K.toCK c w = some true → I.ext c (f w)) ∧ (ev K.toCK c w = some false → ¬ I.ext c (f w)) :=
  ev_sound hK.base c w

mutual

/-- **Soundness of the evaluation with data and counting.** -/
theorem evD_sound (hK : CKXSpec K I f val) : ∀ (c : ClassExpr) (w : Fin k),
    (evD K c w = some true → I.ext c (f w)) ∧ (evD K c w = some false → ¬ I.ext c (f w))
  | .and cs, w => by
    rw [evD, Interp.ext]
    obtain ⟨h1, h2⟩ := evDAnd_sound hK cs w
    exact ⟨fun h c hc => h1 h c hc, fun h hall => by
      obtain ⟨c, hc, hn⟩ := h2 h; exact hn (hall c hc)⟩
  | .or cs, w => by
    rw [evD, Interp.ext]
    obtain ⟨h1, h2⟩ := evDOr_sound hK cs w
    exact ⟨fun h => by obtain ⟨c, hc, he⟩ := h1 h; exact ⟨c, hc, he⟩,
      fun h ⟨c, hc, he⟩ => h2 h c hc he⟩
  | .not c, w => by
    rw [evD, Interp.ext]
    obtain ⟨h1, h2⟩ := evD_sound hK c w
    constructor
    · intro h
      cases hv : evD K c w with
      | none => rw [hv] at h; cases h
      | some b => rw [hv] at h; cases b <;> simp_all
    · intro h
      cases hv : evD K c w with
      | none => rw [hv] at h; cases h
      | some b => rw [hv] at h; cases b <;> simp_all
  | .some p c, w => by
    have ih := fun v => evD_sound hK c v
    have hb := hK.base
    rw [evD, Interp.ext]
    dsimp only
    split_ifs with h1 h2
    · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
      obtain ⟨v, hv, he⟩ := List.any_eq_true.1 h1
      exact ⟨f v, hb.pos p w v hv, (ih v).1 (beq_iff_eq.1 he)⟩
    · refine ⟨fun h => (nomatch h), fun _ => ?_⟩
      simp only [Bool.and_eq_true, List.all_eq_true] at h2
      obtain ⟨⟨hex, hs⟩, hall⟩ := h2
      rintro ⟨y, hy, hc⟩
      obtain ⟨v, rfl⟩ := hb.surj hs y
      exact (ih v).2 (beq_iff_eq.1 (hall v (hb.neg p w v hex hy))) hc
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .all p c, w => by
    have ih := fun v => evD_sound hK c v
    have hb := hK.base
    rw [evD, Interp.ext]
    dsimp only
    split_ifs with h1 h2
    · refine ⟨fun h => (nomatch h), fun _ => ?_⟩
      obtain ⟨v, hv, he⟩ := List.any_eq_true.1 h1
      exact fun hall => (ih v).2 (beq_iff_eq.1 he) (hall _ (hb.pos p w v hv))
    · refine ⟨fun _ => ?_, fun h => (nomatch h)⟩
      simp only [Bool.and_eq_true, List.all_eq_true] at h2
      obtain ⟨⟨hex, hs⟩, hall⟩ := h2
      intro y hy
      obtain ⟨v, rfl⟩ := hb.surj hs y
      exact (ih v).1 (beq_iff_eq.1 (hall v (hb.neg p w v hex hy)))
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | .min n p c, w => by
    rw [evD, Interp.ext]
    obtain ⟨m1, m2, -, -⟩ := cntO_sound hK p c w _ (fun v => evD_sound hK c v) n
    exact ⟨m1, m2⟩
  | .max n p c, w => by
    rw [evD, Interp.ext]
    obtain ⟨-, -, x1, x2⟩ := cntO_sound hK p c w _ (fun v => evD_sound hK c v) n
    exact ⟨x1, x2⟩
  | .exact n p c, w => by
    rw [evD, Interp.ext]
    obtain ⟨m1, m2, x1, x2⟩ := cntO_sound hK p c w _ (fun v => evD_sound hK c v) n
    exact andV_sound ⟨m1, m2⟩ ⟨x1, x2⟩
  | .dataSome p R, w => by
    rw [evD, Interp.ext]
    exact dsomeV_sound hK p R w
  | .dataAll p R, w => by
    rw [evD, Interp.ext]
    exact dallV_sound hK p R w
  | .dataHasValue p l, w => by
    rw [evD, Interp.ext]
    obtain ⟨h1, h2⟩ := dsomeV_sound hK p (.oneOf [l]) w
    refine ⟨fun h => ?_, fun h ⟨x, hl, hx⟩ => h2 h ⟨x, hx, (drExt_oneOf_single l x).2 hl⟩⟩
    obtain ⟨x, hx, hr⟩ := h1 h
    exact ⟨x, (drExt_oneOf_single l x).1 hr, hx⟩
  | .dataMin n p R, w => by
    rw [evD, Interp.ext]
    obtain ⟨m1, m2, -, -⟩ := cntD_sound hK p R w n
    exact ⟨m1, m2⟩
  | .dataMax n p R, w => by
    rw [evD, Interp.ext]
    obtain ⟨-, -, x1, x2⟩ := cntD_sound hK p R w n
    exact ⟨x1, x2⟩
  | .dataExact n p R, w => by
    rw [evD, Interp.ext]
    obtain ⟨m1, m2, x1, x2⟩ := cntD_sound hK p R w n
    exact andV_sound ⟨m1, m2⟩ ⟨x1, x2⟩
  | .cls A, w => by rw [evD]; exact ev_sound hK.base _ w
  | .thing, w => by rw [evD]; exact ev_sound hK.base _ w
  | .nothing, w => by rw [evD]; exact ev_sound hK.base _ w
  | .oneOf as, w => by rw [evD]; exact ev_sound hK.base _ w
  | .hasValue p a, w => by rw [evD]; exact ev_sound hK.base _ w
  | .hasSelf p, w => by rw [evD]; exact ev_sound hK.base _ w

theorem evDAnd_sound (hK : CKXSpec K I f val) : ∀ (cs : List ClassExpr) (w : Fin k),
    (evDAnd K cs w = some true → ∀ c ∈ cs, I.ext c (f w)) ∧
    (evDAnd K cs w = some false → ∃ c ∈ cs, ¬ I.ext c (f w))
  | [], w => by rw [evDAnd]; exact ⟨fun _ c hc => absurd hc List.not_mem_nil, fun h => (nomatch h)⟩
  | c :: cs, w => by
    rw [evDAnd]
    obtain ⟨h1, h2⟩ := evD_sound hK c w
    obtain ⟨h3, h4⟩ := evDAnd_sound hK cs w
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨ha, hb⟩ := andV_true h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h1 ha
      · exact h3 hb d hd
    · rcases andV_false h with ha | hb
      · exact ⟨c, List.mem_cons_self, h2 ha⟩
      · obtain ⟨d, hd, hn⟩ := h4 hb
        exact ⟨d, List.mem_cons_of_mem _ hd, hn⟩

theorem evDOr_sound (hK : CKXSpec K I f val) : ∀ (cs : List ClassExpr) (w : Fin k),
    (evDOr K cs w = some true → ∃ c ∈ cs, I.ext c (f w)) ∧
    (evDOr K cs w = some false → ∀ c ∈ cs, ¬ I.ext c (f w))
  | [], w => by rw [evDOr]; exact ⟨fun h => (nomatch h), fun _ c hc => absurd hc List.not_mem_nil⟩
  | c :: cs, w => by
    rw [evDOr]
    obtain ⟨h1, h2⟩ := evD_sound hK c w
    obtain ⟨h3, h4⟩ := evDOr_sound hK cs w
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases orV_true h with ha | hb
      · exact ⟨c, List.mem_cons_self, h1 ha⟩
      · obtain ⟨d, hd, he⟩ := h3 hb
        exact ⟨d, List.mem_cons_of_mem _ hd, he⟩
    · obtain ⟨ha, hb⟩ := orV_false h
      intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact h2 ha
      · exact h4 hb d hd

end

end Sound

/-! ## Refuting axioms with data -/

/-- Some pair of the listed classes shares a core element (with `evD`). -/
def refDisjCD (K : CKX k) : List ClassExpr → Bool
  | [] => false
  | c :: cs => cs.any (fun d => (List.finRange k).any fun w =>
      evD K c w == some true && evD K d w == some true) || refDisjCD K cs

/-- `p ⊑ q` fails on the core: a `p`-value that is exactly no `q`-value. -/
def refSubDP (K : CKX k) (p q : DataProp) : Bool :=
  (List.finRange k).any fun w => (K.dv q w).2 && (K.dv p w).1.any fun i => !(K.dv q w).1.contains i

/-- Some pair of the listed data properties shares a value at a core element. -/
def refDisjDP (K : CKX k) : List DataProp → Bool
  | [] => false
  | p :: ps => ps.any (fun q => (List.finRange k).any fun w =>
      (K.dv p w).1.any fun i => (K.dv q w).1.contains i) || refDisjDP K ps

/-- The violations found with `evD` or on the data. -/
def refuteX (K : CKX k) : Axiom → Bool
  | .subClassOf c d => (List.finRange k).any fun w => evD K c w == some true && evD K d w == some false
  | .equivalentClasses cs => cs.any fun c => cs.any fun d =>
      (List.finRange k).any fun w => evD K c w == some true && evD K d w == some false
  | .disjointClasses cs => refDisjCD K cs
  | .domain r c => (List.finRange k).any fun w => !(K.succ r w).1.isEmpty && evD K c w == some false
  | .range r c => (List.finRange k).any fun w => (K.succ r w).1.any fun v => evD K c v == some false
  | .classAssertion c a => match indOf K.toCK a with
    | some w => evD K c w == some false
    | none => false
  | .subDataPropertyOf p q => refSubDP K p q
  | .equivalentDataProperties ps => ps.any fun p => ps.any fun q => refSubDP K p q
  | .disjointDataProperties ps => refDisjDP K ps
  | .dataDomain p c => (List.finRange k).any fun w => !(K.dv p w).1.isEmpty && evD K c w == some false
  | .dataRange p R => (List.finRange k).any fun w => (K.dv p w).1.any fun i => K.dr R w i == some false
  | .functionalData p => (List.finRange k).any fun w =>
      let L := (K.dv p w).1
      L.any fun i => L.any fun j => i != j
  | .dataPropertyAssertion p a l => match indOf K.toCK a with
    | some w => (K.dv p w).2 && (K.dv p w).1.all fun i => K.dr (.oneOf [l]) w i == some false
    | none => false
  | .negativeDataPropertyAssertion p a l => match indOf K.toCK a with
    | some w => (K.dv p w).1.any fun i => K.dr (.oneOf [l]) w i == some true
    | none => false
  | _ => false

/-- **The model violates `ax`**, read off the core, with data and counting. -/
def refuteD (K : CKX k) (ax : Axiom) : Bool := refute K.toCK ax || refuteX K ax

section RefuteSound

variable {DM : DatatypeMap} {Dom : Type} {K : CKX k} {I : Interp DM Dom} {f : Fin k → Dom}
  {val : Fin k → Nat → DM.Val}

theorem refDisjCD_sound (hK : CKXSpec K I f val) : ∀ (cs : List ClassExpr), refDisjCD K cs = true →
    ¬ cs.Pairwise fun c d => ∀ x, ¬ (I.ext c x ∧ I.ext d x)
  | [], h, _ => by cases h
  | c :: cs, h, hp => by
    rw [refDisjCD, Bool.or_eq_true] at h
    rw [List.pairwise_cons] at hp
    rcases h with h | h
    · obtain ⟨d, hd, h⟩ := List.any_eq_true.1 h
      obtain ⟨w, -, h⟩ := List.any_eq_true.1 h
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
      exact hp.1 d hd (f w) ⟨(evD_sound hK c w).1 h.1, (evD_sound hK d w).1 h.2⟩
    · exact refDisjCD_sound hK cs h hp.2

theorem refSubDP_sound (hK : CKXSpec K I f val) {p q : DataProp} (h : refSubDP K p q = true) :
    ¬ ∀ x v, I.dp p x v → I.dp q x v := by
  intro hall
  simp only [refSubDP, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨w, -, hex, i, hi, hn⟩ := h
  obtain ⟨j, hj, he⟩ := hK.dneg q w _ hex (hall _ _ (hK.dpos p w i hi))
  exact hn (hK.dinj p q w i j hi hj he ▸ hj)

theorem refDisjDP_sound (hK : CKXSpec K I f val) : ∀ (ps : List DataProp), refDisjDP K ps = true →
    ¬ ps.Pairwise fun p q => ∀ x v, ¬ (I.dp p x v ∧ I.dp q x v)
  | [], h, _ => by cases h
  | p :: ps, h, hp => by
    rw [refDisjDP, Bool.or_eq_true] at h
    rw [List.pairwise_cons] at hp
    rcases h with h | h
    · obtain ⟨q, hq, h⟩ := List.any_eq_true.1 h
      obtain ⟨w, -, h⟩ := List.any_eq_true.1 h
      obtain ⟨i, hi, h⟩ := List.any_eq_true.1 h
      exact hp.1 q hq (f w) (val w i) ⟨hK.dpos p w i hi, hK.dpos q w i (List.contains_iff_mem.1 h)⟩
    · exact refDisjDP_sound hK ps h hp.2

/-- **Soundness of the refutation with data and counting.** -/
theorem refuteX_sound (hK : CKXSpec K I f val) (N : List IRI) (ax : Axiom) (h : refuteX K ax = true) :
    ¬ I.sat N ax := by
  have hb := hK.base
  cases ax with
  | subClassOf c d =>
    simp only [refuteX, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨w, -, h1, h2⟩ := h
    exact fun hs => (evD_sound hK d w).2 h2 (hs _ ((evD_sound hK c w).1 h1))
  | equivalentClasses cs =>
    simp only [refuteX, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, d, hd, w, -, h1, h2⟩ := h
    exact fun hs => (evD_sound hK d w).2 h2 (hs c hc d hd _ ((evD_sound hK c w).1 h1))
  | disjointClasses cs => exact refDisjCD_sound hK cs h
  | domain r c =>
    simp only [refuteX, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.isEmpty_eq_false_iff] at h
    obtain ⟨w, -, hne, h2⟩ := h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ hne
    exact fun hs => (evD_sound hK c w).2 h2 (hs _ _ (hb.pos r w v hv))
  | range r c =>
    simp only [refuteX, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨w, -, v, hv, h2⟩ := h
    exact fun hs => (evD_sound hK c v).2 h2 (hs _ _ (hb.pos r w v hv))
  | classAssertion c a =>
    simp only [refuteX] at h
    split at h
    next w hw =>
      rw [beq_iff_eq] at h
      intro hs
      simp only [Interp.sat] at hs
      rw [indOf_spec hb hw] at hs
      exact (evD_sound hK c w).2 h hs
    next => cases h
  | subDataPropertyOf p q => exact refSubDP_sound hK h
  | equivalentDataProperties ps =>
    simp only [refuteX, List.any_eq_true] at h
    obtain ⟨p, hp, q, hq, h⟩ := h
    exact fun hs => refSubDP_sound hK h (hs p hp q hq)
  | disjointDataProperties ps => exact refDisjDP_sound hK ps h
  | dataDomain p c =>
    simp only [refuteX, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, List.isEmpty_eq_false_iff] at h
    obtain ⟨w, -, hne, h2⟩ := h
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
    exact fun hs => (evD_sound hK c w).2 h2 (hs _ _ (hK.dpos p w i hi))
  | dataRange p R =>
    simp only [refuteX, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨w, -, i, hi, h2⟩ := h
    exact fun hs => absurd ((hK.dr R w i false h2 ⟨p, hi⟩).1 (hs _ _ (hK.dpos p w i hi))) (by simp)
  | functionalData p =>
    simp only [refuteX, List.any_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨w, -, i, hi, j, hj, hne⟩ := h
    exact fun hs => hne (hK.dinj p p w i j hi hj (hs _ _ _ (hK.dpos p w i hi) (hK.dpos p w j hj)))
  | dataPropertyAssertion p a l =>
    simp only [refuteX] at h
    split at h
    next w hw =>
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
      rintro ⟨x, hl, hx⟩
      rw [indOf_spec hb hw] at hx
      obtain ⟨i, hi, rfl⟩ := hK.dneg p w x h.1 hx
      exact absurd ((hK.dr _ w i false (h.2 i hi) ⟨p, hi⟩).1 ((drExt_oneOf_single l _).2 hl))
        (by simp)
    next => cases h
  | negativeDataPropertyAssertion p a l =>
    simp only [refuteX] at h
    split at h
    next w hw =>
      simp only [List.any_eq_true, beq_iff_eq] at h
      obtain ⟨i, hi, h2⟩ := h
      intro hs
      simp only [Interp.sat] at hs
      rw [indOf_spec hb hw] at hs
      exact hs ⟨val w i, (drExt_oneOf_single l _).1 ((hK.dr _ w i true h2 ⟨p, hi⟩).2 rfl),
        hK.dpos p w i hi⟩
    next => cases h
  | _ => simp [refuteX] at h

/-- **Soundness of `refuteD`**: the model does not satisfy `ax`. -/
theorem refuteD_sound (hK : CKXSpec K I f val) (N : List IRI) (ax : Axiom) (h : refuteD K ax = true) :
    ¬ I.sat N ax := by
  rw [refuteD, Bool.or_eq_true] at h
  rcases h with h | h
  · exact refute_sound hK.base N ax h
  · exact refuteX_sound hK N ax h

end RefuteSound

end ContextCalculus.OWLFrontend

#print axioms ContextCalculus.OWLFrontend.evD_sound
#print axioms ContextCalculus.OWLFrontend.refuteX_sound
#print axioms ContextCalculus.OWLFrontend.refuteD_sound
