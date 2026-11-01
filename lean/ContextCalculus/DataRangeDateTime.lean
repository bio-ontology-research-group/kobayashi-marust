import Mathlib.Data.Set.Card
import Mathlib.Data.Int.Interval
import ContextCalculus.DataRangeDecimalBands

/-!
# dateTime bounds as ordered cells, and `rdf:XMLLiteral` identity
(`docs/DATATYPES.md`, "dateTime bounds as ordered cells",
`frontend/datatypes/time.rs`, `vocabulary.rs` `time_cells`)

**The value space.** An `xsd:dateTime` value is timezoned (`zoned t o`: the
instant `t`, in seconds, and the offset `o`, in minutes, `-840 ≤ o ≤ 840`)
or untimezoned (`untz l`: the local time `l`). Seconds carry arbitrary
decimal fractions, so `t` and `l` are decimals (`IsDecimal`). Identity keeps
the offset: `zoned t o = zoned t o'` only for `o = o'`.

**The order** (XSD 1.1 part 2, 3.3.7 and D.2.1): two timezoned values are
ordered by their instants, two untimezoned values by their local times, and
a timezoned `P` and an untimezoned `Q` compare only beyond fourteen hours:
`P < Q` iff `P < Q - 14h`, `P > Q` iff `P > Q + 14h`. XSD equality (`eqv`)
holds between values of one kind at the same position.

**The encoding** (`TimeRange`): a range is a pair of axis intervals, `z` over
the instants of the timezoned values and `u` over the local times of the
untimezoned values. A bound facet restricts both axes (`restrict`).

Theorems:

* `restrict_mem`: the encoding of a bound facet is exact for the XSD order:
  `(restrict r f b).mem x ↔ r.mem x ∧ facetSem f b x`;
* `Axis.subsetB_sound`, `Axis.disjointB_sound`, `Rng.subsetB_sound`,
  `Rng.disjointB_sound`: the oracle's inclusion and disjointness decisions
  are sound (the value relation clauses `c → d`, `c ∧ d → ⊥`);
* `cell_uniform`: every axis interval whose endpoints are cuts contains
  every point of a cell of the cuts or none (the cell exactness theorem:
  `cell_member` decides a whole cell by one representative);
* `gap_eq_cellOf`, `cellOf_cut`: the cells `time_cells` names (open gaps
  between consecutive cuts and the cuts) are the cells of the cuts;
* `zoned_point_encard`, `untz_point_encard`, `gap_infinite`,
  `gap_infinite_any`: the sizes
  `Cell::size` uses (`1681`, `1`, infinite), which `CellSpec.size_eq` of
  `DataRangeCells` asks for;
* `xml_value_eq_iff`: two well-typed `rdf:XMLLiteral` literals denote the
  same value iff their lexical forms are equal.
-/

namespace ContextCalculus.DataRangeDateTime
open ContextCalculus.DataRangeDecimalBands

/-! ## Values and the XSD order -/

/-- Fourteen hours in seconds. -/
def spread : ℚ := 50400

inductive DTVal where
  | zoned (t : ℚ) (o : ℤ)
  | untz (l : ℚ)
  deriving DecidableEq

/-- The value space of `xsd:dateTime`. -/
def Valid : DTVal → Prop
  | .zoned t o => IsDecimal t ∧ -840 ≤ o ∧ o ≤ 840
  | .untz l => IsDecimal l

/-- The XSD 1.1 strict order. -/
def lt : DTVal → DTVal → Prop
  | .zoned t _, .zoned t' _ => t < t'
  | .untz l, .untz l' => l < l'
  | .zoned t _, .untz l => t < l - spread
  | .untz l, .zoned t _ => l + spread < t

/-- XSD equality (not identity): one kind, one position. -/
def eqv : DTVal → DTVal → Prop
  | .zoned t _, .zoned t' _ => t = t'
  | .untz l, .untz l' => l = l'
  | _, _ => False

inductive Facet where
  | minIn | minEx | maxIn | maxEx

/-- The value set of a bound facet with bound `b`. -/
def facetSem : Facet → DTVal → DTVal → Prop
  | .minIn, b, x => lt b x ∨ eqv b x
  | .minEx, b, x => lt b x
  | .maxIn, b, x => lt x b ∨ eqv x b
  | .maxEx, b, x => lt x b

/-! ## Axis intervals -/

/-- A lower bound `(p, inclusive)`. -/
def lowOk : Option (ℚ × Bool) → ℚ → Prop
  | none, _ => True
  | some (p, true), q => p ≤ q
  | some (p, false), q => p < q

def highOk : Option (ℚ × Bool) → ℚ → Prop
  | none, _ => True
  | some (p, true), q => q ≤ p
  | some (p, false), q => q < p

structure Axis where
  present : Bool
  lo : Option (ℚ × Bool)
  hi : Option (ℚ × Bool)

def Axis.mem (a : Axis) (q : ℚ) : Prop := a.present = true ∧ lowOk a.lo q ∧ highOk a.hi q

def Axis.full : Axis := ⟨true, none, none⟩
def Axis.absent : Axis := ⟨false, none, none⟩

/-- `tighten_min`: keep the larger bound, the exclusive one at a tie. -/
def tightenLo (cur : Option (ℚ × Bool)) (b : ℚ × Bool) : Option (ℚ × Bool) :=
  match cur with
  | none => some b
  | some c => if c.1 < b.1 ∨ (c.1 = b.1 ∧ c.2 = true ∧ b.2 = false) then some b else some c

def tightenHi (cur : Option (ℚ × Bool)) (b : ℚ × Bool) : Option (ℚ × Bool) :=
  match cur with
  | none => some b
  | some c => if b.1 < c.1 ∨ (c.1 = b.1 ∧ c.2 = true ∧ b.2 = false) then some b else some c

theorem lowOk_imp {c p : ℚ} {ci pi : Bool} (h : c < p ∨ (c = p ∧ (ci = true ∨ pi = false)))
    (q : ℚ) (hq : lowOk (some (p, pi)) q) : lowOk (some (c, ci)) q := by
  rcases h with h | ⟨rfl, h | h⟩
  · cases ci <;> cases pi <;> simp only [lowOk] at hq ⊢ <;> linarith
  · subst h; cases pi <;> simp only [lowOk] at hq ⊢ <;> linarith
  · subst h; cases ci <;> simp only [lowOk] at hq ⊢ <;> linarith

theorem highOk_imp {c p : ℚ} {ci pi : Bool} (h : p < c ∨ (c = p ∧ (ci = true ∨ pi = false)))
    (q : ℚ) (hq : highOk (some (p, pi)) q) : highOk (some (c, ci)) q := by
  rcases h with h | ⟨rfl, h | h⟩
  · cases ci <;> cases pi <;> simp only [highOk] at hq ⊢ <;> linarith
  · subst h; cases pi <;> simp only [highOk] at hq ⊢ <;> linarith
  · subst h; cases ci <;> simp only [highOk] at hq ⊢ <;> linarith

theorem lowOk_tighten (cur : Option (ℚ × Bool)) (b : ℚ × Bool) (q : ℚ) :
    lowOk (tightenLo cur b) q ↔ lowOk cur q ∧ lowOk (some b) q := by
  rcases cur with _ | ⟨c, ci⟩
  · simp [tightenLo, lowOk]
  obtain ⟨p, pi⟩ := b
  simp only [tightenLo]
  split_ifs with h
  · refine ⟨fun hq => ⟨lowOk_imp ?_ q hq, hq⟩, fun h => h.2⟩
    rcases h with h | ⟨h1, h2, _⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · refine ⟨fun hq => ⟨hq, lowOk_imp ?_ q hq⟩, fun h => h.1⟩
    push Not at h
    obtain ⟨h1, h2⟩ := h
    rcases lt_or_eq_of_le h1 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      cases ci <;> cases pi <;> simp_all

theorem highOk_tighten (cur : Option (ℚ × Bool)) (b : ℚ × Bool) (q : ℚ) :
    highOk (tightenHi cur b) q ↔ highOk cur q ∧ highOk (some b) q := by
  rcases cur with _ | ⟨c, ci⟩
  · simp [tightenHi, highOk]
  obtain ⟨p, pi⟩ := b
  simp only [tightenHi]
  split_ifs with h
  · refine ⟨fun hq => ⟨highOk_imp ?_ q hq, hq⟩, fun h => h.2⟩
    rcases h with h | ⟨h1, h2, _⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · refine ⟨fun hq => ⟨hq, highOk_imp ?_ q hq⟩, fun h => h.1⟩
    push Not at h
    obtain ⟨h1, h2⟩ := h
    rcases lt_or_eq_of_le h1 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1.symm, ?_⟩
      cases ci <;> cases pi <;> simp_all

def Axis.tlo (a : Axis) (b : ℚ × Bool) : Axis := ⟨a.present, tightenLo a.lo b, a.hi⟩
def Axis.thi (a : Axis) (b : ℚ × Bool) : Axis := ⟨a.present, a.lo, tightenHi a.hi b⟩

theorem Axis.mem_tlo (a : Axis) (b : ℚ × Bool) (q : ℚ) :
    (a.tlo b).mem q ↔ a.mem q ∧ lowOk (some b) q := by
  simp only [Axis.mem, Axis.tlo, lowOk_tighten]; tauto

theorem Axis.mem_thi (a : Axis) (b : ℚ × Bool) (q : ℚ) :
    (a.thi b).mem q ↔ a.mem q ∧ highOk (some b) q := by
  simp only [Axis.mem, Axis.thi, highOk_tighten]; tauto

/-- Meet of two lower (upper) bounds. -/
def meetLo (x : Option (ℚ × Bool)) : Option (ℚ × Bool) → Option (ℚ × Bool)
  | none => x
  | some p => tightenLo x p

def meetHi (x : Option (ℚ × Bool)) : Option (ℚ × Bool) → Option (ℚ × Bool)
  | none => x
  | some p => tightenHi x p

theorem lowOk_meet (x y : Option (ℚ × Bool)) (q : ℚ) :
    lowOk (meetLo x y) q ↔ lowOk x q ∧ lowOk y q := by
  rcases y with _ | p
  · simp [meetLo, lowOk]
  · exact lowOk_tighten x p q

theorem highOk_meet (x y : Option (ℚ × Bool)) (q : ℚ) :
    highOk (meetHi x y) q ↔ highOk x q ∧ highOk y q := by
  rcases y with _ | p
  · simp [meetHi, highOk]
  · exact highOk_tighten x p q

/-- `Axis::intersect`. -/
def Axis.inter (a b : Axis) : Axis := ⟨a.present && b.present, meetLo a.lo b.lo, meetHi a.hi b.hi⟩

theorem Axis.mem_inter (a b : Axis) (q : ℚ) : (a.inter b).mem q ↔ a.mem q ∧ b.mem q := by
  simp only [Axis.mem, Axis.inter, lowOk_meet, highOk_meet, Bool.and_eq_true]; tauto

/-- Crossed bounds (`Axis::is_empty` without the `present` test). -/
def boundsCross : Option (ℚ × Bool) → Option (ℚ × Bool) → Bool
  | some (p, pi), some (r, ri) => decide (r < p) || (decide (p = r) && !(pi && ri))
  | _, _ => false

/-- `Axis::is_empty`. -/
def Axis.isEmptyB (a : Axis) : Bool := !a.present || boundsCross a.lo a.hi

theorem boundsCross_sound (lo hi : Option (ℚ × Bool)) (h : boundsCross lo hi = true) (q : ℚ)
    (hl : lowOk lo q) (hh : highOk hi q) : False := by
  rcases lo with _ | ⟨p, pi⟩ <;> rcases hi with _ | ⟨r, ri⟩ <;> simp [boundsCross] at h
  rcases h with h | ⟨rfl, h⟩
  · cases pi <;> cases ri <;> simp only [lowOk, highOk] at hl hh <;> linarith
  · rcases h with rfl | rfl
    · cases ri <;> simp only [lowOk, highOk] at hl hh <;> linarith
    · cases pi <;> simp only [lowOk, highOk] at hl hh <;> linarith

theorem Axis.isEmptyB_sound (a : Axis) (h : a.isEmptyB = true) (q : ℚ) : ¬ a.mem q := by
  rintro ⟨hp, hl, hh⟩
  simp only [Axis.isEmptyB, hp, Bool.not_true, Bool.false_or] at h
  exact boundsCross_sound _ _ h q hl hh

def Axis.subsetLo : Option (ℚ × Bool) → Option (ℚ × Bool) → Bool
  | _, none => true
  | none, some _ => false
  | some (s, si), some (o, oi) => decide (o < s) || (decide (s = o) && (oi || !si))

def Axis.subsetHi : Option (ℚ × Bool) → Option (ℚ × Bool) → Bool
  | _, none => true
  | none, some _ => false
  | some (s, si), some (o, oi) => decide (s < o) || (decide (s = o) && (oi || !si))

/-- `Axis::subset`. -/
def Axis.subsetB (a b : Axis) : Bool :=
  a.isEmptyB || (!b.isEmptyB && Axis.subsetLo a.lo b.lo && Axis.subsetHi a.hi b.hi)

theorem subsetLo_sound (s o : Option (ℚ × Bool)) (h : Axis.subsetLo s o = true) (q : ℚ)
    (hq : lowOk s q) : lowOk o q := by
  rcases o with _ | ⟨o, oi⟩
  · trivial
  rcases s with _ | ⟨s, si⟩
  · simp [Axis.subsetLo] at h
  simp only [Axis.subsetLo, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨rfl, h⟩
  · cases si <;> cases oi <;> simp [lowOk] at hq ⊢ <;> linarith
  · cases si <;> cases oi <;> simp [lowOk] at hq h ⊢ <;> linarith

theorem subsetHi_sound (s o : Option (ℚ × Bool)) (h : Axis.subsetHi s o = true) (q : ℚ)
    (hq : highOk s q) : highOk o q := by
  rcases o with _ | ⟨o, oi⟩
  · trivial
  rcases s with _ | ⟨s, si⟩
  · simp [Axis.subsetHi] at h
  simp only [Axis.subsetHi, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨rfl, h⟩
  · cases si <;> cases oi <;> simp [highOk] at hq ⊢ <;> linarith
  · cases si <;> cases oi <;> simp [highOk] at hq h ⊢ <;> linarith

/-- **Inclusion is sound** (`c → d` for `range_subsumed = Some(true)`). -/
theorem Axis.subsetB_sound (a b : Axis) (h : a.subsetB b = true) (q : ℚ) (hq : a.mem q) : b.mem q := by
  unfold Axis.subsetB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨hb, hlo⟩, hhi⟩
  · exact absurd hq (a.isEmptyB_sound h q)
  · refine ⟨?_, subsetLo_sound _ _ hlo q hq.2.1, subsetHi_sound _ _ hhi q hq.2.2⟩
    cases hpres : b.present
    · simp [Axis.isEmptyB, hpres] at hb
    · rfl

/-- **Disjointness is sound** (`c ∧ d → ⊥` for `range_disjoint = Some(true)`). -/
theorem Axis.disjointB_sound (a b : Axis) (h : (a.inter b).isEmptyB = true) (q : ℚ) :
    ¬ (a.mem q ∧ b.mem q) := fun hq => (a.inter b).isEmptyB_sound h q ((Axis.mem_inter a b q).2 hq)

/-! ## Ranges -/

/-- `TimeRange`: the timezoned axis `z` and the untimezoned axis `u`. -/
structure Rng where
  z : Axis
  u : Axis

def Rng.mem (r : Rng) : DTVal → Prop
  | .zoned t _ => r.z.mem t
  | .untz l => r.u.mem l

/-- `xsd:dateTime`, `xsd:dateTimeStamp`, and `dateTime ⊓ ¬dateTimeStamp`. -/
def Rng.dateTime : Rng := ⟨Axis.full, Axis.full⟩
def Rng.stamp : Rng := ⟨Axis.full, Axis.absent⟩
def Rng.untimezoned : Rng := ⟨Axis.absent, Axis.full⟩

theorem Rng.mem_dateTime (x : DTVal) : Rng.dateTime.mem x := by
  cases x <;> simp [Rng.dateTime, Rng.mem, Axis.mem, Axis.full, lowOk, highOk]

/-- `xsd:dateTimeStamp` holds exactly the timezoned values (OWL 2 4.7). -/
theorem Rng.mem_stamp (x : DTVal) : Rng.stamp.mem x ↔ ∃ t o, x = .zoned t o := by
  cases x <;> simp [Rng.stamp, Rng.mem, Axis.mem, Axis.full, Axis.absent, lowOk, highOk]

/-- The local-time cells' base: `dateTime ⊓ ¬dateTimeStamp`. -/
theorem Rng.mem_untimezoned (x : DTVal) : Rng.untimezoned.mem x ↔ ¬ Rng.stamp.mem x := by
  cases x <;> simp [Rng.untimezoned, Rng.stamp, Rng.mem, Axis.mem, Axis.full, Axis.absent, lowOk,
    highOk]

/-- `TimeRange::restrict`: the bound acts on its own axis and, moved by
fourteen hours and strict, on the other. -/
def restrict (r : Rng) : Facet → DTVal → Rng
  | .minIn, .zoned t _ => ⟨r.z.tlo (t, true), r.u.tlo (t + spread, false)⟩
  | .minEx, .zoned t _ => ⟨r.z.tlo (t, false), r.u.tlo (t + spread, false)⟩
  | .maxIn, .zoned t _ => ⟨r.z.thi (t, true), r.u.thi (t - spread, false)⟩
  | .maxEx, .zoned t _ => ⟨r.z.thi (t, false), r.u.thi (t - spread, false)⟩
  | .minIn, .untz l => ⟨r.z.tlo (l + spread, false), r.u.tlo (l, true)⟩
  | .minEx, .untz l => ⟨r.z.tlo (l + spread, false), r.u.tlo (l, false)⟩
  | .maxIn, .untz l => ⟨r.z.thi (l - spread, false), r.u.thi (l, true)⟩
  | .maxEx, .untz l => ⟨r.z.thi (l - spread, false), r.u.thi (l, false)⟩

/-- **The encoding of a bound facet is exact** for the XSD 1.1 order. -/
theorem restrict_mem (r : Rng) (f : Facet) (b x : DTVal) :
    (restrict r f b).mem x ↔ r.mem x ∧ facetSem f b x := by
  cases f <;> cases b <;> cases x <;>
    simp only [restrict, Rng.mem, Axis.mem_tlo, Axis.mem_thi, facetSem, lt, eqv, lowOk, highOk,
      or_false] <;>
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;>
    first
    | (rcases h2 with h2 | h2 <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith) | linarith)
    | (rcases lt_or_eq_of_le h2 with h2 | h2 <;> first | exact Or.inl h2 | exact Or.inr h2.symm | exact Or.inr h2)
    | linarith

def Rng.inter (a b : Rng) : Rng := ⟨a.z.inter b.z, a.u.inter b.u⟩

theorem Rng.mem_inter (a b : Rng) (x : DTVal) : (a.inter b).mem x ↔ a.mem x ∧ b.mem x := by
  cases x <;> simp only [Rng.inter, Rng.mem, Axis.mem_inter]

def Rng.subsetB (a b : Rng) : Bool := a.z.subsetB b.z && a.u.subsetB b.u
def Rng.disjointB (a b : Rng) : Bool := (a.z.inter b.z).isEmptyB && (a.u.inter b.u).isEmptyB

theorem Rng.subsetB_sound (a b : Rng) (h : a.subsetB b = true) (x : DTVal) (hx : a.mem x) :
    b.mem x := by
  simp only [Rng.subsetB, Bool.and_eq_true] at h
  cases x
  · exact Axis.subsetB_sound _ _ h.1 _ hx
  · exact Axis.subsetB_sound _ _ h.2 _ hx

theorem Rng.disjointB_sound (a b : Rng) (h : a.disjointB b = true) (x : DTVal) :
    ¬ (a.mem x ∧ b.mem x) := by
  simp only [Rng.disjointB, Bool.and_eq_true] at h
  cases x
  · exact Axis.disjointB_sound _ _ h.1 _
  · exact Axis.disjointB_sound _ _ h.2 _

/-! ## Cells -/

/-- The cell of `q` for the cuts `cuts`: the points on the same side of
every cut, equal to the same cuts. -/
def cellOf (cuts : List ℚ) (q : ℚ) : Set ℚ :=
  {y | ∀ c ∈ cuts, (c < q ↔ c < y) ∧ (c = q ↔ c = y)}

theorem mem_cellOf_self (cuts : List ℚ) (q : ℚ) : q ∈ cellOf cuts q :=
  fun _ _ => ⟨Iff.rfl, Iff.rfl⟩

/-- The endpoints of `a` are cuts. -/
def EndsIn (cuts : List ℚ) (a : Axis) : Prop :=
  (∀ p, a.lo = some p → p.1 ∈ cuts) ∧ (∀ p, a.hi = some p → p.1 ∈ cuts)

theorem lowOk_cell {cuts : List ℚ} {lo : Option (ℚ × Bool)} (h : ∀ p, lo = some p → p.1 ∈ cuts)
    {q y : ℚ} (hy : y ∈ cellOf cuts q) : lowOk lo y ↔ lowOk lo q := by
  rcases lo with _ | ⟨p, pi⟩
  · simp [lowOk]
  obtain ⟨hlt, heq⟩ := hy p (h _ rfl)
  cases pi
  · simp only [lowOk]; exact hlt.symm
  · simp only [lowOk, le_iff_lt_or_eq]; rw [hlt, heq]

theorem highOk_cell {cuts : List ℚ} {hi : Option (ℚ × Bool)} (h : ∀ p, hi = some p → p.1 ∈ cuts)
    {q y : ℚ} (hy : y ∈ cellOf cuts q) : highOk hi y ↔ highOk hi q := by
  rcases hi with _ | ⟨p, pi⟩
  · simp [highOk]
  obtain ⟨hlt, heq⟩ := hy p (h _ rfl)
  cases pi
  · simp only [highOk]
    rw [← not_le, ← not_le, le_iff_lt_or_eq, le_iff_lt_or_eq, hlt, heq]
  · simp only [highOk]
    rw [← not_lt, ← not_lt, hlt]

/-- **Cell exactness.** An axis interval whose endpoints are cuts contains
every point of a cell of the cuts or none of it, so the representative of
the cell decides the whole cell (`cell_member`). -/
theorem cell_uniform (cuts : List ℚ) (a : Axis) (ha : EndsIn cuts a) {q y : ℚ}
    (hy : y ∈ cellOf cuts q) : a.mem y ↔ a.mem q := by
  unfold Axis.mem
  rw [lowOk_cell ha.1 hy, highOk_cell ha.2 hy]

/-- On a range, membership of a timezoned value depends on its instant only
(the 1681 values of one instant form one cell). -/
theorem cell_uniform_zoned (cuts : List ℚ) (r : Rng) (hr : EndsIn cuts r.z) {t t' : ℚ}
    (ht : t' ∈ cellOf cuts t) (o o' : ℤ) : r.mem (.zoned t' o') ↔ r.mem (.zoned t o) :=
  cell_uniform cuts r.z hr ht

theorem cell_uniform_untz (cuts : List ℚ) (r : Rng) (hr : EndsIn cuts r.u) {l l' : ℚ}
    (hl : l' ∈ cellOf cuts l) : r.mem (.untz l') ↔ r.mem (.untz l) :=
  cell_uniform cuts r.u hr hl

/-- A cut is a cell of its own (a point cell). -/
theorem cellOf_cut (cuts : List ℚ) {c : ℚ} (hc : c ∈ cuts) : cellOf cuts c = {c} := by
  ext y
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hy; exact ((hy c hc).2.1 rfl).symm
  · rintro rfl; exact mem_cellOf_self cuts y

/-- The open gap `(lo, hi)` between consecutive cuts (`None` = unbounded),
as `time_cells` names it. -/
def gapAxis (lo hi : Option ℚ) : Axis := ⟨true, lo.map (·, false), hi.map (·, false)⟩

/-- **The named gaps are the cells.** If the endpoints of the gap are cuts
and no cut lies inside it, the gap is the cell of each of its points. -/
theorem gap_eq_cellOf (cuts : List ℚ) (lo hi : Option ℚ)
    (hlo : ∀ a, lo = some a → a ∈ cuts) (hhi : ∀ b, hi = some b → b ∈ cuts)
    (hnone : ∀ c ∈ cuts, ¬ (gapAxis lo hi).mem c) {q : ℚ} (hq : (gapAxis lo hi).mem q) (y : ℚ) :
    y ∈ cellOf cuts q ↔ (gapAxis lo hi).mem y := by
  constructor
  · intro hy
    exact (cell_uniform cuts (gapAxis lo hi)
      ⟨fun p hp => by
        rcases lo with _ | a <;> simp [gapAxis] at hp
        rw [← hp]; exact hlo a rfl,
       fun p hp => by
        rcases hi with _ | b <;> simp [gapAxis] at hp
        rw [← hp]; exact hhi b rfl⟩ hy).2 hq
  · intro hy c hc
    have hcn := hnone c hc
    obtain ⟨_, hql, hqh⟩ := hq
    obtain ⟨_, hyl, hyh⟩ := hy
    -- `c` is not inside the gap: it is at or below `lo` or at or above `hi`.
    have side : (∀ a, lo = some a → c ≤ a) ∨ (∀ b, hi = some b → b ≤ c) := by
      rcases lo with _ | a <;> rcases hi with _ | b
      · exact absurd ⟨rfl, trivial, trivial⟩ hcn
      · right; intro b' hb'; cases hb'
        exact not_lt.1 fun h => hcn ⟨rfl, trivial, h⟩
      · left; intro a' ha'; cases ha'
        exact not_lt.1 fun h => hcn ⟨rfl, h, trivial⟩
      · by_cases hac : a < c
        · right; intro b' hb'; cases hb'
          exact not_lt.1 fun h => hcn ⟨rfl, hac, h⟩
        · left; intro a' ha'; cases ha'
          exact not_lt.1 hac
    rcases side with hside | hside
    · rcases lo with _ | a
      · -- no lower end: then `hi` is bounded and `c` sits above it
        rcases hi with _ | b
        · exact absurd ⟨rfl, trivial, trivial⟩ hcn
        · have hbc : b ≤ c := not_lt.1 fun h => hcn ⟨rfl, trivial, h⟩
          simp only [gapAxis, Option.map, highOk] at hqh hyh
          exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩
      · have hca := hside a rfl
        simp only [gapAxis, Option.map, lowOk] at hql hyl
        exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩
    · rcases hi with _ | b
      · rcases lo with _ | a
        · exact absurd ⟨rfl, trivial, trivial⟩ hcn
        · have hca : c ≤ a := not_lt.1 fun h => hcn ⟨rfl, h, trivial⟩
          simp only [gapAxis, Option.map, lowOk] at hql hyl
          exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩
      · have hbc := hside b rfl
        simp only [gapAxis, Option.map, highOk] at hqh hyh
        exact ⟨⟨fun h => by linarith, fun h => by linarith⟩, ⟨fun h => by linarith, fun h => by linarith⟩⟩

/-! ## Cell sizes -/

/-- The cell `dateTimeStamp[t, t]`: every timezoned value at the instant `t`. -/
def zonedPoint (t : ℚ) : Rng := ⟨⟨true, some (t, true), some (t, true)⟩, Axis.absent⟩

theorem zonedPoint_values (t : ℚ) (ht : IsDecimal t) :
    {x | Valid x ∧ (zonedPoint t).mem x} = (fun o : ℤ => DTVal.zoned t o) '' Set.Icc (-840) 840 := by
  ext x
  cases x with
  | zoned t' o =>
    simp only [Set.mem_setOf_eq, Valid, zonedPoint, Rng.mem, Axis.mem, lowOk, highOk, true_and,
      Set.mem_image, Set.mem_Icc, DTVal.zoned.injEq]
    constructor
    · rintro ⟨⟨_, h1, h2⟩, h3, h4⟩
      exact ⟨o, ⟨h1, h2⟩, le_antisymm h4 h3 ▸ rfl, rfl⟩
    · rintro ⟨o', ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨⟨ht, h1, h2⟩, le_rfl, le_rfl⟩
  | untz l =>
    simp [Valid, zonedPoint, Rng.mem, Axis.mem, Axis.absent]

/-- **A timezoned point cell has 1681 values** (`VALUES_PER_INSTANT`). -/
theorem zoned_point_encard (t : ℚ) (ht : IsDecimal t) :
    {x | Valid x ∧ (zonedPoint t).mem x}.encard = 1681 := by
  rw [zonedPoint_values t ht, Function.Injective.encard_image (fun a b h => by
    simpa using h), ← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
  rfl

def untzPoint (l : ℚ) : Rng := ⟨Axis.absent, ⟨true, some (l, true), some (l, true)⟩⟩

/-- **An untimezoned point cell is one value.** -/
theorem untz_point_encard (l : ℚ) (hl : IsDecimal l) :
    {x | Valid x ∧ (untzPoint l).mem x}.encard = 1 := by
  have : {x | Valid x ∧ (untzPoint l).mem x} = {DTVal.untz l} := by
    ext x
    cases x with
    | zoned t o => simp [untzPoint, Rng.mem, Axis.mem, Axis.absent]
    | untz l' =>
      simp only [Set.mem_setOf_eq, Valid, untzPoint, Rng.mem, Axis.mem, lowOk, highOk, true_and,
        Set.mem_singleton_iff, DTVal.untz.injEq]
      constructor
      · rintro ⟨_, h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨hl, le_rfl, le_rfl⟩
  rw [this, Set.encard_singleton]

/-- **A nonempty open gap is infinite** on either axis (seconds are decimals). -/
theorem gap_infinite {a b : ℚ} (h : a < b) :
    {x | Valid x ∧ (⟨Axis.absent, gapAxis (some a) (some b)⟩ : Rng).mem x}.Infinite ∧
    {x | Valid x ∧ (⟨gapAxis (some a) (some b), Axis.absent⟩ : Rng).mem x}.Infinite := by
  have hband := decimal_band_infinite h
  constructor
  · refine Set.Infinite.mono ?_ (hband.image (f := fun q => DTVal.untz q)
      (fun x _ y _ hxy => by simpa using hxy))
    rintro _ ⟨q, ⟨hq1, hq2, hq3, _⟩, rfl⟩
    exact ⟨hq3, rfl, hq1, hq2⟩
  · refine Set.Infinite.mono ?_ (hband.image (f := fun q => DTVal.zoned q 0)
      (fun x _ y _ hxy => by simpa using hxy))
    rintro _ ⟨q, ⟨hq1, hq2, hq3, _⟩, rfl⟩
    exact ⟨⟨hq3, by norm_num, by norm_num⟩, rfl, hq1, hq2⟩

/-- Every nonempty gap, bounded or not, is infinite on either axis. -/
theorem gap_infinite_any (lo hi : Option ℚ) {q : ℚ} (hq : (gapAxis lo hi).mem q) :
    {x | Valid x ∧ (⟨Axis.absent, gapAxis lo hi⟩ : Rng).mem x}.Infinite ∧
    {x | Valid x ∧ (⟨gapAxis lo hi, Axis.absent⟩ : Rng).mem x}.Infinite := by
  obtain ⟨_, hql, hqh⟩ := hq
  -- a bounded gap `(q, b₀)` inside the given one
  obtain ⟨b₀, hqb, hsub⟩ : ∃ b₀, q < b₀ ∧ ∀ y, q < y → y < b₀ → (gapAxis lo hi).mem y := by
    rcases hi with _ | b
    · refine ⟨q + 1, by linarith, fun y hy _ => ⟨rfl, ?_, trivial⟩⟩
      rcases lo with _ | a
      · trivial
      · simp only [gapAxis, Option.map, lowOk] at hql ⊢; linarith
    · simp only [gapAxis, Option.map, highOk] at hqh
      refine ⟨(q + b) / 2, by linarith, fun y hy hyb => ⟨rfl, ?_, ?_⟩⟩
      · rcases lo with _ | a
        · trivial
        · simp only [gapAxis, Option.map, lowOk] at hql ⊢; linarith
      · simp only [gapAxis, Option.map, highOk]; linarith
  obtain ⟨h1, h2⟩ := gap_infinite hqb
  constructor
  · refine h1.mono ?_
    rintro (_ | l) ⟨hv, hm⟩
    · exact absurd hm.1 (by simp [Axis.absent])
    · obtain ⟨_, hl, hh⟩ := hm
      exact ⟨hv, hsub l hl hh⟩
  · refine h2.mono ?_
    rintro (_ | l) ⟨hv, hm⟩
    · obtain ⟨_, hl, hh⟩ := hm
      exact ⟨hv, hsub _ hl hh⟩
    · exact absurd hm.1 (by simp [Axis.absent])

/-! ## `rdf:XMLLiteral` -/

/-- RDF Concepts 5.1: the lexical space of `rdf:XMLLiteral` is the set of
strings in exclusive canonical XML (`canonical`), and the lexical-to-value
mapping is a one-to-one map from it onto the XML values (`xv` injective).
**Two well-typed literals denote the same value iff their lexical forms are
equal**, which is the identity `Val::Xml` uses. -/
theorem xml_value_eq_iff {V : Type} (canonical : List Char → Prop)
    (xv : {s // canonical s} → V) (hinj : Function.Injective xv)
    (s s' : List Char) (hs : canonical s) (hs' : canonical s') :
    xv ⟨s, hs⟩ = xv ⟨s', hs'⟩ ↔ s = s' :=
  ⟨fun h => congrArg Subtype.val (hinj h), fun h => by subst h; rfl⟩

end ContextCalculus.DataRangeDateTime
