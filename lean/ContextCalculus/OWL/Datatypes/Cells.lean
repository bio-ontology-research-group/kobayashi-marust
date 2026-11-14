import ContextCalculus.OWL.Datatypes.Map
import ContextCalculus.SRIQD.CellOracle
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod

/-!
# Cells of the OWL 2 value space (v1.7.0 stage C4, part C)

The oracle for the OWL 2 datatype map cuts the values into cells on which
every *base atom* of the supported sub-theory is constant, and counts the
values of each cell (`OWL/Datatypes/CellsSpec.lean` proves the cells exact,
`OWL/Datatypes/CellsEval.lean` proves the atoms constant on them).

## Base atoms (`BAtom`)

* `kind k`: the value space of a datatype of the map. Supported:
  `owl:real`, `xsd:decimal`, `xsd:integer` and the twelve integer types
  derived from it, `xsd:double`, `xsd:float`, `xsd:string`,
  `rdf:PlainLiteral`, `xsd:boolean`, `xsd:hexBinary`, `xsd:base64Binary`,
  `xsd:anyURI`, `xsd:dateTime`, `xsd:dateTimeStamp`, `rdf:XMLLiteral`,
  `rdfs:Literal`. Declined (`supportedKind`): `owl:rational`,
  `xsd:normalizedString`, `xsd:token`, `xsd:language`, `xsd:Name`,
  `xsd:NCName`, `xsd:NMTOKEN`.
* `numR k bs`: a numeric datatype (`owl:real`, `xsd:decimal`, an integer
  type) with bound facets `bs` (minimum or maximum, strict or not, a
  rational bound).
* `empty`: the empty set (an ill-typed literal, a facet that does not
  apply).
* `lit w`: the value of a literal.

## Cells (`Cell`)

* `pt w`: one point: the value of a literal, a numeric bound, or a
  boolean.
* `gap lo hi cls`: the reals strictly between two neighbouring numeric
  points (`none`: unbounded), of class `cls`: integers (`0`), decimals
  that are not integers (`1`), other reals (`2`).
* the rest of each other value space (`dblR`, `fltR`, `strR` for strings
  without a tag, `tagR` with a tag, `uriR`, `hexR`, `b64R`, `xmlR`,
  `timeTz`, `timeLoc`), and `other` for the values outside every value
  space of the supported datatypes.

Sizes: a point has one value; integers between two bounds are counted;
`xsd:double` and `xsd:float` have `2·(2^e - 1)·2^m + 3` values
(`FloatV.card`) minus the points; every other cell is infinite.
-/

namespace ContextCalculus.OWL.Datatypes

open ContextCalculus.SRIQD (toE)

/-! ## Floats are finite -/

/-- The floats as a sum of products. -/
def FloatV.equiv (e m : Nat) : FloatV e m ≃ (Bool × Fin (2 ^ e - 1) × Fin (2 ^ m)) ⊕ (Bool ⊕ Unit) where
  toFun
    | .fin s E M => .inl (s, E, M)
    | .inf s => .inr (.inl s)
    | .nan => .inr (.inr ())
  invFun
    | .inl (s, E, M) => .fin s E M
    | .inr (.inl s) => .inf s
    | .inr (.inr ()) => .nan
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨s, E, M⟩ | s | ⟨⟩ <;> rfl

instance (e m : Nat) : Fintype (FloatV e m) := Fintype.ofEquiv _ (FloatV.equiv e m).symm

/-- The number of floats. -/
def FloatV.card (e m : Nat) : Nat := 2 * (2 ^ e - 1) * 2 ^ m + 3

theorem FloatV.card_eq (e m : Nat) : Fintype.card (FloatV e m) = FloatV.card e m := by
  rw [Fintype.card_congr (FloatV.equiv e m)]
  simp [FloatV.card, Fintype.card_sum, Fintype.card_prod]
  ring

/-! ## Decimals -/

/-- `q` has a finite decimal expansion (decided by the denominator). -/
def decQ (q : ℚ) : Bool := decide (q.den ∣ 10 ^ Nat.log 2 q.den)

theorem dvd_pow_log_of_dvd_pow {d k : Nat} (hd : d ≠ 0) (h : d ∣ 10 ^ k) : d ∣ 10 ^ Nat.log 2 d := by
  have h10 : (10 : Nat) ≠ 0 := by norm_num
  rw [← Nat.factorization_le_iff_dvd hd (pow_ne_zero _ h10)]
  rw [← Nat.factorization_le_iff_dvd hd (pow_ne_zero _ h10)] at h
  intro p
  have hp := h p
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hp ⊢
  by_cases h0 : (10 : Nat).factorization p = 0
  · rw [h0, mul_zero] at hp
    rw [Nat.le_zero.1 hp]
    exact Nat.zero_le _
  · by_cases hdp : d.factorization p = 0
    · rw [hdp]; exact Nat.zero_le _
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.2 hdp)
      have hpow : p ^ d.factorization p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd)
        (Nat.ordProj_dvd d p)
      have h2 : 2 ^ d.factorization p ≤ d :=
        (Nat.pow_le_pow_left hpp.two_le _).trans hpow
      have hlog : d.factorization p ≤ Nat.log 2 d := Nat.le_log_of_pow_le (by norm_num) h2
      calc d.factorization p ≤ Nat.log 2 d := hlog
        _ ≤ Nat.log 2 d * (10 : Nat).factorization p :=
          Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h0)

theorem isDecimalQ_iff (q : ℚ) : IsDecimalQ q ↔ decQ q = true := by
  rw [decQ, decide_eq_true_iff]
  constructor
  · rintro ⟨z, k, hq⟩
    refine dvd_pow_log_of_dvd_pow (k := k) q.den_nz ?_
    have hq' : q = Rat.divInt z ((10 ^ k : ℕ) : ℤ) := by
      rw [Rat.divInt_eq_div, hq]; push_cast; rfl
    have h1 := Rat.den_dvd z ((10 ^ k : ℕ) : ℤ)
    rw [← hq'] at h1
    exact Int.natCast_dvd_natCast.1 h1
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨q.num * c, Nat.log 2 q.den, ?_⟩
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have h10 : ((10 : ℚ) ^ Nat.log 2 q.den) = (q.den : ℚ) * c := by exact_mod_cast hc
    have hc0 : (c : ℚ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h10
      exact absurd h10 (pow_ne_zero _ (by norm_num))
    rw [h10]
    push_cast
    rw [mul_div_mul_right _ _ hc0]
    exact (Rat.num_div_den q).symm

/-! ## Base atoms -/

/-- The base atoms (see the module docstring). -/
inductive BAtom where
  | kind (k : Kind)
  | numR (k : Kind) (bs : List ((Bool × Bool) × ℚ))
  | empty
  | lit (w : ValOf ℚ)
deriving DecidableEq, Repr

/-- The meaning of a base atom in the map. -/
def BAtom.sem : BAtom → Val → Prop
  | .kind k => kindSem k
  | .numR k bs => fun v => kindSem k v ∧ ∀ b ∈ bs, ∃ x, v = .num x ∧ boundRel b.1 x (b.2 : ℝ)
  | .empty => fun _ => False
  | .lit w => fun v => v = toVal w

/-- The kinds of the supported sub-theory. -/
def supportedKind : Kind → Bool
  | .rational | .normalizedString | .token | .language | .name | .ncName | .nmToken => false
  | _ => true

/-- The numeric kinds with bound facets in the sub-theory. -/
def numKind : Kind → Bool
  | .real | .decimal | .integer .. => true
  | _ => false

/-- The base atoms of the supported sub-theory. -/
def BAtom.supported : BAtom → Bool
  | .kind k => supportedKind k
  | .numR k _ => numKind k
  | _ => true

/-! ## Points -/

/-- The bounds of an integer type. -/
def intBounds : Kind → List ℚ
  | .integer lo hi => lo.toList.map (fun z : Int => (z : ℚ)) ++ hi.toList.map (fun z : Int => (z : ℚ))
  | _ => []

/-- The numbers an atom mentions. -/
def BAtom.nums : BAtom → List ℚ
  | .kind k => intBounds k
  | .numR k bs => intBounds k ++ bs.map Prod.snd
  | .lit (.num q) => [q]
  | _ => []

/-- The non-numeric values an atom mentions. -/
def BAtom.others : BAtom → List (ValOf ℚ)
  | .lit (.num _) => []
  | .lit w => [w]
  | _ => []

/-- The numeric points. -/
def numPts (as : List BAtom) : List ℚ := (as.flatMap BAtom.nums).dedup

/-- The other points: the literal values and both booleans. -/
def otherPts (as : List BAtom) : List (ValOf ℚ) :=
  (as.flatMap BAtom.others ++ [ValOf.bool true, ValOf.bool false]).dedup

/-- All points. -/
def allPts (as : List BAtom) : List (ValOf ℚ) := (numPts as).map .num ++ otherPts as

/-! ## Cells -/

/-- The cells (see the module docstring). -/
inductive Cell where
  | pt (w : ValOf ℚ)
  | gap (lo hi : Option ℚ) (cls : Fin 3)
  | dblR
  | fltR
  | strR
  | tagR
  | uriR
  | hexR
  | b64R
  | xmlR
  | timeTz
  | timeLoc
  | other
deriving DecidableEq, Repr

/-- `lo < p` with `none` as minus infinity. -/
def ltLo (lo : Option ℚ) (p : ℚ) : Bool :=
  match lo with
  | none => true
  | some a => decide (a < p)

/-- `p < hi` with `none` as plus infinity. -/
def ltHi (p : ℚ) (hi : Option ℚ) : Bool :=
  match hi with
  | none => true
  | some b => decide (p < b)

/-- `(lo, hi)` is a nonempty interval without points inside. -/
def gapOK (P : List ℚ) (lo hi : Option ℚ) : Bool :=
  (match lo, hi with
    | some a, some b => decide (a < b)
    | _, _ => true) && P.all fun p => !(ltLo lo p && ltHi p hi)

/-- The gaps between neighbouring points. -/
def gapPairs (P : List ℚ) : List (Option ℚ × Option ℚ) :=
  ((none :: P.map some).flatMap fun lo => (P.map some ++ [none]).map fun hi => (lo, hi)).filter
    fun x => gapOK P x.1 x.2

/-- The rest cells. -/
def restCells : List Cell :=
  [.dblR, .fltR, .strR, .tagR, .uriR, .hexR, .b64R, .xmlR, .timeTz, .timeLoc, .other]

/-- The cells of a list of atoms. -/
def cellsOf (as : List BAtom) : List Cell :=
  ((allPts as).map Cell.pt ++
    (gapPairs (numPts as)).flatMap (fun x : Option ℚ × Option ℚ => [0, 1, 2].map (Cell.gap x.1 x.2)) ++
    restCells).dedup

def isDbl : ValOf ℚ → Bool
  | .dbl _ => true
  | _ => false

def isFlt : ValOf ℚ → Bool
  | .flt _ => true
  | _ => false

/-- The number of values of a cell; `none` for infinitely many. -/
def cellSize (as : List BAtom) : Cell → Option Nat
  | .pt _ => some 1
  | .gap (some a) (some b) 0 => some (⌈b⌉ - ⌊a⌋ - 1).toNat
  | .gap _ _ _ => none
  | .dblR => some (FloatV.card 11 52 - ((otherPts as).filter isDbl).length)
  | .fltR => some (FloatV.card 8 23 - ((otherPts as).filter isFlt).length)
  | _ => none

/-! ## Evaluating atoms on cells -/

/-- The kind check on a literal value (a computable `kindSem`). -/
def kindPt : Kind → ValOf ℚ → Bool
  | .real, .num _ => true
  | .rational, .num _ => true
  | .decimal, .num q => decQ q
  | .integer lo hi, .num q =>
      q.den == 1 && (lo.all fun l => decide ((l : ℚ) ≤ q)) && (hi.all fun h => decide (q ≤ (h : ℚ)))
  | .double, .dbl _ => true
  | .float, .flt _ => true
  | .string, .str s none => xmlString s
  | .normalizedString, .str s none => xmlString s && isNormalizedX s.toList
  | .token, .str s none => xmlString s && isTokenX s.toList
  | .language, .str s none => xmlString s && Parse.isLanguageTag s.toList
  | .name, .str s none => xmlString s && isNameX s.toList
  | .ncName, .str s none => xmlString s && isNCNameX s.toList
  | .nmToken, .str s none => xmlString s && isNmtokenX s.toList
  | .plainLiteral, .str s none => xmlString s
  | .plainLiteral, .str s (some t) => xmlString s && langTagOK t.toList && lowerTag t == t
  | .boolean, .bool _ => true
  | .hexBinary, .hex _ => true
  | .base64Binary, .b64 _ => true
  | .anyURI, .uri s => xmlString s
  | .dateTime, .time t _ => decQ t
  | .dateTimeStamp, .time t z => z && decQ t
  | .xmlLiteral, .xml s => xmlString s
  | .literal, _ => true
  | _, _ => false

/-- A bound facet on a rational. -/
def boundB (b : Bool × Bool) (x y : ℚ) : Bool :=
  match b with
  | (true, false) => decide (y ≤ x)
  | (true, true) => decide (y < x)
  | (false, false) => decide (x ≤ y)
  | (false, true) => decide (x < y)

/-- An atom at a point. -/
def evalPt : BAtom → ValOf ℚ → Bool
  | .kind k, w => kindPt k w
  | .numR k bs, w => kindPt k w && (match w with
      | .num q => bs.all fun b => boundB b.1 q b.2
      | _ => false)
  | .empty, _ => false
  | .lit w', w => w == w'

/-- The point `p` lies below the gap whose lower end is `lo`. -/
def ptBelow (lo : Option ℚ) (p : ℚ) : Bool :=
  match lo with
  | none => false
  | some a => decide (p ≤ a)

/-- The point `p` lies above the gap whose upper end is `hi`. -/
def ptAbove (hi : Option ℚ) (p : ℚ) : Bool :=
  match hi with
  | none => false
  | some b => decide (b ≤ p)

/-- A kind on a gap. -/
def kindGap : Kind → Option ℚ → Option ℚ → Fin 3 → Bool
  | .real, _, _, _ => true
  | .decimal, _, _, c => c != 2
  | .integer l h, lo, hi, c => c == 0 && (l.all fun l => ptBelow lo l) && (h.all fun h => ptAbove hi h)
  | .literal, _, _, _ => true
  | _, _, _, _ => false

/-- A bound facet on a gap. -/
def boundGap (b : Bool × Bool) (y : ℚ) (lo hi : Option ℚ) : Bool :=
  match b with
  | (true, _) => ptBelow lo y
  | (false, _) => ptAbove hi y

/-- A kind on one of the rest cells. -/
def kindRest : Kind → Cell → Bool
  | .literal, _ => true
  | .double, .dblR => true
  | .float, .fltR => true
  | .string, .strR => true
  | .plainLiteral, .strR => true
  | .plainLiteral, .tagR => true
  | .anyURI, .uriR => true
  | .hexBinary, .hexR => true
  | .base64Binary, .b64R => true
  | .xmlLiteral, .xmlR => true
  | .dateTime, .timeTz => true
  | .dateTime, .timeLoc => true
  | .dateTimeStamp, .timeTz => true
  | _, _ => false

/-- **An atom on a cell.** -/
def evalCell (a : BAtom) : Cell → Bool
  | .pt w => evalPt a w
  | .gap lo hi c =>
    match a with
    | .kind k => kindGap k lo hi c
    | .numR k bs => kindGap k lo hi c && bs.all fun b => boundGap b.1 b.2 lo hi
    | _ => false
  | c =>
    match a with
    | .kind k => kindRest k c
    | _ => false

/-! ## The cell of a value -/

/-- The class of a real: integer `0`, other decimal `1`, other real `2`. -/
noncomputable def numClass (x : ℝ) : Fin 3 := by
  classical
  exact if ∃ z : ℤ, x = z then 0 else if IsDecimalR x then 1 else 2

/-- The largest point below `x`. -/
noncomputable def maxBelow (P : List ℚ) (x : ℝ) : Option ℚ := by
  classical
  exact (P.filter fun q : ℚ => decide ((q : ℝ) < x)).max?

/-- The smallest point above `x`. -/
noncomputable def minAbove (P : List ℚ) (x : ℝ) : Option ℚ := by
  classical
  exact (P.filter fun q : ℚ => decide (x < (q : ℝ))).min?

/-- The rest cell of a non-numeric value outside the points. -/
def restCell : Val → Cell
  | .num _ => .other
  | .dbl _ => .dblR
  | .flt _ => .fltR
  | .str s none => if xmlString s then .strR else .other
  | .str s (some t) => if xmlString s && langTagOK t.toList && lowerTag t == t then .tagR else .other
  | .bool _ => .other
  | .hex _ => .hexR
  | .b64 _ => .b64R
  | .uri s => if xmlString s then .uriR else .other
  | .time t z => if decQ t then (if z then .timeTz else .timeLoc) else .other
  | .xml s => if xmlString s then .xmlR else .other
  | .extra _ => .other

/-- The cell of a value. -/
noncomputable def cellOf (as : List BAtom) (v : Val) : Cell := by
  classical
  exact if h : ∃ w ∈ allPts as, toVal w = v then .pt h.choose
  else match v with
    | .num x => .gap (maxBelow (numPts as) x) (minAbove (numPts as) x) (numClass x)
    | v => restCell v

end ContextCalculus.OWL.Datatypes
