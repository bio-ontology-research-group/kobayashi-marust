import ContextCalculus.DataValueSingletonElision

/-!
# String chain, `dateTimeStamp` and the binary types against the OWL 2 map

`docs/DATATYPES.md`, "Boolean data ranges and ordered cells", part (ii) of
the exactness argument: the oracle (`frontend/datatypes.rs`,
`range_subsumed` with `string_chain_rank`, `range_disjoint`) emits

* `A ⊑ B` for the string-family types with `rank A ≤ rank B` in the chain
  `language ⊂ NCName ⊂ Name ⊂ NMTOKEN ⊂ token ⊂ normalizedString ⊂ string ⊂
  rdf:PlainLiteral` (one way only: the reverse direction is `Some(false)` for
  `range_subsumed`, which emits no clause);
* `xsd:dateTimeStamp ⊑ xsd:dateTime`;
* `xsd:hexBinary ⊓ xsd:base64Binary ⊑ ⊥`, and disjointness between types of
  different partitions (strings, dateTime, binary).

This file states the value spaces of these twelve datatypes as the OWL 2
datatype map defines them (OWL 2 Structural Specification sections 4.3, 4.5,
4.7; XSD 1.1 part 2 sections 3.3.1, 3.3.7, 3.3.15, 3.3.16, 3.4.1 to 3.4.7,
3.4.28; XML 1.0 fifth edition productions [2], [4], [4a]) and proves:

* `oracleDec_sound`: the oracle's decisions on these names are a
  `DecisionSound` fact for that datatype map (the hypothesis
  `DataValueSingletonElision` needs);
* `chain_strict`: every inclusion of the chain is strict (the reverse
  `range_subsumed = Some(false)` is true), with explicit witnesses;
* `language_sub_NCName` and `Name_sub_NMTOKEN`: the two inclusions that are
  not inclusions of derivation (the others hold because each type is derived
  by restriction from the next).

A derived string type's value space is its base type's value space
intersected with its pattern (XSD derivation by restriction). The time line
of `xsd:dateTime` is a parameter `T`; nothing below depends on it. Core Lean
only.
-/

namespace ContextCalculus.DataRangeStrings
open ContextCalculus.DataValueSingletonElision

/-! ## Characters (XML 1.0 fifth edition) -/

/-- Production [2] `Char`. Lean's `Char` already excludes surrogates. -/
def xmlChar (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xD || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) ||
    (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- Production [4] `NameStartChar`. -/
def nameStartChar (c : Char) : Bool :=
  let n := c.toNat
  n == 0x3A || (0x41 ≤ n && n ≤ 0x5A) || n == 0x5F || (0x61 ≤ n && n ≤ 0x7A) ||
    (0xC0 ≤ n && n ≤ 0xD6) || (0xD8 ≤ n && n ≤ 0xF6) || (0xF8 ≤ n && n ≤ 0x2FF) ||
    (0x370 ≤ n && n ≤ 0x37D) || (0x37F ≤ n && n ≤ 0x1FFF) || (0x200C ≤ n && n ≤ 0x200D) ||
    (0x2070 ≤ n && n ≤ 0x218F) || (0x2C00 ≤ n && n ≤ 0x2FEF) || (0x3001 ≤ n && n ≤ 0xD7FF) ||
    (0xF900 ≤ n && n ≤ 0xFDCF) || (0xFDF0 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0xEFFFF)

/-- Production [4a] `NameChar`. -/
def nameChar (c : Char) : Bool :=
  let n := c.toNat
  nameStartChar c || n == 0x2D || n == 0x2E || (0x30 ≤ n && n ≤ 0x39) || n == 0xB7 ||
    (0x300 ≤ n && n ≤ 0x36F) || (0x203F ≤ n && n ≤ 0x2040)

def alphaChar (c : Char) : Bool :=
  let n := c.toNat
  (0x41 ≤ n && n ≤ 0x5A) || (0x61 ≤ n && n ≤ 0x7A)

def alnumChar (c : Char) : Bool :=
  alphaChar c || (0x30 ≤ c.toNat && c.toNat ≤ 0x39)

/-! ## Patterns -/

/-- Split at every `-`. -/
def splitDash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '-' then [] :: splitDash cs
    else match splitDash cs with
      | p :: ps => (c :: p) :: ps
      | [] => [[c]]

def subtag (q : Char → Bool) (p : List Char) : Bool :=
  1 ≤ p.length && p.length ≤ 8 && p.all q

/-- The `xsd:language` pattern `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`. -/
def languagePat (s : List Char) : Bool :=
  match splitDash s with
  | p :: ps => subtag alphaChar p && ps.all (subtag alnumChar)
  | [] => false

/-- `whiteSpace = replace` leaves the value unchanged: no tab, LF or CR. -/
def replaced (s : List Char) : Bool :=
  s.all (fun c => c.toNat != 0x9 && c.toNat != 0xA && c.toNat != 0xD)

/-- No two consecutive spaces. -/
def noDoubleSpace : List Char → Bool
  | ' ' :: ' ' :: _ => false
  | _ :: xs => noDoubleSpace xs
  | [] => true

/-- `whiteSpace = collapse` leaves the value unchanged: replaced, and no
leading, trailing or double space. -/
def collapsed (s : List Char) : Bool :=
  replaced s && s.head? != some ' ' && s.getLast? != some ' ' && noDoubleSpace s

/-- `\i\c*` -/
def nameShape : List Char → Bool
  | [] => false
  | c :: cs => nameStartChar c && cs.all nameChar

/-! ## Value spaces -/

/-- The values of the twelve datatypes. `str s none` is an `xsd:string`
value (OWL 2 identifies it with the `rdf:PlainLiteral` value without a
language tag), `str s (some t)` an `rdf:PlainLiteral` value with language
tag `t`; `dateTime t o` a time instant `t` on the time line `T` with an
optional timezone offset `o` in minutes; `hex o` and `b64 o` the octet
sequences of `xsd:hexBinary` and `xsd:base64Binary`, which OWL 2 section 4.5
keeps disjoint. -/
inductive MapVal (T : Type) where
  | str (s : List Char) (tag : Option (List Char))
  | dateTime (t : T) (offset : Option Int)
  | hex (octets : List UInt8)
  | b64 (octets : List UInt8)

def isPlain (s : List Char) (t : Option (List Char)) : Bool :=
  s.all xmlChar && (match t with | none => true | some tg => languagePat tg)
def isString (s : List Char) (t : Option (List Char)) : Bool := t.isNone && s.all xmlChar
def isNormalized (s : List Char) (t : Option (List Char)) : Bool := isString s t && replaced s
def isToken (s : List Char) (t : Option (List Char)) : Bool := isNormalized s t && collapsed s
def isNMTOKEN (s : List Char) (t : Option (List Char)) : Bool :=
  isToken s t && !s.isEmpty && s.all nameChar
def isName (s : List Char) (t : Option (List Char)) : Bool := isToken s t && nameShape s
def isNCName (s : List Char) (t : Option (List Char)) : Bool := isName s t && !(s.contains ':')
def isLanguage (s : List Char) (t : Option (List Char)) : Bool := isToken s t && languagePat s

/-- Timezone offsets range over `-14:00 … +14:00` (XSD 1.1 part 2, 3.3.7). -/
def offsetOk (m : Int) : Bool := decide (-840 ≤ m) && decide (m ≤ 840)

/-- The datatypes. -/
inductive SName where
  | language | NCName | Name | NMTOKEN | token | normalizedString | string | PlainLiteral
  | dateTime | dateTimeStamp | hexBinary | base64Binary
  deriving DecidableEq

variable {T : Type}

/-- The datatype map on these names, as a Boolean test. -/
def denB : SName → MapVal T → Bool
  | .language, .str s t => isLanguage s t
  | .NCName, .str s t => isNCName s t
  | .Name, .str s t => isName s t
  | .NMTOKEN, .str s t => isNMTOKEN s t
  | .token, .str s t => isToken s t
  | .normalizedString, .str s t => isNormalized s t
  | .string, .str s t => isString s t
  | .PlainLiteral, .str s t => isPlain s t
  | .dateTime, .dateTime _ none => true
  | .dateTime, .dateTime _ (some m) => offsetOk m
  | .dateTimeStamp, .dateTime _ (some m) => offsetOk m
  | .hexBinary, .hex _ => true
  | .base64Binary, .b64 _ => true
  | _, _ => false

/-- The datatype map `(·)^DT` on these names. -/
def den (n : SName) (v : MapVal T) : Prop := denB n v = true

/-! ## The oracle's decisions -/

/-- `string_chain_rank`. -/
def chainRank : SName → Option Nat
  | .language => some 0 | .NCName => some 1 | .Name => some 2 | .NMTOKEN => some 3
  | .token => some 4 | .normalizedString => some 5 | .string => some 6 | .PlainLiteral => some 7
  | _ => none

inductive Family where
  | strings | time | binary
  deriving DecidableEq

def family : SName → Family
  | .dateTime | .dateTimeStamp => .time
  | .hexBinary | .base64Binary => .binary
  | _ => .strings

/-- The relation clauses the oracle emits between two of these names:
`some true` is `a ⊑ b` (`range_subsumed = Some(true)`), `some false` is
`a ⊓ b ⊑ ⊥` (`range_disjoint = Some(true)`), `none` no clause. -/
def oracleDec (a b : SName) : Option Bool :=
  match chainRank a, chainRank b with
  | some x, some y => if x ≤ y then some true else none
  | _, _ =>
    if family a ≠ family b then some false
    else match a, b with
      | .dateTimeStamp, .dateTime => some true
      | .dateTime, .dateTime => some true
      | .dateTimeStamp, .dateTimeStamp => some true
      | .hexBinary, .hexBinary => some true
      | .base64Binary, .base64Binary => some true
      | .hexBinary, .base64Binary => some false
      | .base64Binary, .hexBinary => some false
      | _, _ => none

/-! ## The two inclusions that are not derivations -/

theorem splitDash_ne_nil : ∀ s : List Char, splitDash s ≠ []
  | [] => by simp [splitDash]
  | c :: cs => by
    unfold splitDash
    split
    · simp
    · cases h : splitDash cs with
      | nil => exact absurd h (splitDash_ne_nil cs)
      | cons p ps => simp

theorem splitDash_cons_ne {c : Char} {cs : List Char} (hc : c ≠ '-') :
    ∃ p ps, splitDash (c :: cs) = (c :: p) :: ps ∧ ∀ q, q ∈ splitDash cs → q = p ∨ q ∈ ps := by
  obtain ⟨p, ps, h⟩ : ∃ p ps, splitDash cs = p :: ps := by
    cases h : splitDash cs with
    | nil => exact absurd h (splitDash_ne_nil cs)
    | cons p ps => exact ⟨p, ps, rfl⟩
  refine ⟨p, ps, ?_, ?_⟩
  · simp [splitDash, hc, h]
  · intro q hq
    rw [h] at hq
    simpa using hq

/-- Every character is a `-` or lies in a part. -/
theorem mem_splitDash : ∀ (s : List Char) (x : Char), x ∈ s → x = '-' ∨ ∃ p ∈ splitDash s, x ∈ p
  | [], x, h => by simp at h
  | c :: cs, x, h => by
    by_cases hc : c = '-'
    · rcases List.mem_cons.1 h with hx | h
      · exact Or.inl (hx ▸ hc)
      · rcases mem_splitDash cs x h with h' | ⟨p, hp, hx⟩
        · exact Or.inl h'
        · refine Or.inr ⟨p, ?_, hx⟩
          simp [splitDash, hc, hp]
    · obtain ⟨p, ps, he, hsub⟩ := splitDash_cons_ne (cs := cs) hc
      rw [he]
      rcases List.mem_cons.1 h with hx | h
      · exact Or.inr ⟨c :: p, by simp, by simp [hx]⟩
      · rcases mem_splitDash cs x h with h' | ⟨q, hq, hx⟩
        · exact Or.inl h'
        · rcases hsub q hq with hqp | hq'
          · exact Or.inr ⟨c :: p, by simp, by simp [← hqp, hx]⟩
          · exact Or.inr ⟨q, by simp [hq'], hx⟩

theorem alpha_alnum {c : Char} (h : alphaChar c = true) : alnumChar c = true := by
  simp [alnumChar, h]

/-- A value of the `xsd:language` pattern starts with a letter and has only
letters, digits and `-`. -/
theorem languagePat_spec {s : List Char} (h : languagePat s = true) :
    (∃ c cs, s = c :: cs ∧ alphaChar c = true) ∧ ∀ x ∈ s, x = '-' ∨ alnumChar x = true := by
  unfold languagePat at h
  cases hs : splitDash s with
  | nil => rw [hs] at h; exact absurd h (by simp)
  | cons p ps =>
    rw [hs] at h
    simp only [subtag, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hp1, _⟩, hpa⟩, hps⟩ := h
    constructor
    · cases s with
      | nil => simp [splitDash] at hs; simp [hs.1] at hp1
      | cons c cs =>
        by_cases hc : c = '-'
        · simp [splitDash, hc] at hs; simp [hs.1] at hp1
        · obtain ⟨p', ps', he, _⟩ := splitDash_cons_ne (cs := cs) hc
          rw [he] at hs
          simp only [List.cons.injEq] at hs
          exact ⟨c, cs, rfl, hpa c (by rw [← hs.1]; simp)⟩
    · intro x hx
      rcases mem_splitDash s x hx with h' | ⟨q, hq, hxq⟩
      · exact Or.inl h'
      · right
        rw [hs] at hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact alpha_alnum (hpa x hxq)
        · exact (hps q hq).2 x hxq

theorem alpha_nameStart {c : Char} (h : alphaChar c = true) : nameStartChar c = true := by
  simp only [alphaChar, nameStartChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h ⊢
  omega

theorem nameStart_nameChar {c : Char} (h : nameStartChar c = true) : nameChar c = true := by
  simp [nameChar, h]

theorem alnum_or_dash_nameChar {c : Char} (h : c = '-' ∨ alnumChar c = true) : nameChar c = true := by
  rcases h with rfl | h
  · decide
  · simp only [alnumChar, alphaChar, nameChar, nameStartChar, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h ⊢
    omega

theorem alnum_or_dash_ne_colon {c : Char} (h : c = '-' ∨ alnumChar c = true) : c ≠ ':' := by
  rintro rfl
  rcases h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- `xsd:language ⊑ xsd:NCName`. -/
theorem language_sub_NCName {s : List Char} {t : Option (List Char)}
    (h : isLanguage s t = true) : isNCName s t = true := by
  simp only [isLanguage, Bool.and_eq_true] at h
  obtain ⟨htok, hpat⟩ := h
  obtain ⟨⟨c, cs, rfl, hc⟩, hall⟩ := languagePat_spec hpat
  simp only [isNCName, isName, htok, nameShape, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    List.all_eq_true]
  refine ⟨⟨alpha_nameStart hc, fun x hx => alnum_or_dash_nameChar (hall x (by simp [hx]))⟩, ?_⟩
  cases hcon : (c :: cs).contains ':' with
  | false => rfl
  | true =>
    have hm : ':' ∈ c :: cs := by simpa using hcon
    exact absurd rfl (alnum_or_dash_ne_colon (hall ':' hm))

/-- `xsd:Name ⊑ xsd:NMTOKEN`: every `NameStartChar` is a `NameChar`. -/
theorem Name_sub_NMTOKEN {s : List Char} {t : Option (List Char)}
    (h : isName s t = true) : isNMTOKEN s t = true := by
  simp only [isName, Bool.and_eq_true] at h
  obtain ⟨htok, hshape⟩ := h
  cases s with
  | nil => simp [nameShape] at hshape
  | cons c cs =>
    simp only [nameShape, Bool.and_eq_true, List.all_eq_true] at hshape
    simp only [isNMTOKEN, htok, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by simp, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact nameStart_nameChar hshape.1
    · exact hshape.2 x hx

/-! ## The chain, by steps -/

section Steps
variable {v : MapVal T}

theorem step_language : den .language v → den .NCName v := by
  cases v <;> simp [den, denB]; exact language_sub_NCName
theorem step_NCName : den .NCName v → den .Name v := by
  cases v <;> simp [den, denB, isNCName]; exact fun h _ => h
theorem step_Name : den .Name v → den .NMTOKEN v := by
  cases v <;> simp [den, denB]; exact Name_sub_NMTOKEN
theorem step_NMTOKEN : den .NMTOKEN v → den .token v := by
  cases v <;> simp [den, denB, isNMTOKEN]; exact fun h _ _ => h
theorem step_token : den .token v → den .normalizedString v := by
  cases v <;> simp [den, denB, isToken]; exact fun h _ => h
theorem step_normalized : den .normalizedString v → den .string v := by
  cases v <;> simp [den, denB, isNormalized]; exact fun h _ => h
theorem step_string : den .string v → den .PlainLiteral v := by
  cases v <;> simp [den, denB, isString, isPlain]
  rename_i s t
  intro ht hs
  cases t with
  | none => simpa using hs
  | some _ => simp at ht
theorem step_dateTimeStamp : den .dateTimeStamp v → den .dateTime v := by
  cases v with
  | dateTime t o => cases o <;> simp [den, denB]
  | _ => simp [den, denB]

end Steps

/-- The chain by rank. -/
def ofRank : Nat → SName
  | 0 => .language | 1 => .NCName | 2 => .Name | 3 => .NMTOKEN | 4 => .token
  | 5 => .normalizedString | 6 => .string | _ => .PlainLiteral

theorem ofRank_of_chainRank {a : SName} {x : Nat} (h : chainRank a = some x) :
    a = ofRank x ∧ x ≤ 7 := by
  cases a <;> simp [chainRank] at h <;> subst h <;> exact ⟨rfl, by decide⟩

theorem ofRank_step {v : MapVal T} : ∀ k, k < 7 → den (ofRank k) v → den (ofRank (k + 1)) v
  | 0, _ => step_language
  | 1, _ => step_NCName
  | 2, _ => step_Name
  | 3, _ => step_NMTOKEN
  | 4, _ => step_token
  | 5, _ => step_normalized
  | 6, _ => step_string
  | _ + 7, h => absurd h (by omega)

theorem ofRank_mono {v : MapVal T} {x : Nat} (h : den (ofRank x) v) :
    ∀ y, x ≤ y → y ≤ 7 → den (ofRank y) v := by
  intro y
  induction y with
  | zero => intro hx _; rw [Nat.le_zero.1 hx] at h; exact h
  | succ y ih =>
    intro hx hy
    rcases Nat.lt_or_ge x (y + 1) with hlt | hge
    · exact ofRank_step y (by omega) (ih (by omega) (by omega))
    · rw [show y + 1 = x by omega]; exact h

/-- **The chain inclusions.** -/
theorem chain_sub {a b : SName} {x y : Nat} (ha : chainRank a = some x) (hb : chainRank b = some y)
    (hxy : x ≤ y) {v : MapVal T} (h : den a v) : den b v := by
  obtain ⟨rfl, _⟩ := ofRank_of_chainRank ha
  obtain ⟨rfl, hy⟩ := ofRank_of_chainRank hb
  exact ofRank_mono h y hxy hy

/-- **The oracle's decisions on these names are sound for the OWL 2
datatype map.** -/
theorem oracleDec_sound : DecisionSound (den (T := T)) oracleDec := by
  intro a b y ha
  constructor
  · intro h
    cases a <;> cases b <;> simp [oracleDec, chainRank, family] at h ⊢ <;>
      first
      | exact ha
      | exact chain_sub rfl rfl (by decide) ha
      | exact step_dateTimeStamp ha
  · intro h hb
    cases a <;> cases b <;> simp [oracleDec, chainRank, family] at h <;>
      cases y <;> simp_all [den, denB]

/-- `xsd:dateTimeStamp ⊑ xsd:dateTime`. -/
theorem dateTimeStamp_sub_dateTime {v : MapVal T} : den .dateTimeStamp v → den .dateTime v :=
  step_dateTimeStamp

/-- `xsd:hexBinary ⊓ xsd:base64Binary = ∅`. -/
theorem hex_b64_disjoint {v : MapVal T} : den .hexBinary v → ¬ den .base64Binary v := by
  cases v <;> simp [den, denB]

/-! ## Strictness

`range_subsumed` answers `Some(false)` downwards in the chain; that is true
(every step has a witness). -/

/-- A witness of each step: a value of the type and not of the type below. -/
def witness : SName → MapVal T
  | .NCName => .str "_".toList none
  | .Name => .str "a:b".toList none
  | .NMTOKEN => .str "1".toList none
  | .token => .str "a b".toList none
  | .normalizedString => .str " a".toList none
  | .string => .str "\t".toList none
  | .PlainLiteral => .str "a".toList (some "en".toList)
  | _ => .str [] none

/-- The predecessor in the chain. -/
def below : SName → SName
  | .NCName => .language | .Name => .NCName | .NMTOKEN => .Name | .token => .NMTOKEN
  | .normalizedString => .token | .string => .normalizedString | .PlainLiteral => .string
  | n => n

theorem witness_spec : ∀ a : SName, a ∈ [SName.NCName, .Name, .NMTOKEN, .token,
    .normalizedString, .string, .PlainLiteral] →
    den a (witness (T := T) a) ∧ ¬ den (below a) (witness (T := T) a) := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, Bool.eq_false_iff.1 rfl⟩

/-- **Every inclusion of the chain is strict.** -/
theorem chain_strict {a b : SName} {x y : Nat} (ha : chainRank a = some x) (hb : chainRank b = some y)
    (hxy : y < x) : ∃ v : MapVal T, den a v ∧ ¬ den b v := by
  have hmem : a ∈ [SName.NCName, .Name, .NMTOKEN, .token, .normalizedString, .string,
      .PlainLiteral] := by
    cases a <;> simp [chainRank] at ha ⊢ <;> omega
  obtain ⟨h1, h2⟩ := witness_spec (T := T) a hmem
  refine ⟨witness a, h1, fun hbv => h2 ?_⟩
  have hbr : ∃ z, chainRank (below a) = some z ∧ y ≤ z := by
    cases a <;> simp [chainRank, below] at ha hmem ⊢ <;> omega
  obtain ⟨z, hz, hyz⟩ := hbr
  exact chain_sub hb hz hyz hbv

/-! ## Infinite differences

Every step of the chain has infinitely many witnesses (`step_family`), so a
label set whose least string type is `a` is realized by a fresh value of
`a` outside every type below it, avoiding any finite set of values. -/

theorem all_replicate_of {α : Type} {p : α → Bool} {c : α} (hp : p c = true) (n : Nat) :
    (List.replicate n c).all p = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, hp, ih]

theorem noDoubleSpace_of_nospace : ∀ s : List Char, (∀ x ∈ s, x ≠ ' ') → noDoubleSpace s = true
  | [], _ => rfl
  | [c], _ => by unfold noDoubleSpace; split <;> simp_all [noDoubleSpace]
  | c :: d :: ds, h => by
    have hc : c ≠ ' ' := h c (by simp)
    have ih := noDoubleSpace_of_nospace (d :: ds) (fun x hx => h x (by simp [hx]))
    unfold noDoubleSpace
    split
    · next heq => simp at heq; exact absurd heq.1 hc
    · next heq => simp at heq; obtain ⟨rfl, rfl⟩ := heq; exact ih
    · simp at *

theorem getLast?_ne_space {s : List Char} (h : ∀ x ∈ s, x ≠ ' ') : s.getLast? ≠ some ' ' := by
  intro hl
  exact h ' ' (List.mem_of_getLast? hl) rfl

theorem head?_ne_space {s : List Char} (h : ∀ x ∈ s, x ≠ ' ') : s.head? ≠ some ' ' := by
  intro hl
  exact h ' ' (List.mem_of_head? hl) rfl

/-- `a-a-…-a` with `n + 1` subtags. -/
def langWord : Nat → List Char
  | 0 => ['a']
  | n + 1 => 'a' :: '-' :: langWord n

theorem splitDash_langWord : ∀ n, splitDash (langWord n) = List.replicate (n + 1) ['a']
  | 0 => rfl
  | n + 1 => by
    simp only [langWord, splitDash, show ('a' : Char) ≠ '-' by decide, if_false,
      if_true, splitDash_langWord n]
    rfl

theorem langWord_chars : ∀ n, ∀ x ∈ langWord n, x = 'a' ∨ x = '-'
  | 0, x, h => by simp [langWord] at h; exact Or.inl h
  | n + 1, x, h => by
    simp only [langWord, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact langWord_chars n x h

theorem langWord_length : ∀ n, (langWord n).length = 2 * n + 1
  | 0 => rfl
  | n + 1 => by simp [langWord, langWord_length n]; omega

theorem all_of_mem {s : List Char} {p : Char → Bool} (h : ∀ x ∈ s, p x = true) : s.all p = true :=
  List.all_eq_true.2 h

/-- The witnesses of the steps (and of `language` itself). -/
def stepWord : SName → Nat → List Char
  | .language, n => langWord n
  | .NCName, n => '_' :: List.replicate n 'a'
  | .Name, n => ':' :: List.replicate n 'a'
  | .NMTOKEN, n => '1' :: List.replicate n 'a'
  | .token, n => 'a' :: ' ' :: List.replicate (n + 1) 'a'
  | .normalizedString, n => ' ' :: List.replicate n 'a'
  | .string, n => '\t' :: List.replicate n 'a'
  | _, n => List.replicate n 'a'

def stepVal (a : SName) (n : Nat) : MapVal T :=
  match a with
  | .PlainLiteral => .str (List.replicate n 'a') (some ['e', 'n'])
  | a => .str (stepWord a n) none

theorem stepVal_injective (a : SName) : Function.Injective (stepVal (T := T) a) := by
  intro i j h
  cases a <;> simp [stepVal, stepWord] at h <;>
    first
    | exact h
    | (have := congrArg List.length h; simp [langWord_length] at this; omega)
    | (have := congrArg List.length h.1; simp at this; omega)
    | (have := congrArg List.length h; simp at this; omega)

theorem replicate_a_mem {n : Nat} {x : Char} (h : x ∈ List.replicate n 'a') : x = 'a' :=
  List.eq_of_mem_replicate h

theorem rep_nospace (n : Nat) : ∀ x ∈ List.replicate n 'a', x ≠ ' ' := by
  intro x hx; rw [replicate_a_mem hx]; decide

theorem cons_rep_nospace {c : Char} (hc : c ≠ ' ') (n : Nat) :
    ∀ x ∈ c :: List.replicate n 'a', x ≠ ' ' := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact hc
  · exact rep_nospace n x hx

theorem getLast?_cons_rep {c : Char} (hc : c ≠ ' ') (n : Nat) :
    ¬ (c :: List.replicate n 'a').getLast? = some ' ' := getLast?_ne_space (cons_rep_nospace hc n)

theorem noDoubleSpace_cons_rep {c : Char} (hc : c ≠ ' ') (n : Nat) :
    noDoubleSpace (c :: List.replicate n 'a') = true :=
  noDoubleSpace_of_nospace _ (cons_rep_nospace hc n)

theorem getLast?_space_rep (n : Nat) :
    ¬ (' ' :: List.replicate (n + 1) 'a').getLast? = some ' ' := by
  rw [List.replicate_succ, List.getLast?_cons_cons]
  exact getLast?_cons_rep (by decide) n

theorem noDoubleSpace_token_word (n : Nat) :
    noDoubleSpace ('a' :: ' ' :: List.replicate (n + 1) 'a') = true := by
  rw [List.replicate_succ]
  show noDoubleSpace (' ' :: 'a' :: List.replicate n 'a') = true
  show noDoubleSpace ('a' :: List.replicate n 'a') = true
  exact noDoubleSpace_cons_rep (by decide) n

theorem languagePat_underscore (cs : List Char) : languagePat ('_' :: cs) = false := by
  obtain ⟨p, ps, he, _⟩ := splitDash_cons_ne (c := '_') (cs := cs) (by decide)
  simp only [languagePat, he, subtag, List.all_cons]
  simp [show alphaChar '_' = false by decide]

/-- **Infinite differences.** For every string type `a` of the chain, `stepVal a`
is an injective family of values of `a` outside the type below it. -/
theorem step_family (a : SName) (ha : (chainRank a).isSome = true) (n : Nat) :
    den a (stepVal (T := T) a n) ∧ (a = .language ∨ ¬ den (below a) (stepVal (T := T) a n)) := by
  have hrep : ∀ x ∈ List.replicate n 'a', x = 'a' := fun x hx => replicate_a_mem hx
  have hrep1 : ∀ x ∈ List.replicate (n + 1) 'a', x = 'a' := fun x hx => replicate_a_mem hx
  cases a <;> simp [chainRank] at ha
  case language =>
    refine ⟨?_, Or.inl rfl⟩
    have hc := langWord_chars n
    have hns : ∀ x ∈ langWord n, x ≠ ' ' := by
      intro x hx; rcases hc x hx with rfl | rfl <;> decide
    simp only [den, denB, stepVal, stepWord, isLanguage, isToken, isNormalized, isString,
      collapsed, replaced, languagePat, splitDash_langWord, Option.isNone_none, Bool.true_and,
      Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨all_of_mem fun x hx => ?_, all_of_mem fun x hx => ?_⟩,
      ⟨⟨⟨all_of_mem fun x hx => ?_, head?_ne_space hns⟩, getLast?_ne_space hns⟩,
        noDoubleSpace_of_nospace _ hns⟩⟩, ?_⟩
    · rcases hc x hx with rfl | rfl <;> decide
    · rcases hc x hx with rfl | rfl <;> decide
    · rcases hc x hx with rfl | rfl <;> decide
    · rw [List.replicate_succ]
      simp only [Bool.and_eq_true]
      exact ⟨by decide, all_replicate_of (by decide) n⟩
  all_goals simp [den, denB, stepVal, stepWord, below, isLanguage, isNCName, isName, isNMTOKEN,
    isToken, isNormalized, isString, isPlain, collapsed, replaced, nameShape, List.all_replicate,
    getLast?_cons_rep, noDoubleSpace_cons_rep, getLast?_space_rep, noDoubleSpace_token_word,
    languagePat_underscore, show xmlChar 'a' = true by decide, show xmlChar '_' = true by decide,
    show xmlChar ':' = true by decide, show xmlChar '1' = true by decide,
    show xmlChar ' ' = true by decide, show xmlChar '\t' = true by decide,
    show nameStartChar '_' = true by decide, show nameStartChar ':' = true by decide,
    show nameStartChar '1' = false by decide, show nameChar 'a' = true by decide,
    show nameChar '1' = true by decide, show nameChar ' ' = false by decide,
    show languagePat ['e', 'n'] = true by decide]


/-- A type strictly below `a` in the oracle's decisions excludes `stepVal a n`. -/
theorem step_avoids_inner (a b : SName) (ha : (chainRank a).isSome = true)
    (hba : oracleDec b a = some true) (hab : oracleDec a b ≠ some true) (n : Nat) :
    ¬ den b (stepVal (T := T) a n) := by
  intro hb
  obtain ⟨_, hbelow⟩ := step_family (T := T) a ha n
  cases a <;> cases b <;> simp [oracleDec, chainRank, family] at ha hba hab <;>
    simp only [below] at hbelow <;>
    first
    | exact absurd (chain_sub rfl rfl (by decide) hb) (hbelow.resolve_left (by decide))
    | exact absurd hb (hbelow.resolve_left (by decide))

/-! ## The oracle's membership test for string values

`derived_string_member` (`frontend/datatypes.rs`) decides whether a string
(no language tag) lies in a derived string type, with `None` for a name type
and a non-ASCII value. `rustMember` transcribes it; `rustMember_sound` shows
that every decision it makes is the datatype map's, for values whose
characters are XML characters. The frontend rejects every literal with a
character outside the XML character set (`conformance/lexical.rs`, "literal
contains a character outside the XML character set"), so the side condition
holds for every value the oracle sees. -/

def isAscii (c : Char) : Bool := c.toNat < 128

/-- `name_start` of `derived_string_member`. -/
def rustNameStart (c : Char) : Bool := alphaChar c || c == '_' || c == ':'

/-- `name_char` of `derived_string_member`. -/
def rustNameChar (c : Char) : Bool :=
  rustNameStart c || (0x30 ≤ c.toNat && c.toNat ≤ 0x39) || c == '-' || c == '.'

/-- The first character is a `name_start`. -/
def rustHead : List Char → Bool
  | [] => false
  | c :: _ => rustNameStart c

/-- `derived_string_member(kind, value)`. -/
def rustMember (k : SName) (s : List Char) : Option Bool :=
  match k with
  | .string => some true
  | .normalizedString => some (replaced s)
  | .token => some (collapsed s)
  | .language | .NMTOKEN | .Name | .NCName =>
    if !collapsed s then some false
    else if !(s.all isAscii) then none
    else match k with
      | .language => some (languagePat s)
      | .NMTOKEN => some (!s.isEmpty && s.all rustNameChar)
      | .Name => some (rustHead s && s.all rustNameChar)
      | .NCName => some (rustHead s && s.all rustNameChar && !(s.contains ':'))
      | _ => none
  | _ => none

theorem rustNameStart_iff {c : Char} (h : isAscii c = true) :
    rustNameStart c = true ↔ nameStartChar c = true := by
  simp only [isAscii, decide_eq_true_eq] at h
  have h1 : c = '_' ↔ c.toNat = 0x5F := by
    rw [← Char.toNat_inj]; rfl
  have h2 : c = ':' ↔ c.toNat = 0x3A := by
    rw [← Char.toNat_inj]; rfl
  simp only [rustNameStart, alphaChar, nameStartChar, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, h1, h2]
  omega

theorem rustNameStart_eq {c : Char} (h : isAscii c = true) : rustNameStart c = nameStartChar c :=
  Bool.eq_iff_iff.2 (rustNameStart_iff h)

theorem rustNameChar_iff {c : Char} (h : isAscii c = true) :
    rustNameChar c = true ↔ nameChar c = true := by
  simp only [isAscii, decide_eq_true_eq] at h
  have h1 : c = '-' ↔ c.toNat = 0x2D := by
    rw [← Char.toNat_inj]; rfl
  have h2 : c = '.' ↔ c.toNat = 0x2E := by
    rw [← Char.toNat_inj]; rfl
  have h3 : c = '_' ↔ c.toNat = 0x5F := by
    rw [← Char.toNat_inj]; rfl
  have h4 : c = ':' ↔ c.toNat = 0x3A := by
    rw [← Char.toNat_inj]; rfl
  simp only [rustNameChar, rustNameStart, alphaChar, nameChar, nameStartChar, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h1, h2, h3, h4]
  omega

theorem rustNameChar_eq {c : Char} (h : isAscii c = true) : rustNameChar c = nameChar c :=
  Bool.eq_iff_iff.2 (rustNameChar_iff h)

theorem all_congr_ascii {s : List Char} {p q : Char → Bool} (ha : s.all isAscii = true)
    (h : ∀ c, isAscii c = true → p c = q c) : s.all p = s.all q := by
  simp only [List.all_eq_true] at ha
  induction s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons]
    rw [h c (ha c (by simp)), ih (fun x hx => ha x (by simp [hx]))]

theorem collapsed_replaced {s : List Char} (h : collapsed s = true) : replaced s = true := by
  simp only [collapsed, Bool.and_eq_true] at h
  exact h.1.1.1

theorem nameShape_eq {s : List Char} (ha : s.all isAscii = true) :
    nameShape s = (rustHead s && s.all rustNameChar) := by
  cases s with
  | nil => rfl
  | cons c cs =>
    have hca : isAscii c = true := by simp at ha; exact ha.1
    have hcs : cs.all isAscii = true := by simp at ha ⊢; exact ha.2
    rw [List.all_cons, all_congr_ascii hcs (fun x hx => rustNameChar_eq hx), rustHead,
      rustNameStart_eq hca, rustNameChar_eq hca]
    simp only [nameShape]
    cases h : nameStartChar c
    · rfl
    · rw [nameStart_nameChar h]; rfl

/-- **The oracle's string-membership decisions are the datatype map's.** -/
theorem rustMember_sound {T : Type} (k : SName) (s : List Char) (hx : s.all xmlChar = true)
    (b : Bool) (h : rustMember k s = some b) : denB (T := T) k (.str s none) = b := by
  cases k with
  | string => simp [rustMember] at h; subst h; simp [denB, isString, hx]
  | normalizedString => simp [rustMember] at h; subst h; simp [denB, isNormalized, isString, hx]
  | token =>
    simp [rustMember] at h; subst h
    cases hc : collapsed s <;> simp [denB, isToken, isNormalized, isString, hx, hc,
      collapsed_replaced]
  | language | NMTOKEN | Name | NCName =>
    simp only [rustMember] at h
    by_cases hc : collapsed s = true
    · have htok : isToken s none = true := by
        simp [isToken, isNormalized, isString, hx, hc, collapsed_replaced hc]
      by_cases ha : s.all isAscii = true
      · simp only [hc, ha, Bool.not_true, Bool.false_eq_true, if_false] at h
        simp only [Option.some.injEq] at h
        subst h
        have hn := all_congr_ascii ha (fun c hc => rustNameChar_eq hc)
        simp only [denB, isLanguage, isNMTOKEN, isName, isNCName, htok, Bool.true_and,
          nameShape_eq ha, hn]
      · simp [hc, ha] at h
    · simp [hc] at h; subst h
      simp [denB, isLanguage, isNMTOKEN, isName, isNCName, isToken, hc]
  | _ => simp [rustMember] at h

end ContextCalculus.DataRangeStrings
