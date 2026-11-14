import ContextCalculus.OWL.Datatypes.Lexical
import Mathlib.Data.Real.Basic
import Mathlib.Order.WithBot

/-!
# The OWL 2 datatype map as an `OWL.DatatypeMap` (v1.7.0 stage C4)

`owl2MapP pat` is the OWL 2 datatype map (Structural Specification,
section 4) as a `DatatypeMap` of `OWL/Semantics.lean`:

* values `Val = ValOf ℝ` (`OWL/Datatypes/Lexical.lean`): `owl:real` is
  modelled by the real numbers, so `DataIntersectionOf(owl:real
  DataComplementOf(owl:rational))` is infinite, as in the specification;
* `datatype t`: the value space of the datatype of kind `kindOf t`
  (`kindSem`);
* `literal l`: the value of `litVal l`, with its rational number read as a
  real;
* `facet t f l`: the constraining facets of the map (`facetSem`):
  `xsd:minInclusive`, `xsd:maxInclusive`, `xsd:minExclusive`,
  `xsd:maxExclusive` on the numeric types (facet values in `owl:real`), on
  `xsd:double` and `xsd:float` (facet values of the same type, IEEE order
  with `-0 = +0`, NaN comparable to nothing) and on `xsd:dateTime` and
  `xsd:dateTimeStamp` (the partial order of XML Schema 1.1 with the
  14-hour rule for values without a timezone); `xsd:length`,
  `xsd:minLength`, `xsd:maxLength` on the string types, `xsd:anyURI` and
  `rdf:PlainLiteral` (characters of the string part) and on the binary
  types (octets); `xsd:pattern` on the string types, `xsd:anyURI` and
  `rdf:PlainLiteral`; `rdf:langRange` on `rdf:PlainLiteral` (basic
  filtering of RFC 4647). A facet that does not apply to the datatype,
  or a facet value outside the facet's value space, gives `none` (the
  restriction is empty).

**Approximation `pat`**: `xsd:pattern` is read through the parameter
`pat regex s` ("`s` matches the XML Schema regular expression `regex`");
XML Schema regular expressions are not implemented. Statements about
`owl2MapP pat` that hold for every `pat` hold for the true matcher.

The other approximations are the ones named in
`OWL/Datatypes/Lexical.lean` (`xmlLexical`, `langTagOK`).
-/

namespace ContextCalculus.OWL.Datatypes

/-- The data values of the map. -/
abbrev Val := ValOf ℝ

/-- A literal value as a value of the map. -/
noncomputable def toVal : ValOf ℚ → Val := ValOf.map fun q : ℚ => (q : ℝ)

/-- `x` has a finite decimal expansion. -/
def IsDecimalR (x : ℝ) : Prop := ∃ (z : ℤ) (k : ℕ), x = (z : ℝ) / 10 ^ k

/-- `t` has a finite decimal expansion. -/
def IsDecimalQ (t : ℚ) : Prop := ∃ (z : ℤ) (k : ℕ), t = (z : ℚ) / 10 ^ k

/-- A string value without a language tag whose string passes `ok`. -/
def strSem (ok : List Char → Bool) (v : Val) : Prop :=
  ∃ s, v = .str s none ∧ xmlString s = true ∧ ok s.toList = true

/-- The value space of a datatype of kind `k`. -/
def kindSem : Kind → Val → Prop
  | .real => fun v => ∃ x, v = .num x
  | .rational => fun v => ∃ q : ℚ, v = .num (q : ℝ)
  | .decimal => fun v => ∃ x, v = .num x ∧ IsDecimalR x
  | .integer lo hi => fun v =>
      ∃ z : ℤ, v = .num (z : ℝ) ∧ (∀ l ∈ lo, l ≤ z) ∧ ∀ h ∈ hi, z ≤ h
  | .double => fun v => ∃ x, v = .dbl x
  | .float => fun v => ∃ x, v = .flt x
  | .string => strSem fun _ => true
  | .normalizedString => strSem isNormalizedX
  | .token => strSem isTokenX
  | .language => strSem Parse.isLanguageTag
  | .name => strSem isNameX
  | .ncName => strSem isNCNameX
  | .nmToken => strSem isNmtokenX
  | .plainLiteral => fun v => ∃ s, xmlString s = true ∧
      (v = .str s none ∨ ∃ t, v = .str s (some t) ∧ langTagOK t.toList = true ∧ lowerTag t = t)
  | .boolean => fun v => ∃ b, v = .bool b
  | .hexBinary => fun v => ∃ bs, v = .hex bs
  | .base64Binary => fun v => ∃ bs, v = .b64 bs
  | .anyURI => fun v => ∃ s, v = .uri s ∧ xmlString s = true
  | .dateTime => fun v => ∃ t z, v = .time t z ∧ IsDecimalQ t
  | .dateTimeStamp => fun v => ∃ t, v = .time t true ∧ IsDecimalQ t
  | .xmlLiteral => fun v => ∃ s, v = .xml s ∧ xmlString s = true
  | .literal => fun _ => True

/-! ## Facets -/

/-- The four bound facets, by local name: `(minimum?, strict?)`. -/
def boundFacet (f : IRI) : Option (Bool × Bool) :=
  if f = Parse.xsdNs ++ "minInclusive" then some (true, false)
  else if f = Parse.xsdNs ++ "minExclusive" then some (true, true)
  else if f = Parse.xsdNs ++ "maxInclusive" then some (false, false)
  else if f = Parse.xsdNs ++ "maxExclusive" then some (false, true)
  else none

/-- The three length facets: `0` length, `1` minLength, `2` maxLength. -/
def lengthFacet (f : IRI) : Option (Fin 3) :=
  if f = Parse.xsdNs ++ "length" then some 0
  else if f = Parse.xsdNs ++ "minLength" then some 1
  else if f = Parse.xsdNs ++ "maxLength" then some 2
  else none

/-- A bound facet `b` with facet value `y`, on a linear order. -/
def boundRel {α : Type} [LinearOrder α] (b : Bool × Bool) (x y : α) : Prop :=
  match b with
  | (true, false) => y ≤ x
  | (true, true) => y < x
  | (false, false) => x ≤ y
  | (false, true) => x < y

/-- A length facet with value `n`. -/
def lengthRel (k : Fin 3) (len n : Nat) : Prop :=
  if k = 0 then len = n else if k = 1 then n ≤ len else len ≤ n

/-- The position of a float in the IEEE order: `none` for NaN, `⊥` and `⊤`
for the infinities; both zeros are `0`. -/
def FloatV.key {e m : Nat} : FloatV e m → Option (WithBot (WithTop ℚ))
  | .nan => none
  | .inf true => some ⊥
  | .inf false => some ⊤
  | x@(.fin ..) => (x.toRat?).map fun q => ((q : WithTop ℚ) : WithBot (WithTop ℚ))

/-- A bound facet on floats: both sides comparable. -/
def floatRel {e m : Nat} (b : Bool × Bool) (x y : FloatV e m) : Prop :=
  ∃ kx ky, x.key = some kx ∧ y.key = some ky ∧ boundRel b kx ky

/-- `(t₁, z₁) < (t₂, z₂)` in the order of `xsd:dateTime` (XML Schema 1.1):
the timeline order if both or neither have a timezone; otherwise the
value without a timezone may lie 14 hours either way. -/
def timeLt (a b : ℚ × Bool) : Prop :=
  if a.2 = b.2 then a.1 < b.1 else a.1 + 50400 < b.1

/-- A bound facet on `dateTime` values (a partial order: `≥` is `>` or
`=`). -/
def timeRel (b : Bool × Bool) (x y : ℚ × Bool) : Prop :=
  match b with
  | (true, false) => timeLt y x ∨ x = y
  | (true, true) => timeLt y x
  | (false, false) => timeLt x y ∨ x = y
  | (false, true) => timeLt x y

/-- Basic filtering (RFC 4647, section 3.3.1) of a lower-case tag by a
language range. -/
def langMatch (range tag : String) : Prop :=
  tag ≠ "" ∧ (range = "*" ∨ lowerTag range = tag ∨ (lowerTag range ++ "-").isPrefixOf tag = true)

/-- The string part of a value, for the length and pattern facets. -/
def strPart : Val → Option String
  | .str s _ => some s
  | .uri s => some s
  | _ => none

/-- The octets of a binary value. -/
def octets : Val → Option (List UInt8)
  | .hex bs => some bs
  | .b64 bs => some bs
  | _ => none

/-- The kinds with the string facets. -/
def stringish : Kind → Bool
  | .string | .normalizedString | .token | .language | .name | .ncName | .nmToken
  | .anyURI | .plainLiteral => true
  | _ => false

/-- The kinds of the numeric tower. -/
def numeric : Kind → Bool
  | .real | .rational | .decimal | .integer .. => true
  | _ => false

/-- The constraining facet `f` with the facet value `lv` on a datatype of
kind `k`; `pat` reads `xsd:pattern`. -/
noncomputable def facetSem (pat : String → String → Prop) (k : Kind) (f : IRI)
    (lv : Option (ValOf ℚ)) : Option (Val → Prop) :=
  match boundFacet f, lv with
  | some b, some (.num q) =>
      if numeric k then some fun v => ∃ x, v = .num x ∧ boundRel b x (q : ℝ) else none
  | some b, some (.dbl y) =>
      if k = .double then some fun v => ∃ x, v = .dbl x ∧ floatRel b x y else none
  | some b, some (.flt y) =>
      if k = .float then some fun v => ∃ x, v = .flt x ∧ floatRel b x y else none
  | some b, some (.time t z) =>
      if k = .dateTime ∨ k = .dateTimeStamp then
        some fun v => ∃ t' z', v = .time t' z' ∧ timeRel b (t', z') (t, z)
      else none
  | some _, _ => none
  | none, _ =>
    match lengthFacet f, lv with
    | some L, some (.num q) =>
        if q.den = 1 ∧ 0 ≤ q.num then
          if stringish k then
            some fun v => ∃ s, strPart v = some s ∧ lengthRel L s.length q.num.toNat
          else if k = .hexBinary ∨ k = .base64Binary then
            some fun v => ∃ bs, octets v = some bs ∧ lengthRel L bs.length q.num.toNat
          else none
        else none
    | some _, _ => none
    | none, some (.str p none) =>
        if f = Parse.xsdNs ++ "pattern" ∧ stringish k then
          some fun v => ∃ s, strPart v = some s ∧ pat p s
        else if f = Parse.rdfNs ++ "langRange" ∧ k = .plainLiteral then
          some fun v => ∃ s t, v = .str s (some t) ∧ langMatch p t
        else none
    | none, _ => none

/-- **The OWL 2 datatype map**, with `xsd:pattern` read by `pat`. -/
noncomputable def owl2MapP (pat : String → String → Prop) : DatatypeMap where
  Val := Val
  datatype t := (kindOf t).map kindSem
  literal l := (litVal l).map toVal
  facet t f l :=
    match kindOf t with
    | some k => facetSem pat k f (litVal l)
    | none => none

theorem owl2MapP_literal (pat : String → String → Prop) (l : Literal) :
    (owl2MapP pat).literal l = (litVal l).map toVal := rfl

theorem toVal_injective : Function.Injective toVal := by
  intro a b h
  cases a <;> cases b <;> simp_all [toVal, ValOf.map]

/-- Two literals denote the same value of the map iff `litVal` gives the
same value. -/
theorem owl2MapP_literal_eq (pat : String → String → Prop) (l1 l2 : Literal) :
    (owl2MapP pat).literal l1 = (owl2MapP pat).literal l2 ↔ litVal l1 = litVal l2 := by
  rw [owl2MapP_literal, owl2MapP_literal]
  exact Option.map_injective toVal_injective |>.eq_iff

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.owl2MapP_literal_eq
