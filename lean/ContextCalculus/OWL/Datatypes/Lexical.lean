import ContextCalculus.OWL.Parse
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Power

/-!
# The OWL 2 datatype map: kinds, values and lexical-to-value mappings (v1.7.0 stage C4)

The OWL 2 Structural Specification, section 4, fixes the datatype map: the
datatypes, their value spaces, their lexical-to-value mappings and their
facets. This file holds the computable half: the datatype kinds
(`Kind`, `kindOf`), the values with a numeric component `R` (`ValOf R`),
and the value of each literal (`litVal`), with numbers as rationals. Every
literal of the map denotes a rational number or a non-numeric value, so
`ValOf ℚ` holds every literal value; `OWL/Datatypes/Map.lean` embeds it
into `ValOf ℝ`, the value type of the map.

## Value spaces (`ValOf R`)

* `num x`: the value space of `owl:real`. `owl:rational`, `xsd:decimal`,
  `xsd:integer` and the integer types derived from it are subsets
  (section 4.1). `"1"^^xsd:integer` and `"1.0"^^xsd:decimal` both denote
  `num 1`.
* `dbl x` and `flt x`: `xsd:double` and `xsd:float` (section 4.2). Their
  value spaces are disjoint from each other and from `owl:real`. A value
  is an IEEE 754 bit pattern up to the NaN payload (`FloatV e m`): a
  finite value by sign, biased exponent and fraction (so `+0` and `-0`
  are different values), the two infinities and one NaN. Data values are
  equal when they are identical, so `NaN` equals itself and `+0` differs
  from `-0` as values (the order of the facets treats them as equal).
* `str s none` and `str s (some tag)`: `rdf:PlainLiteral` (section 4.3):
  strings without and with a language tag, the tag in lower case. The
  values of `xsd:string` are the ones without a tag; its derived types
  are subsets.
* `bool b`: `xsd:boolean` (section 4.4).
* `hex bs` and `b64 bs`: `xsd:hexBinary` and `xsd:base64Binary` (section
  4.5), finite sequences of octets, as two disjoint value spaces (see
  "Points to check" below).
* `uri s`: `xsd:anyURI` (section 4.6), disjoint from the strings.
* `time t tz`: `xsd:dateTime` (section 4.7): `tz` is the timezone offset
  in minutes (`none` without a timezone); `t` is the instant in seconds from
  1970-01-01T00:00:00 UTC when there is an offset, the local time in
  seconds otherwise. The offset is part of the value: section 4.7 says that
  two values for the same instant with different offsets are equal but not
  identical, and OWL 2 value spaces use identity.
  `"2008-07-08T20:44:11.656+01:00"` and `"2008-07-08T19:44:11.656Z"` are
  two values. `Z`, `+00:00` and `-00:00` are the offset `0` (XML Schema
  1.1, `timezoneOffset`), and `24:00:00` is `00:00:00` of the next day
  (XML Schema 1.1, `dateTimeLexicalMap`). `xsd:dateTimeStamp` is the part
  with an offset.
* `xml s`: `rdf:XMLLiteral` (section 4.8).
* `extra n`: data values outside every value space of the map. The direct
  semantics (section 2.2) only asks the data domain to contain the value
  spaces of the map; datatypes outside the map may hold further values.
  Without these values, `DataSomeValuesFrom(p DataComplementOf(D))` with
  `D` the union of the map's datatypes would be unsatisfiable, which the
  direct semantics does not say.

## Approximations (each named)

* `xmlLexical`: `rdf:XMLLiteral` takes every string of XML characters as
  a lexical form and as its own value; the specification asks for a
  well-balanced XML fragment and takes its canonical form as the value.
* `langTagOK`: language tags follow `[a-zA-Z]{1,8}(-[a-zA-Z0-9]{1,8})*`
  (the pattern of `xsd:language`, the check of the OFN parser), a
  superset of the BCP 47 well-formed tags that `rdf:PlainLiteral` asks for.

The other lexical mappings follow XML Schema 1.1 Part 2 (as cited by the
OWL 2 specification): decimal, integer and rational literals exactly,
`xsd:double` and `xsd:float` by rounding to nearest with ties to even and
overflow to the infinities (`roundFloat`), `xsd:dateTime` through the
proleptic Gregorian calendar with year 0 (`daysFromCivil`), the string
types with the XML 1.0 (fifth edition) `Char`, `Name`, `NCName` and
`Nmtoken` productions, `xsd:base64Binary` with the canonical-padding rule
of XML Schema 1.1.

## Sources of the identity choices (Structural Specification, section 4)

* numbers: "The value space of owl:real is the set of all real numbers";
  `owl:rational` "is a subset of the value space of owl:real, and it
  contains the value space of xsd:decimal"; the integer types take their
  value spaces from XML Schema (subsets of the decimals).
* floats: "the value spaces of xsd:double, xsd:float, and xsd:decimal are
  pairwise disjoint" and "the value space of owl:real is defined as being
  disjoint with the value spaces of xsd:double and xsd:float as well";
  positive and negative zero are "equal, but not identical". Section 4 does
  not mention NaN; XML Schema 1.1 (datatypes `float` and `double`) makes NaN
  identical to itself and equal to nothing, which is the choice here (the
  facet order excludes NaN, `FloatV.key`).
* strings: "the value spaces of all of these datatypes are contained in the
  value space of rdf:PlainLiteral"; the lower-case tags follow the
  rdf:PlainLiteral specification.
* binary: "the value spaces of these two datatypes are disjoint" (they are
  "isomorphic copies").
* anyURI: "IRIs are not strings" and "the value spaces of xsd:anyURI and
  xsd:string are disjoint".
* dateTime: two values for the same instant with different offsets are
  "equal, but nonidentical data values".
* facets: "equality is used only in the definition of facets".
-/

namespace ContextCalculus.OWL.Datatypes

open ContextCalculus.OWL.Parse (xsdNs rdfNs owlNs rdfPlainLiteral isDigitC isHexC isAlphaC
  digitsVal parseInt isDecimal isFloat isLanguageTag twoDigits daysIn isTimezone isDateTime
  isRational)

/-! ## Kinds -/

/-- The datatypes of the OWL 2 datatype map, with `xsd:double` and
`xsd:float` apart and the integer types by their bounds. -/
inductive Kind where
  | real
  | rational
  | decimal
  /-- An integer type with optional lower and upper bounds. -/
  | integer (lo hi : Option Int)
  | double
  | float
  | string
  | normalizedString
  | token
  | language
  | name
  | ncName
  | nmToken
  | plainLiteral
  | boolean
  | hexBinary
  | base64Binary
  | anyURI
  | dateTime
  | dateTimeStamp
  | xmlLiteral
  /-- `rdfs:Literal`. -/
  | literal
deriving DecidableEq, Repr

/-- The kind of a datatype IRI of the OWL 2 datatype map, `none` for any
other IRI (the table of `Parse.dtKind` with `double` and `float` apart). -/
def kindOf (dt : IRI) : Option Kind :=
  let xsd : List (String × Kind) :=
    [("decimal", .decimal), ("integer", .integer none none),
     ("nonNegativeInteger", .integer (some 0) none),
     ("nonPositiveInteger", .integer none (some 0)),
     ("positiveInteger", .integer (some 1) none),
     ("negativeInteger", .integer none (some (-1))),
     ("long", .integer (some (-9223372036854775808)) (some 9223372036854775807)),
     ("int", .integer (some (-2147483648)) (some 2147483647)),
     ("short", .integer (some (-32768)) (some 32767)),
     ("byte", .integer (some (-128)) (some 127)),
     ("unsignedLong", .integer (some 0) (some 18446744073709551615)),
     ("unsignedInt", .integer (some 0) (some 4294967295)),
     ("unsignedShort", .integer (some 0) (some 65535)),
     ("unsignedByte", .integer (some 0) (some 255)),
     ("double", .double), ("float", .float),
     ("string", .string), ("normalizedString", .normalizedString), ("token", .token),
     ("language", .language), ("Name", .name), ("NCName", .ncName),
     ("NMTOKEN", .nmToken), ("boolean", .boolean), ("hexBinary", .hexBinary),
     ("base64Binary", .base64Binary), ("anyURI", .anyURI), ("dateTime", .dateTime),
     ("dateTimeStamp", .dateTimeStamp)]
  if dt == owlNs ++ "real" then some .real
  else if dt == owlNs ++ "rational" then some .rational
  else if dt == rdfPlainLiteral then some .plainLiteral
  else if dt == rdfNs ++ "XMLLiteral" then some .xmlLiteral
  else if dt == rdfsLiteral then some .literal
  else if dt.startsWith xsdNs then xsd.lookup (dt.drop xsdNs.length).toString
  else none

/-! ## Floating-point values -/

/-- IEEE 754 binary values with `e` exponent bits and `m` fraction bits,
up to the NaN payload: finite values by sign, biased exponent (`0` for
zero and the subnormals) and fraction; the two infinities; one NaN. -/
inductive FloatV (e m : Nat) where
  | fin (neg : Bool) (E : Fin (2 ^ e - 1)) (M : Fin (2 ^ m))
  | inf (neg : Bool)
  | nan
deriving DecidableEq, Repr

namespace FloatV

variable {e m : Nat}

/-- The exponent bias `2^(e-1) - 1`. -/
def bias (e : Nat) : Int := 2 ^ (e - 1) - 1

/-- The number of a finite value, `none` for the infinities and NaN. -/
def toRat? : FloatV e m → Option ℚ
  | fin neg E M =>
    let mag : ℚ :=
      if E.val = 0 then (M.val : ℚ) * (2 : ℚ) ^ (1 - bias e - (m : Int))
      else ((2 ^ m + M.val : Nat) : ℚ) * (2 : ℚ) ^ ((E.val : Int) - bias e - (m : Int))
    some (if neg then -mag else mag)
  | _ => none

/-- A signed zero. -/
def zero (neg : Bool) : FloatV e m :=
  if h : 0 < 2 ^ e - 1 then fin neg ⟨0, h⟩ ⟨0, Nat.two_pow_pos m⟩ else nan

end FloatV

/-- `⌊log₂ q⌋` for `q > 0`. -/
def floorLog2 (q : ℚ) : Int :=
  let k0 : Int := (Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)
  if q < (2 : ℚ) ^ k0 then k0 - 1 else if (2 : ℚ) ^ (k0 + 1) ≤ q then k0 + 1 else k0

/-- Rounding a nonnegative rational to the nearest natural number, ties to
even. -/
def roundHalfEven (s : ℚ) : Nat :=
  let f := ⌊s⌋
  let r := s - f
  (if r > 1 / 2 ∨ (r = 1 / 2 ∧ f % 2 = 1) then f + 1 else f).toNat

/-- The float nearest to `±q` (`q ≥ 0`, sign `neg`): round to nearest,
ties to even, overflow to the infinity, underflow to the signed zero
(IEEE 754 and XML Schema 1.1, `floatLexicalMap`). -/
def roundFloat (e m : Nat) (neg : Bool) (q : ℚ) : FloatV e m :=
  if q ≤ 0 then FloatV.zero neg
  else
    let emin : Int := 1 - FloatV.bias e
    let emax : Int := FloatV.bias e
    let ex0 := max (floorLog2 q) emin
    let N0 := roundHalfEven (q / (2 : ℚ) ^ (ex0 - (m : Int)))
    let ex := if N0 = 2 ^ (m + 1) then ex0 + 1 else ex0
    let N := if N0 = 2 ^ (m + 1) then 2 ^ m else N0
    if emax < ex then .inf neg
    else if hN : N < 2 ^ m then
      -- subnormal or zero: `ex = emin`
      if hE : 0 < 2 ^ e - 1 then .fin neg ⟨0, hE⟩ ⟨N, hN⟩ else .nan
    else
      let E := (ex + FloatV.bias e).toNat
      if hE : E < 2 ^ e - 1 then
        if hM : N - 2 ^ m < 2 ^ m then .fin neg ⟨E, hE⟩ ⟨N - 2 ^ m, hM⟩ else .inf neg
      else .inf neg

/-! ## Values -/

/-- The data values, with numbers in `R` (see the module docstring). -/
inductive ValOf (R : Type) where
  | num (x : R)
  | dbl (x : FloatV 11 52)
  | flt (x : FloatV 8 23)
  | str (s : String) (lang : Option String)
  | bool (b : Bool)
  | hex (bs : List UInt8)
  | b64 (bs : List UInt8)
  | uri (s : String)
  | time (t : ℚ) (tz : Option Int)
  | xml (s : String)
  | extra (n : Nat)
deriving DecidableEq, Repr

/-- Changing the numbers. -/
def ValOf.map {R S : Type} (f : R → S) : ValOf R → ValOf S
  | .num x => .num (f x)
  | .dbl x => .dbl x
  | .flt x => .flt x
  | .str s l => .str s l
  | .bool b => .bool b
  | .hex bs => .hex bs
  | .b64 bs => .b64 bs
  | .uri s => .uri s
  | .time t z => .time t z
  | .xml s => .xml s
  | .extra n => .extra n

/-! ## Characters and names (XML 1.0, fifth edition) -/

/-- The XML `Char` production. -/
def isXMLChar (c : Char) : Bool :=
  let n := c.toNat
  n == 0x9 || n == 0xA || n == 0xD || (0x20 ≤ n && n ≤ 0xD7FF) ||
    (0xE000 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- A string of XML characters. -/
def xmlString (s : String) : Bool := s.toList.all isXMLChar

/-- The XML `NameStartChar` production. -/
def isNameStartX (c : Char) : Bool :=
  let n := c.toNat
  c == ':' || isAlphaC c || c == '_' || (0xC0 ≤ n && n ≤ 0xD6) || (0xD8 ≤ n && n ≤ 0xF6) ||
    (0xF8 ≤ n && n ≤ 0x2FF) || (0x370 ≤ n && n ≤ 0x37D) || (0x37F ≤ n && n ≤ 0x1FFF) ||
    (0x200C ≤ n && n ≤ 0x200D) || (0x2070 ≤ n && n ≤ 0x218F) || (0x2C00 ≤ n && n ≤ 0x2FEF) ||
    (0x3001 ≤ n && n ≤ 0xD7FF) || (0xF900 ≤ n && n ≤ 0xFDCF) || (0xFDF0 ≤ n && n ≤ 0xFFFD) ||
    (0x10000 ≤ n && n ≤ 0xEFFFF)

/-- The XML `NameChar` production. -/
def isNameCharX (c : Char) : Bool :=
  let n := c.toNat
  isNameStartX c || c == '-' || c == '.' || isDigitC c || n == 0xB7 ||
    (0x300 ≤ n && n ≤ 0x36F) || (0x203F ≤ n && n ≤ 0x2040)

/-- `Name`. -/
def isNameX (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | c :: rest => isNameStartX c && rest.all isNameCharX

/-- `NCName`: a `Name` without a colon. -/
def isNCNameX (cs : List Char) : Bool := isNameX cs && !cs.contains ':'

/-- `Nmtoken`. -/
def isNmtokenX (cs : List Char) : Bool := !cs.isEmpty && cs.all isNameCharX

/-- No tab, line feed or carriage return (`xsd:normalizedString`). -/
def isNormalizedX (cs : List Char) : Bool := cs.all fun c => c != '\t' && c != '\n' && c != '\r'

/-- `xsd:token`: normalized, no leading or trailing space, no two
adjacent spaces. -/
def isTokenX (cs : List Char) : Bool :=
  isNormalizedX cs && cs.head? != some ' ' && cs.getLast? != some ' ' &&
    !(cs.zip cs.tail).any fun (a, b) => a == ' ' && b == ' '

/-- **Approximation `langTagOK`**: the pattern of `xsd:language`
(see the module docstring). -/
def langTagOK (cs : List Char) : Bool := isLanguageTag cs

/-- A language tag in lower case (ASCII letters only occur in tags). -/
def lowerTag (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-! ## Numbers -/

/-- Split an optional sign. -/
def splitSign : List Char → Bool × List Char
  | '-' :: ds => (true, ds)
  | '+' :: ds => (false, ds)
  | ds => (false, ds)

/-- The value of an `xsd:decimal` lexical form. -/
def parseDecimalQ (cs : List Char) : Option ℚ :=
  if !isDecimal cs then none
  else
    let (neg, ds) := splitSign cs
    let mag : Option ℚ := match ds.splitOn '.' with
      | [a] => some (digitsVal a : ℚ)
      | [a, b] => some ((digitsVal a : ℚ) + (digitsVal b : ℚ) / (10 : ℚ) ^ b.length)
      | _ => none
    mag.map fun x => if neg then -x else x

/-- The value of an `owl:rational` lexical form `n/d`. -/
def parseRationalQ (cs : List Char) : Option ℚ :=
  if !isRational cs then none
  else match cs.splitOn '/' with
    | [n, d] => (parseInt n).map fun z => (z : ℚ) / (digitsVal d : ℚ)
    | _ => none

/-- The value of an `xsd:double` (`e = 11`, `m = 52`) or `xsd:float`
(`e = 8`, `m = 23`) lexical form. -/
def parseFloatV (e m : Nat) (cs : List Char) : Option (FloatV e m) :=
  if !isFloat cs then none
  else if cs == "INF".toList || cs == "+INF".toList then some (.inf false)
  else if cs == "-INF".toList then some (.inf true)
  else if cs == "NaN".toList then some .nan
  else
    let neg := cs.head? == some '-'
    let (mant, ex) : List Char × Int := match cs.findIdx? (fun c => c == 'e' || c == 'E') with
      | none => (cs, 0)
      | some i => (cs.take i, (parseInt (cs.drop (i + 1))).getD 0)
    match parseDecimalQ mant with
    | some q => some (roundFloat e m neg (|q| * (10 : ℚ) ^ ex))
    | none => none

/-! ## Binary data -/

def hexVal (c : Char) : Nat :=
  if isDigitC c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- The octets of an `xsd:hexBinary` lexical form. -/
def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest =>
    if isHexC a && isHexC b then (parseHex rest).map fun t => (16 * hexVal a + hexVal b).toUInt8 :: t
    else none
  | [_] => none

def b64Val (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if isDigitC c then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- Single spaces between characters only (XML Schema 1.1: a space may
follow each character except at the end). -/
def b64Spaces (cs : List Char) : Bool :=
  cs.head? != some ' ' && cs.getLast? != some ' ' &&
    !(cs.zip cs.tail).any fun (a, b) => a == ' ' && b == ' '

/-- Decode groups of four characters. The final group may end in `=` or
`==`, and then its unused bits must be zero (XML Schema 1.1, `B16` and
`B04`). -/
def b64Groups : List Char → Option (List UInt8)
  | [] => some []
  | [a, b, '=', '='] => do
    let x ← b64Val a
    let y ← b64Val b
    if y % 16 != 0 then none else some [(4 * x + y / 16).toUInt8]
  | [a, b, c, '='] => do
    let x ← b64Val a
    let y ← b64Val b
    let z ← b64Val c
    if z % 4 != 0 then none
    else some [(4 * x + y / 16).toUInt8, (16 * (y % 16) + z / 4).toUInt8]
  | a :: b :: c :: d :: rest => do
    let x ← b64Val a
    let y ← b64Val b
    let z ← b64Val c
    let w ← b64Val d
    let t ← b64Groups rest
    some ((4 * x + y / 16).toUInt8 :: (16 * (y % 16) + z / 4).toUInt8 :: (64 * (z % 4) + w).toUInt8 :: t)
  | _ => none

/-- The octets of an `xsd:base64Binary` lexical form. -/
def parseB64 (cs : List Char) : Option (List UInt8) :=
  if b64Spaces cs then b64Groups (cs.filter (· != ' ')) else none

/-! ## Date and time -/

/-- Days from 1970-01-01 to the given date of the proleptic Gregorian
calendar (with year 0). -/
def daysFromCivil (y : Int) (mo d : Nat) : Int :=
  let y' := if mo ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp : Int := ((mo : Int) + 9) % 12
  let doy := (153 * mp + 2) / 5 + (d : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The timezone offset in minutes of `Z` or `[+-]hh:mm`. -/
def tzMinutes : List Char → Option Int
  | ['Z'] => some 0
  | s :: h1 :: h2 :: ':' :: m1 :: m2 :: [] =>
    match twoDigits [h1, h2], twoDigits [m1, m2] with
    | some h, some m =>
      let v : Int := 60 * h + m
      some (if s == '-' then -v else v)
    | _, _ => none
  | _ => none

/-- The value of an `xsd:dateTime` lexical form (`needTz` for
`xsd:dateTimeStamp`): seconds from 1970-01-01T00:00:00 (UTC if a timezone
is given) and the timezone offset in minutes, if given. The lexical check
is the one of the OFN parser (`Parse.isDateTime`). -/
def parseDateTime (needTz : Bool) (cs : List Char) : Option (ℚ × Option Int) :=
  if !isDateTime needTz cs then none
  else match cs.splitOn 'T' with
  | [date, time] =>
    let (neg, date) := match date with
      | '-' :: d => (true, d)
      | d => (false, d)
    match date.splitOn '-' with
    | [y, mo, d] =>
      let year : Int := if neg then -(digitsVal y : Int) else digitsVal y
      match twoDigits mo, twoDigits d, twoDigits (time.take 2), twoDigits ((time.drop 3).take 2),
        twoDigits ((time.drop 6).take 2) with
      | some mo', some d', some h, some mi, some s =>
        let rest := time.drop 8
        let (frac, tz) := match rest with
          | '.' :: r => (r.takeWhile isDigitC, r.dropWhile isDigitC)
          | r => ([], r)
        let secs : ℚ := (s : ℚ) + (digitsVal frac : ℚ) / (10 : ℚ) ^ frac.length
        let loc : ℚ := ((daysFromCivil year mo' d' * 86400 + h * 3600 + mi * 60 : Int) : ℚ) + secs
        if tz.isEmpty then some (loc, none)
        else (tzMinutes tz).map fun off => (loc - ((off * 60 : Int) : ℚ), some off)
      | _, _, _, _, _ => none
    | _ => none
  | _ => none

/-! ## The value of a literal -/

/-- **Approximation `xmlLexical`**: every string of XML characters is a
lexical form of `rdf:XMLLiteral` and its own value. -/
def xmlLexical (s : String) : Option (ValOf ℚ) :=
  if xmlString s then some (.xml s) else none

/-- A string value of a derived string type: XML characters and the type's
lexical check. -/
def strIf (ok : Bool) (s : String) : Option (ValOf ℚ) :=
  if ok && xmlString s then some (.str s none) else none

/-- The value of the lexical form `lex` in a datatype of kind `k`. -/
def lexVal (k : Kind) (lex : String) : Option (ValOf ℚ) :=
  let cs := lex.toList
  match k with
  | .real | .literal => none
  | .rational => (parseRationalQ cs).map .num
  | .decimal => (parseDecimalQ cs).map .num
  | .integer lo hi =>
    match parseInt cs with
    | some v => if (lo.all fun l => l ≤ v) && (hi.all fun h => v ≤ h) then some (.num v) else none
    | none => none
  | .double => (parseFloatV 11 52 cs).map .dbl
  | .float => (parseFloatV 8 23 cs).map .flt
  | .string => strIf true lex
  | .normalizedString => strIf (isNormalizedX cs) lex
  | .token => strIf (isTokenX cs) lex
  | .language => strIf (isLanguageTag cs) lex
  | .name => strIf (isNameX cs) lex
  | .ncName => strIf (isNCNameX cs) lex
  | .nmToken => strIf (isNmtokenX cs) lex
  | .boolean =>
    if lex == "true" || lex == "1" then some (.bool true)
    else if lex == "false" || lex == "0" then some (.bool false) else none
  | .hexBinary => (parseHex cs).map .hex
  | .base64Binary => (parseB64 cs).map .b64
  | .anyURI => if xmlString lex then some (.uri lex) else none
  | .dateTime => (parseDateTime false cs).map fun p => .time p.1 p.2
  | .dateTimeStamp => (parseDateTime true cs).map fun p => .time p.1 p.2
  | .xmlLiteral => xmlLexical lex
  | .plainLiteral =>
    -- `text@tag`, split at the last `@`; an empty tag gives a string
    match cs.reverse.splitOn '@' with
    | [] | [_] => none
    | tagR :: _ =>
      let tag := tagR.reverse
      let text := String.ofList (cs.take (cs.length - tag.length - 1))
      if !xmlString text then none
      else if tag.isEmpty then some (.str text none)
      else if langTagOK tag then some (.str text (some (lowerTag (String.ofList tag))))
      else none

/-- The value of a literal; `none` for an ill-typed literal or a datatype
outside the map. A literal with a language tag (`"abc"@en`, datatype
`rdf:PlainLiteral`) denotes the string with the tag in lower case. -/
def litVal (l : Literal) : Option (ValOf ℚ) :=
  match l.lang with
  | some tag =>
    if l.datatype == rdfPlainLiteral && langTagOK tag.toList && xmlString l.lexical then
      some (.str l.lexical (some (lowerTag tag)))
    else none
  | none =>
    match kindOf l.datatype with
    | some k => lexVal k l.lexical
    | none => none

end ContextCalculus.OWL.Datatypes
