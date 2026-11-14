import ContextCalculus.OWL.Datatypes.Oracle

/-!
# Tests of the oracle of the OWL 2 datatype map (v1.7.0 stage C4)

`#guard` checks of `owlCard` and `owlCheck` on small atom lists.
-/

namespace ContextCalculus.OWL.Datatypes.OracleTests

open ContextCalculus.OWL

def xs (s : String) : IRI := Parse.xsdNs ++ s
def L (s d : String) : Literal := { lexical := s, datatype := xs d, lang := none }

/-- `xsd:int[≥ 5]` and `xsd:int[≤ 3]`. -/
def int5 : DataRange := .restriction (xs "int") [(xs "minInclusive", L "5" "integer")]
def int3 : DataRange := .restriction (xs "int") [(xs "maxInclusive", L "3" "integer")]
def spec1 : Fin 2 → DataRange := ![int5, int3]

#guard owlCheck spec1
#guard owlCard spec1 {0} = some 2147483643
#guard owlCard spec1 {1} = some 2147483652
#guard owlCard spec1 {0, 1} = some 0
#guard owlCard spec1 ∅ = none

/-- `xsd:int[≥ 1, ≤ 2]` has two values. -/
def int12 : Fin 1 → DataRange :=
  ![.restriction (xs "int") [(xs "minInclusive", L "1" "integer"), (xs "maxInclusive", L "2" "int")]]
#guard owlCard int12 {0} = some 2

/-- `xsd:decimal[> 0, < 1]` is infinite, `xsd:integer[> 0, < 1]` empty. -/
def dec01 : Fin 2 → DataRange :=
  ![.restriction (xs "decimal") [(xs "minExclusive", L "0" "integer"), (xs "maxExclusive", L "1" "integer")],
    .restriction (xs "integer") [(xs "minExclusive", L "0" "integer"), (xs "maxExclusive", L "1" "integer")]]
#guard owlCard dec01 {0} = none
#guard owlCard dec01 {1} = some 0
#guard owlCard dec01 {0, 1} = some 0

/-- Booleans have two values. -/
def bool1 : Fin 1 → DataRange := ![.datatype (xs "boolean")]
#guard owlCard bool1 {0} = some 2

/-- `"1"^^xsd:integer` and `"1.0"^^xsd:decimal` are one value. -/
def oneOne : Fin 2 → DataRange := ![.oneOf [L "1" "integer"], .oneOf [L "1.0" "decimal"]]
#guard owlCard oneOne {0, 1} = some 1
#guard owlCard oneOne {0} = some 0

/-- `"1"^^xsd:float` and `"1"^^xsd:integer` are different values. -/
def floatInt : Fin 2 → DataRange := ![.oneOf [L "1" "float"], .oneOf [L "1" "integer"]]
#guard owlCard floatInt {0, 1} = some 0
#guard owlCard floatInt {0} = some 1

/-- `xsd:float` has `2^32 - 2^24 + 3` values; one is a literal here. -/
def float1 : Fin 2 → DataRange := ![.datatype (xs "float"), .oneOf [L "1" "float"]]
#guard owlCard float1 {0} = some 4278190082

/-- Integers are decimals. -/
def intNotDec : Fin 2 → DataRange := ![.datatype (xs "integer"), .not (.datatype (xs "decimal"))]
#guard owlCard intNotDec {0, 1} = some 0

/-- A free datatype with strings only: accepted; with a literal: declined. -/
def free1 : Fin 2 → DataRange := ![.datatype "http://example.org/dt", .datatype (xs "string")]
#guard owlCheck free1
def free2 : Fin 2 → DataRange := ![.datatype "http://example.org/dt", .oneOf [L "a" "string"]]
#guard !owlCheck free2

/-- Declined: `xsd:token` and string facets. -/
def tok : Fin 1 → DataRange := ![.datatype (xs "token")]
#guard !owlCheck tok
def strLen : Fin 1 → DataRange := ![.restriction (xs "string") [(xs "maxLength", L "3" "integer")]]
#guard !owlCheck strLen

/-- Section 4.7: the same instant with offsets `+01:00` and `Z` gives two
values; `Z` and `+00:00` give one. -/
def dt2 : Fin 1 → DataRange :=
  ![.oneOf [L "2008-07-08T20:44:11.656+01:00" "dateTime", L "2008-07-08T19:44:11.656Z" "dateTime"]]
#guard owlCard dt2 {0} = some 2
def dt1 : Fin 1 → DataRange :=
  ![.oneOf [L "2008-07-08T19:44:11Z" "dateTime", L "2008-07-08T19:44:11+00:00" "dateTime"]]
#guard owlCard dt1 {0} = some 1

end ContextCalculus.OWL.Datatypes.OracleTests
