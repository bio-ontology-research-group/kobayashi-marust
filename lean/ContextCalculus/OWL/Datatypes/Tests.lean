import ContextCalculus.OWL.Datatypes.Map

/-!
# Tests of the OWL 2 datatype map (v1.7.0 stage C4)

Literal values of `owl2MapP`, checked by the kernel (`decide +kernel`,
no extra axioms).
-/

namespace ContextCalculus.OWL.Datatypes.Tests

open ContextCalculus.OWL

/-- A literal with an `xsd:` datatype. -/
def X (lex dt : String) : Literal := { lexical := lex, datatype := Parse.xsdNs ++ dt, lang := none }

/-- A literal with a full datatype IRI. -/
def Lit (lex dt : String) : Literal := { lexical := lex, datatype := dt, lang := none }

variable (pat : String → String → Prop)

/-- `"1"^^xsd:integer` and `"1.0"^^xsd:decimal` denote the same value. -/
theorem integer_eq_decimal : (owl2MapP pat).literal (X "1" "integer") = (owl2MapP pat).literal (X "1.0" "decimal") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `"+01"^^xsd:int` and `"1"^^xsd:nonNegativeInteger` denote the same value. -/
theorem int_eq_nonNegativeInteger :
    (owl2MapP pat).literal (X "+01" "int") = (owl2MapP pat).literal (X "1" "nonNegativeInteger") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `"1"^^xsd:float` and `"1"^^xsd:integer` denote different values. -/
theorem float_ne_integer : (owl2MapP pat).literal (X "1" "float") ≠ (owl2MapP pat).literal (X "1" "integer") :=
  fun h => absurd ((owl2MapP_literal_eq pat _ _).1 h) (by decide +kernel)

/-- `"1"^^xsd:float` and `"1"^^xsd:double` denote different values. -/
theorem float_ne_double : (owl2MapP pat).literal (X "1" "float") ≠ (owl2MapP pat).literal (X "1" "double") :=
  fun h => absurd ((owl2MapP_literal_eq pat _ _).1 h) (by decide +kernel)

/-- `"0.1"^^xsd:float` rounds to `13421773 / 2^27`. -/
theorem float_point_one :
    (litVal (X "0.1" "float")).bind (fun v => match v with | .flt x => x.toRat? | _ => none) =
      some (13421773 / 134217728) := by decide +kernel

/-- `"1.0"^^xsd:float` and `"1E0"^^xsd:float` denote the same value. -/
theorem float_lexical_forms : (owl2MapP pat).literal (X "1.0" "float") = (owl2MapP pat).literal (X "1E0" "float") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `+0` and `-0` are different float values. -/
theorem float_zeros : (owl2MapP pat).literal (X "0" "float") ≠ (owl2MapP pat).literal (X "-0" "float") :=
  fun h => absurd ((owl2MapP_literal_eq pat _ _).1 h) (by decide +kernel)

/-- `NaN` is one value. -/
theorem double_nan : (owl2MapP pat).literal (X "NaN" "double") = some (.dbl .nan) := by
  rw [owl2MapP_literal, show litVal (X "NaN" "double") = some (.dbl .nan) by decide +kernel]
  rfl

/-- `1e39` overflows `xsd:float` to `+INF`. -/
theorem float_overflow : litVal (X "1e39" "float") = some (.flt (.inf false)) := by decide +kernel

/-- Two time stamps of the same instant are one value. -/
theorem dateTime_same_instant :
    (owl2MapP pat).literal (X "2000-01-01T00:00:00Z" "dateTime") =
      (owl2MapP pat).literal (X "2000-01-01T01:00:00+01:00" "dateTimeStamp") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- A time without a timezone differs from the same clock time in UTC. -/
theorem dateTime_local_ne_utc :
    (owl2MapP pat).literal (X "2000-01-01T00:00:00" "dateTime") ≠
      (owl2MapP pat).literal (X "2000-01-01T00:00:00Z" "dateTime") :=
  fun h => absurd ((owl2MapP_literal_eq pat _ _).1 h) (by decide +kernel)

/-- `24:00:00` is the start of the next day. -/
theorem dateTime_midnight :
    (owl2MapP pat).literal (X "1999-12-31T24:00:00Z" "dateTime") =
      (owl2MapP pat).literal (X "2000-01-01T00:00:00Z" "dateTime") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `"abc"@EN` and `"abc@en"^^rdf:PlainLiteral` denote the same value. -/
theorem plainLiteral_tag :
    (owl2MapP pat).literal { lexical := "abc", datatype := Parse.rdfPlainLiteral, lang := some "EN" } =
      (owl2MapP pat).literal (Lit "abc@en" Parse.rdfPlainLiteral) :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `"abc"^^xsd:string` and `"abc@"^^rdf:PlainLiteral` denote the same value. -/
theorem string_eq_plainLiteral :
    (owl2MapP pat).literal (X "abc" "string") = (owl2MapP pat).literal (Lit "abc@" Parse.rdfPlainLiteral) :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `"abc"^^xsd:string` and `"abc"^^xsd:anyURI` are different values. -/
theorem string_ne_anyURI :
    (owl2MapP pat).literal (X "abc" "string") ≠ (owl2MapP pat).literal (X "abc" "anyURI") :=
  fun h => absurd ((owl2MapP_literal_eq pat _ _).1 h) (by decide +kernel)

/-- Ill-typed literals denote nothing. -/
theorem ill_typed :
    litVal (X "300" "byte") = none ∧ litVal (X "QR==" "base64Binary") = none ∧
      litVal (X "1.5" "integer") = none ∧ litVal (X "2001-02-29T00:00:00" "dateTime") = none ∧
      litVal (X "a b" "token") = some (.str "a b" none) ∧ litVal (X "a  b" "token") = none := by
  decide +kernel

/-- `"QQ=="` is the octet `0x41`, as is `"41"^^xsd:hexBinary`, in a
different value space. -/
theorem binary : litVal (X "QQ==" "base64Binary") = some (.b64 [65]) ∧
    litVal (X "41" "hexBinary") = some (.hex [65]) := by decide +kernel

/-- `"true"` and `"1"` are the same boolean. -/
theorem boolean_forms : (owl2MapP pat).literal (X "true" "boolean") = (owl2MapP pat).literal (X "1" "boolean") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

/-- `owl:rational` literals are reduced fractions. -/
theorem rational_value :
    (owl2MapP pat).literal (Lit "2/4" (Parse.owlNs ++ "rational")) = (owl2MapP pat).literal (X "0.5" "decimal") :=
  (owl2MapP_literal_eq pat _ _).2 (by decide +kernel)

end ContextCalculus.OWL.Datatypes.Tests

#print axioms ContextCalculus.OWL.Datatypes.Tests.integer_eq_decimal
#print axioms ContextCalculus.OWL.Datatypes.Tests.float_ne_integer
#print axioms ContextCalculus.OWL.Datatypes.Tests.float_point_one
#print axioms ContextCalculus.OWL.Datatypes.Tests.dateTime_same_instant
#print axioms ContextCalculus.OWL.Datatypes.Tests.ill_typed
