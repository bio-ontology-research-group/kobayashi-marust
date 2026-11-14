import ContextCalculus.OWLFrontend.SRIQDComplete

/-!
# Tests of the SHIQ(D) translation (v1.7.0 stage C4, part D)

`#guard` checks of `translateSRIQD` (shape, declines) and of the oracle
check on its atoms. The route's answers are checked with the compiled
`km-sriqd-probe` on `testdata/sriqd/*.ofn` (expected answers in
`testdata/sriqd/expected.tsv`): the star elimination enumerates every
record, which the interpreter of `#guard` runs in seconds only for a
handful of concept indices.
-/

namespace ContextCalculus.OWLFrontend.SRIQDTests

open ContextCalculus.OWL

def xs (s : String) : IRI := Parse.xsdNs ++ s
def L (s d : String) : Literal := { lexical := s, datatype := xs d, lang := none }
def p : DataProp := .named "p"
def A : ClassExpr := .cls "A"
def B : ClassExpr := .cls "B"

/-- `(data expressions, concepts, clauses, oracle check)` of a translation. -/
def shape (O : Ontology) (req : List IRI) : Option (Nat × Nat × Nat × Bool) :=
  (translateSRIQD O req).map fun T =>
    (T.tab.length, T.obj.conceptCount, T.ontology.length, Datatypes.owlCheck (SHIQD.spec T.tab))

/- One data expression: names `A`, `F`, `W`, top, bottom; clauses: the two
of the SHIQ translation (top, bottom), `A ⊑ F`, and the three of the
entry. -/
#guard shape ⟨[.subClassOf A (.dataMin 3 p (.datatype (xs "boolean")))]⟩ ["A"] = some (1, 5, 6, true)

/- Equal data expressions share their names. -/
#guard shape ⟨[.subClassOf A (.dataSome p (.datatype (xs "int"))),
  .subClassOf B (.dataSome p (.datatype (xs "int")))]⟩ ["A", "B"] = some (1, 6, 7, true)

/- `DataExactCardinality` gives two data expressions, `FunctionalDataProperty`
one. -/
#guard (shape ⟨[.subClassOf A (.dataExact 2 p (.datatype (xs "int"))),
  .functionalData p]⟩ ["A"]).map (·.1) = some 3

/- `DataHasValue` is `∃p.{l}`. -/
#guard (shape ⟨[.subClassOf A (.dataHasValue p (L "1" "integer"))]⟩ ["A"]).map (·.1) = some 1

/- Sub-properties give `dSub` clauses (and no data expression). -/
#guard (shape ⟨[.subDataPropertyOf p (.named "q")]⟩ []).map (·.2.2.1) = some 3

/- Declined: disjoint data properties, datatype definitions, the top data
property. -/
#guard (translateSRIQD ⟨[.disjointDataProperties [p, .named "q"]]⟩ []).isNone
#guard (translateSRIQD ⟨[.datatypeDefinition "dt" (.datatype (xs "int"))]⟩ []).isNone
#guard (translateSRIQD ⟨[.subClassOf A (.dataSome .top (.datatype (xs "int")))]⟩ ["A"]).isNone

/- `owlCheck` (the full oracle) declines string facets and a free datatype with
a literal; the route splits the free datatype into parts instead
(`allSupported` accepts it). -/
#guard shape ⟨[.subClassOf A (.dataSome p
  (.restriction (xs "string") [(xs "maxLength", L "3" "integer")]))]⟩ ["A"] = some (1, 5, 6, false)
#guard shape ⟨[.subClassOf A (.dataSome p
  (.and [.datatype "http://ex/dt", .oneOf [L "a" "string"]]))]⟩ ["A"] = some (1, 5, 6, false)

/- A free datatype alone passes. -/
#guard shape ⟨[.subClassOf A (.dataSome p (.datatype "http://ex/dt"))]⟩ ["A"] = some (1, 5, 6, true)

end ContextCalculus.OWLFrontend.SRIQDTests
