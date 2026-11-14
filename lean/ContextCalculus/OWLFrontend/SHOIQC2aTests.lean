import ContextCalculus.OWLFrontend.SHOIQC2aReference
import ContextCalculus.OWL.Parse

/-!
# Tests for the SHOIQ C2a route

The answers of `owlSHOIQC2aConsistent`, `owlSHOIQC2aTypeRow`,
`owlSHOIQC2aSameRow` and `owlSHOIQC2aSubRow` on small knowledge bases with
nominals, checked by `#guard` (the interpreter). The consistent cases with
counting run with a hint; the exhaustive search is too slow for them in the
interpreter. The inputs are those of `testdata/shoiq-c2a/`.
-/

namespace ContextCalculus.OWLFrontend.SHOIQC2aTests

open ContextCalculus.OWL

def ont (body : String) : Ontology :=
  match OWL.parse ("Prefix(:=<http://ex/>)\nOntology(<http://ex/t>\n" ++ body ++ "\n)") with
  | .ok O => O
  | .error _ => ⟨[]⟩

def hint (s : String) : Option RawHint :=
  match RawHint.parseHint s with
  | .ok h => some h
  | .error _ => none

def oneofClash := ont "SubClassOf(ObjectOneOf(:a) :B)\nClassAssertion(ObjectComplementOf(:B) :a)"
def sameDiff := ont "SubClassOf(ObjectOneOf(:a) ObjectOneOf(:b))\nDifferentIndividuals(:a :b)"
def nomSat := ont "ClassAssertion(:A :a)\nSubClassOf(:A ObjectHasValue(:r :b))"
def notC2a := ont ("SubClassOf(:A ObjectSomeValuesFrom(:r ObjectOneOf(:o)))\n" ++
  "SubClassOf(ObjectOneOf(:o) ObjectMaxCardinality(1 ObjectInverseOf(:r)))\nClassAssertion(:A :a)")
def countSat := ont ("ClassAssertion(ObjectSomeValuesFrom(:r ObjectOneOf(:o)) :a)\n" ++
  "ClassAssertion(ObjectSomeValuesFrom(:r ObjectOneOf(:o)) :b)\n" ++
  "SubClassOf(ObjectOneOf(:o) ObjectMaxCardinality(1 ObjectInverseOf(:r)))")
def typeO := ont "SubClassOf(ObjectOneOf(:a :b) :C)\nClassAssertion(:D :a)"

#guard owlSHOIQC2aConsistent oneofClash none = some false
#guard owlSHOIQC2aConsistent sameDiff none = some false
#guard owlSHOIQC2aConsistent nomSat (hint "blocks 2\nty 0 0 2 3 5\nty 1 1 3\nlab 0 1 +0") = some true
#guard owlSHOIQC2aConsistent notC2a none = none
#guard owlSHOIQC2aConsistent countSat
  (hint "blocks 2\nty 0 0 3 7\nty 1 1 2 3 5 6\nlab 1 0 +0") = some true
-- the definition names between nominal classes and their restrictions are nominal-only
#guard (translateSHOIQ countSat []).map (fun T => c2aOK T (SHOIQ.nomNames countSat [])) = some true
#guard owlSHOIQC2aTypeRow typeO "http://ex/C" "http://ex/a" none = some true
#guard owlSHOIQC2aTypeRow typeO "http://ex/C" "http://ex/b" none = some true
#guard owlSHOIQC2aSameRow sameDiff "http://ex/a" "http://ex/b" none = some true

end ContextCalculus.OWLFrontend.SHOIQC2aTests
