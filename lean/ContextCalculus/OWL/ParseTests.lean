import ContextCalculus.OWL.Parse
import ContextCalculus.OWL.Names

/-!
# Unit tests for `OWL.parse` and the name lists (v1.6.2)

Each `#guard` runs the executable parser at elaboration time.
-/

namespace ContextCalculus.OWL.ParseTests

open ContextCalculus.OWL

deriving instance BEq for ObjProp
deriving instance BEq for ClassExpr
deriving instance BEq for Axiom

def axiomsOf (text : String) : Option (List Axiom) :=
  match parse text with
  | .ok O => some O.axioms
  | .error _ => none

def reasonOf (text : String) : String :=
  match parse text with
  | .ok _ => "accepted"
  | .error reason => reason

def classNamesOf (text : String) : List IRI :=
  match parse text with
  | .ok O => O.classNames
  | .error _ => []

def roleNamesOf (text : String) : List IRI :=
  match parse text with
  | .ok O => O.objectPropertyNames
  | .error _ => []

def rejects (text reasonPrefix : String) : Bool :=
  (reasonOf text).startsWith reasonPrefix

def ex (local_ : String) : IRI := "http://example.org/onto#" ++ local_
def owl (local_ : String) : IRI := "http://www.w3.org/2002/07/owl#" ++ local_
def exPrefix : String := "Prefix(ex:=<http://example.org/onto#>)\n"

/-! ## IRI identity -/

-- A prefixed and a full spelling of one IRI give one string.
#guard axiomsOf (exPrefix ++ "Ontology(SubClassOf(ex:A <http://example.org/onto#A>))") ==
  some [.subClassOf (.cls (ex "A")) (.cls (ex "A"))]
#guard classNamesOf (exPrefix ++ "Ontology(SubClassOf(ex:A <http://example.org/onto#A>))") ==
  [ex "A"]

-- The empty prefix, and a prefix declared with spaces around `:=`.
#guard axiomsOf "Prefix(:=<http://example.org/onto#>) Prefix(e : = <http://example.org/onto#>)
  Ontology(SubClassOf(:A e:B))" ==
  some [.subClassOf (.cls (ex "A")) (.cls (ex "B"))]

-- The local part keeps later colons.
#guard axiomsOf (exPrefix ++ "Ontology(Declaration(Class(ex:a:b)))") ==
  some [.declareClass (ex "a:b")]

-- The ontology IRI and version IRI may be abbreviated or full.
#guard axiomsOf (exPrefix ++ "Ontology(ex:o <http://v> Declaration(Class(ex:A)))") ==
  some [.declareClass (ex "A")]

-- Standard prefixes are predeclared; redeclaring them identically is allowed.
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(<http://e#r> owl:Thing)))" ==
  some [.subClassOf (.cls "http://e#A") (.some (.named "http://e#r") .thing)]
#guard axiomsOf "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
  Ontology(SubClassOf(owl:Nothing <http://e#A>))" ==
  some [.subClassOf .nothing (.cls "http://e#A")]

/-! ## owl:Thing and owl:Nothing under every spelling -/

def thingSpellings : String :=
  "Prefix(o:=<http://www.w3.org/2002/07/owl#>) Prefix(:=<http://www.w3.org/2002/07/owl#>)
   Ontology(
     SubClassOf(owl:Thing <http://www.w3.org/2002/07/owl#Thing>)
     SubClassOf(o:Thing :Thing)
     SubClassOf(owl:Nothing <http://www.w3.org/2002/07/owl#Nothing>)
     SubClassOf(o:Nothing :Nothing))"

#guard axiomsOf thingSpellings ==
  some [.subClassOf .thing .thing, .subClassOf .thing .thing,
        .subClassOf .nothing .nothing, .subClassOf .nothing .nothing]
#guard classNamesOf thingSpellings == []

-- A non-OWL IRI ending in `#Thing` is an ordinary class.
#guard axiomsOf "Ontology(SubClassOf(<http://e#Thing> <http://e#Nothing>))" ==
  some [.subClassOf (.cls "http://e#Thing") (.cls "http://e#Nothing")]

-- Declarations of owl:Thing / owl:Nothing are skipped.
#guard axiomsOf "Ontology(Declaration(Class(owl:Thing)) Declaration(Class(owl:Nothing)))" ==
  some []

/-! ## Inverses and chains -/

#guard axiomsOf (exPrefix ++
  "Ontology(SubClassOf(ex:A ObjectSomeValuesFrom(ObjectInverseOf(ObjectInverseOf(ex:r)) ex:B)))") ==
  some [.subClassOf (.cls (ex "A")) (.some (.named (ex "r")) (.cls (ex "B")))]
#guard axiomsOf (exPrefix ++
  "Ontology(SubClassOf(ex:A ObjectAllValuesFrom(ObjectInverseOf(ex:r) ex:B)))") ==
  some [.subClassOf (.cls (ex "A")) (.all (.inv (ex "r")) (.cls (ex "B")))]
#guard axiomsOf (exPrefix ++
  "Ontology(SubClassOf(ex:A ObjectAllValuesFrom(ObjectInverseOf(ObjectInverseOf(ObjectInverseOf(ex:r))) ex:B)))") ==
  some [.subClassOf (.cls (ex "A")) (.all (.inv (ex "r")) (.cls (ex "B")))]

#guard axiomsOf (exPrefix ++ "Ontology(
    SubObjectPropertyOf(ex:r ex:s)
    SubObjectPropertyOf(ObjectPropertyChain(ex:r ObjectInverseOf(ex:s)) ex:t)
    SubObjectPropertyOf(ObjectPropertyChain(ex:r ex:s ex:t) ObjectInverseOf(ex:u)))") ==
  some [.subObjectPropertyOf [.named (ex "r")] (.named (ex "s")),
        .subObjectPropertyOf [.named (ex "r"), .inv (ex "s")] (.named (ex "t")),
        .subObjectPropertyOf [.named (ex "r"), .named (ex "s"), .named (ex "t")] (.inv (ex "u"))]
#guard rejects (exPrefix ++ "Ontology(SubObjectPropertyOf(ObjectPropertyChain(ex:r) ex:t))")
  "syntax error: ObjectPropertyChain needs two properties"

#guard axiomsOf (exPrefix ++ "Ontology(
    EquivalentObjectProperties(ex:r ObjectInverseOf(ex:s))
    InverseObjectProperties(ex:r ex:s)
    TransitiveObjectProperty(ex:r)
    SymmetricObjectProperty(ObjectInverseOf(ex:s))
    ObjectPropertyDomain(ex:r ex:A)
    ObjectPropertyRange(ObjectInverseOf(ex:r) ObjectUnionOf(ex:A ObjectComplementOf(ex:B))))") ==
  some [.equivalentObjectProperties [.named (ex "r"), .inv (ex "s")],
        .inverseObjectProperties (.named (ex "r")) (.named (ex "s")),
        .transitive (.named (ex "r")),
        .symmetric (.inv (ex "s")),
        .domain (.named (ex "r")) (.cls (ex "A")),
        .range (.inv (ex "r")) (.or [.cls (ex "A"), .not (.cls (ex "B"))])]

/-! ## Class axioms and names -/

def classAxioms : String := exPrefix ++ "Ontology(
    Declaration(Class(ex:D))
    Declaration(ObjectProperty(ex:q))
    EquivalentClasses(ex:A ObjectIntersectionOf(ex:B ObjectSomeValuesFrom(ex:r ex:C)) ex:A)
    DisjointClasses(ex:B ex:C ex:D)
    SubClassOf(ex:C ObjectAllValuesFrom(ObjectInverseOf(ex:s) ex:A)))"

#guard axiomsOf classAxioms ==
  some [.declareClass (ex "D"), .declareObjectProperty (ex "q"),
        .equivalentClasses [.cls (ex "A"),
          .and [.cls (ex "B"), .some (.named (ex "r")) (.cls (ex "C"))], .cls (ex "A")],
        .disjointClasses [.cls (ex "B"), .cls (ex "C"), .cls (ex "D")],
        .subClassOf (.cls (ex "C")) (.all (.inv (ex "s")) (.cls (ex "A")))]
#guard classNamesOf classAxioms == [ex "D", ex "A", ex "B", ex "C"]
#guard roleNamesOf classAxioms == [ex "q", ex "r", ex "s"]

/-! ## Annotations, literals and comments -/

def annotated : String := r#"Prefix(ex:=<http://example.org/onto#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
# a comment with ( parentheses ) and "quotes
Ontology(<http://example.org/onto>
  Annotation(rdfs:comment "ontology ) comment \" with an escaped quote")
  Annotation(Annotation(rdfs:label "nested") rdfs:seeAlso <http://example.org/x#(y)>)
  Declaration(AnnotationProperty(ex:note))
  Declaration(DataProperty(ex:age))
  Declaration(NamedIndividual(ex:i))
  Declaration(Datatype(ex:dt))
  AnnotationAssertion(rdfs:label ex:A "Zürich ☃ \\ ) ( \" end"@de)
  AnnotationAssertion(ex:note ex:A "42"^^<http://www.w3.org/2001/XMLSchema#integer>)
  AnnotationAssertion(rdfs:seeAlso ex:A _:anon)
  SubAnnotationPropertyOf(ex:note rdfs:comment)
  AnnotationPropertyDomain(ex:note ex:A)
  AnnotationPropertyRange(ex:note ex:A)
  SubClassOf(Annotation(rdfs:comment "a ) b") Annotation(ex:note "\"")
    ex:A # trailing comment )
    ex:B)
  Declaration(Annotation(rdfs:comment "x") Class(ex:C))
)
"#

#guard axiomsOf annotated ==
  some [.subClassOf (.cls (ex "A")) (.cls (ex "B")), .declareClass (ex "C")]

-- Literal escapes: `\\` before the closing quote ends the literal.
#guard axiomsOf r#"Ontology(SubClassOf(Annotation(<http://e#n> "back\\") <http://e#A> <http://e#B>))"# ==
  some [.subClassOf (.cls "http://e#A") (.cls "http://e#B")]

/-! ## Rejections -/

#guard rejects "Ontology(Import(<http://e>))" "out of fragment: Import"
#guard rejects "Ontology(ClassAssertion(<http://e#A> <http://e#a>))"
  "out of fragment: ClassAssertion (ABox assertion)"
#guard rejects "Ontology(ObjectPropertyAssertion(<http://e#r> <http://e#a> <http://e#b>))"
  "out of fragment: ObjectPropertyAssertion (ABox assertion)"
#guard rejects "Ontology(SameIndividual(<http://e#a> <http://e#b>))"
  "out of fragment: SameIndividual (ABox assertion)"
#guard rejects "Ontology(SubClassOf(<http://e#A> DataSomeValuesFrom(<http://e#p> xsd:integer)))"
  "out of fragment: DataSomeValuesFrom (data construct)"
#guard rejects "Ontology(DataPropertyRange(<http://e#p> xsd:integer))"
  "out of fragment: DataPropertyRange (data property axiom)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectMinCardinality(2 <http://e#r>)))"
  "out of fragment: ObjectMinCardinality (cardinality restriction)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectExactCardinality(1 <http://e#r> <http://e#B>)))"
  "out of fragment: ObjectExactCardinality (cardinality restriction)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectOneOf(<http://e#a>)))"
  "out of fragment: ObjectOneOf (nominal)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectHasValue(<http://e#r> <http://e#a>)))"
  "out of fragment: ObjectHasValue (nominal)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectHasSelf(<http://e#r>)))"
  "out of fragment: ObjectHasSelf (self restriction)"
#guard rejects "Ontology(DLSafeRule(Body() Head()))" "out of fragment: DLSafeRule (rule)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(owl:topObjectProperty <http://e#B>)))"
  "out of fragment: owl:topObjectProperty"
#guard rejects "Ontology(SubObjectPropertyOf(<http://e#r> <http://www.w3.org/2002/07/owl#bottomObjectProperty>))"
  "out of fragment: owl:bottomObjectProperty"
#guard rejects "Ontology(HasKey(<http://e#A> (<http://e#r>) ()))" "out of fragment: HasKey (key)"
#guard rejects "Ontology(DisjointUnion(<http://e#A> <http://e#B> <http://e#C>))"
  "out of fragment: DisjointUnion (disjoint union)"
#guard rejects "Ontology(FunctionalObjectProperty(<http://e#r>))"
  "out of fragment: FunctionalObjectProperty (object property characteristic)"
#guard rejects "Ontology(InverseFunctionalObjectProperty(<http://e#r>))"
  "out of fragment: InverseFunctionalObjectProperty (object property characteristic)"
#guard rejects "Ontology(ReflexiveObjectProperty(<http://e#r>))"
  "out of fragment: ReflexiveObjectProperty (object property characteristic)"
#guard rejects "Ontology(IrreflexiveObjectProperty(<http://e#r>))"
  "out of fragment: IrreflexiveObjectProperty (object property characteristic)"
#guard rejects "Ontology(AsymmetricObjectProperty(<http://e#r>))"
  "out of fragment: AsymmetricObjectProperty (object property characteristic)"
#guard rejects "Ontology(DisjointObjectProperties(<http://e#r> <http://e#s>))"
  "out of fragment: DisjointObjectProperties (object property characteristic)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(ObjectPropertyChain(<http://e#r> <http://e#s>) <http://e#B>)))"
  "out of fragment: object property expression ObjectPropertyChain"

-- Syntax errors.
#guard rejects "Ontology(SubClassOf(Annotation(<http://e#n> \"open) <http://e#A> <http://e#B>))"
  "syntax error: unterminated string literal"
-- An IRI runs to the next `>`, spaces included: one operand here.
#guard rejects "Ontology(SubClassOf(<http://e#A <http://e#B>))" "syntax error: wrong number"
#guard rejects "Ontology(SubClassOf(<http://e#A> <http://e#B)))" "syntax error: unterminated full IRI"
#guard rejects "Ontology(SubClassOf(ex:A ex:B))" "syntax error: undeclared prefix ex:"
#guard rejects "Ontology(SubClassOf(A B))" "syntax error: A is not an IRI"
#guard rejects "Ontology(SubClassOf(<http://e#A> <http://e#B>)" "syntax error: unexpected end of input"
#guard rejects "Ontology(SubClassOf(<http://e#A> <http://e#B>))) " "syntax error: content after"
#guard rejects "Prefix(ex:=<http://e#>)" "syntax error: no Ontology"
#guard rejects "Prefix(ex:=<http://e#>) Prefix(ex:=<http://e#>) Ontology()"
  "syntax error: prefix ex: is declared more than once"
#guard rejects "Prefix(owl:=<http://e#>) Ontology()" "syntax error: standard prefix owl:"
#guard rejects "Ontology(SubClassOf(<http://e#A> Annotation(<http://e#n> \"x\") <http://e#B>))"
  "syntax error: Annotation after an operand"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectIntersectionOf(<http://e#B>)))"
  "syntax error: ObjectIntersectionOf needs two operands"
#guard rejects "Ontology(EquivalentClasses(<http://e#A>))" "syntax error: wrong number"
#guard rejects "Ontology(SubClassOf(<http://e#A> <http://e#B> <http://e#C>))" "syntax error: wrong number"
#guard rejects "Ontology(<http://o> <http://v> <http://w>)" "syntax error: unexpected <http://w>"
#guard rejects "Ontology(Declaration(Class(<http://e#A>)) Annotation(<http://e#n> \"x\"))"
  "syntax error: ontology Annotation after an axiom"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(<http://e#r> \"x\")))"
  "syntax error: expected an IRI, found a literal"
#guard rejects "Ontology(ClassAssertion(<http://e#A> _:x))" "out of fragment: ClassAssertion"
#guard rejects "" "syntax error: no Ontology"
#guard reasonOf "Ontology()" == "accepted"

end ContextCalculus.OWL.ParseTests
