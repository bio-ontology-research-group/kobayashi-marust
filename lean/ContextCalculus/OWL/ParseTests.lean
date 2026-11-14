import ContextCalculus.OWL.Parse
import ContextCalculus.OWL.Names

/-!
# Unit tests for `OWL.parse` and the name lists (v1.6.2)

Each `#guard` runs the executable parser at elaboration time.
-/

namespace ContextCalculus.OWL.ParseTests

open ContextCalculus.OWL

deriving instance BEq for ObjProp
deriving instance BEq for DataProp
deriving instance BEq for DataRange
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
  some [.declareAnnotationProperty (ex "note"), .declareDataProperty (ex "age"),
        .declareNamedIndividual (ex "i"), .declareDatatype (ex "dt"),
        .subClassOf (.cls (ex "A")) (.cls (ex "B")), .declareClass (ex "C")]

-- Literal escapes: `\\` before the closing quote ends the literal.
#guard axiomsOf r#"Ontology(SubClassOf(Annotation(<http://e#n> "back\\") <http://e#A> <http://e#B>))"# ==
  some [.subClassOf (.cls "http://e#A") (.cls "http://e#B")]

-- A comment also ends at a carriage return (Rust ends it only at a line feed).
#guard axiomsOf "Ontology(# comment\rSubClassOf(<http://e#A> <http://e#B>))" ==
  some [.subClassOf (.cls "http://e#A") (.cls "http://e#B")]

-- Non-ASCII text in an abbreviated IRI (Rust panics on `à`: its byte 0xA0
-- counts as whitespace there).
#guard axiomsOf (exPrefix ++ "Ontology(SubClassOf(ex:à ex:Zürich))") ==
  some [.subClassOf (.cls (ex "à")) (.cls (ex "Zürich"))]

-- A full IRI that looks like an abbreviated one stays as written.
#guard classNamesOf (exPrefix ++ "Ontology(SubClassOf(<ex:A> ex:A))") == ["ex:A", ex "A"]

/-! ## The OWL 2 DL constructs of stage C0 (v1.7.0) -/

def e (local_ : String) : IRI := "http://e#" ++ local_
def xsd (local_ : String) : IRI := "http://www.w3.org/2001/XMLSchema#" ++ local_
def lit (lex dt : String) : Literal := { lexical := lex, datatype := xsd dt, lang := none }

-- Individuals, nominals, HasValue, Self.
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectOneOf(<http://e#a> _:b)))" ==
  some [.subClassOf (.cls (e "A")) (.oneOf [.named (e "a"), .anon "b"])]
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectHasValue(<http://e#r> <http://e#a>)))" ==
  some [.subClassOf (.cls (e "A")) (.hasValue (.named (e "r")) (.named (e "a")))]
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectHasSelf(ObjectInverseOf(<http://e#r>))))" ==
  some [.subClassOf (.cls (e "A")) (.hasSelf (.inv (e "r")))]

-- Cardinalities, qualified and unqualified.
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectMinCardinality(2 <http://e#r>))
  SubClassOf(<http://e#A> ObjectMaxCardinality(0 <http://e#r> <http://e#B>))
  SubClassOf(<http://e#A> ObjectExactCardinality(1 <http://e#r> <http://e#B>)))" ==
  some [.subClassOf (.cls (e "A")) (.min 2 (.named (e "r")) .thing),
        .subClassOf (.cls (e "A")) (.max 0 (.named (e "r")) (.cls (e "B"))),
        .subClassOf (.cls (e "A")) (.exact 1 (.named (e "r")) (.cls (e "B")))]
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectMinCardinality(-1 <http://e#r>)))"
  "syntax error: -1 is not a nonnegative integer"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectMinCardinality(<http://e#r>)))"
  "syntax error: ObjectMinCardinality takes"

-- Top and bottom properties.
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(owl:topObjectProperty <http://e#B>))
  SubObjectPropertyOf(<http://e#r> <http://www.w3.org/2002/07/owl#bottomObjectProperty>)
  SubClassOf(<http://e#A> ObjectAllValuesFrom(ObjectInverseOf(owl:topObjectProperty) <http://e#B>))
  SubDataPropertyOf(owl:bottomDataProperty owl:topDataProperty))" ==
  some [.subClassOf (.cls (e "A")) (.some .top (.cls (e "B"))),
        .subObjectPropertyOf [.named (e "r")] .bot,
        .subClassOf (.cls (e "A")) (.all .top (.cls (e "B"))),
        .subDataPropertyOf .bot .top]

-- Object property axioms.
#guard axiomsOf "Ontology(DisjointObjectProperties(<http://e#r> <http://e#s>)
  FunctionalObjectProperty(<http://e#r>) InverseFunctionalObjectProperty(<http://e#r>)
  ReflexiveObjectProperty(<http://e#r>) IrreflexiveObjectProperty(<http://e#r>)
  AsymmetricObjectProperty(ObjectInverseOf(<http://e#r>)))" ==
  some [.disjointObjectProperties [.named (e "r"), .named (e "s")],
        .functional (.named (e "r")), .inverseFunctional (.named (e "r")),
        .reflexive (.named (e "r")), .irreflexive (.named (e "r")),
        .asymmetric (.inv (e "r"))]
#guard rejects "Ontology(DisjointObjectProperties(<http://e#r>))" "syntax error: wrong number"
#guard rejects "Ontology(FunctionalObjectProperty(<http://e#r> <http://e#s>))"
  "syntax error: wrong number"

-- Class axioms: DisjointUnion.
#guard axiomsOf "Ontology(DisjointUnion(<http://e#A> <http://e#B> <http://e#C>))" ==
  some [.disjointUnion (e "A") [.cls (e "B"), .cls (e "C")]]
#guard rejects "Ontology(DisjointUnion(<http://e#A> <http://e#B>))" "syntax error: wrong number"

-- Data property axioms and data ranges.
#guard axiomsOf "Ontology(SubDataPropertyOf(<http://e#p> <http://e#q>)
  EquivalentDataProperties(<http://e#p> <http://e#q>)
  DisjointDataProperties(<http://e#p> <http://e#q>)
  DataPropertyDomain(<http://e#p> <http://e#A>)
  DataPropertyRange(<http://e#p> DataUnionOf(xsd:integer DataComplementOf(xsd:string)))
  FunctionalDataProperty(<http://e#p>))" ==
  some [.subDataPropertyOf (.named (e "p")) (.named (e "q")),
        .equivalentDataProperties [.named (e "p"), .named (e "q")],
        .disjointDataProperties [.named (e "p"), .named (e "q")],
        .dataDomain (.named (e "p")) (.cls (e "A")),
        .dataRange (.named (e "p")) (.or [.datatype (xsd "integer"), .not (.datatype (xsd "string"))]),
        .functionalData (.named (e "p"))]
#guard axiomsOf "Ontology(DatatypeDefinition(<http://e#adult>
  DatatypeRestriction(xsd:integer xsd:minInclusive \"18\"^^xsd:integer))
  DataPropertyRange(<http://e#p> DataIntersectionOf(<http://e#adult> DataOneOf(\"1\"^^xsd:integer \"x\"))))" ==
  some [.datatypeDefinition (e "adult")
          (.restriction (xsd "integer") [(xsd "minInclusive", lit "18" "integer")]),
        .dataRange (.named (e "p")) (.and [.datatype (e "adult"),
          .oneOf [lit "1" "integer", lit "x" "string"]])]

-- Data class expressions.
#guard axiomsOf "Ontology(SubClassOf(<http://e#A> DataSomeValuesFrom(<http://e#p> xsd:integer))
  SubClassOf(<http://e#A> DataAllValuesFrom(<http://e#p> rdfs:Literal))
  SubClassOf(<http://e#A> DataHasValue(<http://e#p> \"true\"^^xsd:boolean))
  SubClassOf(<http://e#A> DataMinCardinality(1 <http://e#p>))
  SubClassOf(<http://e#A> DataMaxCardinality(2 <http://e#p> xsd:string))
  SubClassOf(<http://e#A> DataExactCardinality(3 owl:topDataProperty xsd:integer)))" ==
  some [.subClassOf (.cls (e "A")) (.dataSome (.named (e "p")) (.datatype (xsd "integer"))),
        .subClassOf (.cls (e "A")) (.dataAll (.named (e "p")) (.datatype rdfsLiteral)),
        .subClassOf (.cls (e "A")) (.dataHasValue (.named (e "p")) (lit "true" "boolean")),
        .subClassOf (.cls (e "A")) (.dataMin 1 (.named (e "p")) (.datatype rdfsLiteral)),
        .subClassOf (.cls (e "A")) (.dataMax 2 (.named (e "p")) (.datatype (xsd "string"))),
        .subClassOf (.cls (e "A")) (.dataExact 3 .top (.datatype (xsd "integer")))]
-- n-ary data ranges stay rejected.
#guard rejects "Ontology(SubClassOf(<http://e#A> DataSomeValuesFrom(<http://e#p> <http://e#q> xsd:integer)))"
  "out of fragment: DataSomeValuesFrom with 2 data properties (n-ary data range)"
#guard rejects "Ontology(SubClassOf(<http://e#A> DataAllValuesFrom(<http://e#p> <http://e#q> xsd:integer)))"
  "out of fragment: DataAllValuesFrom with 2 data properties (n-ary data range)"

-- Keys.
#guard axiomsOf "Ontology(HasKey(<http://e#A> (<http://e#r> ObjectInverseOf(<http://e#s>)) (<http://e#p>))
  HasKey(<http://e#A> () (<http://e#p>)))" ==
  some [.hasKey (.cls (e "A")) [.named (e "r"), .inv (e "s")] [.named (e "p")],
        .hasKey (.cls (e "A")) [] [.named (e "p")]]
#guard rejects "Ontology(HasKey(<http://e#A> (<http://e#r>)))" "syntax error: HasKey takes"

-- Assertions.
#guard axiomsOf "Ontology(SameIndividual(<http://e#a> _:b) DifferentIndividuals(<http://e#a> <http://e#c>)
  ClassAssertion(<http://e#A> <http://e#a>)
  ObjectPropertyAssertion(ObjectInverseOf(<http://e#r>) <http://e#a> _:b)
  NegativeObjectPropertyAssertion(<http://e#r> <http://e#a> <http://e#c>)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"5\"^^xsd:integer)
  NegativeDataPropertyAssertion(<http://e#p> _:b \"hi\"@en))" ==
  some [.sameIndividual [.named (e "a"), .anon "b"],
        .differentIndividuals [.named (e "a"), .named (e "c")],
        .classAssertion (.cls (e "A")) (.named (e "a")),
        .objectPropertyAssertion (.inv (e "r")) (.named (e "a")) (.anon "b"),
        .negativeObjectPropertyAssertion (.named (e "r")) (.named (e "a")) (.named (e "c")),
        .dataPropertyAssertion (.named (e "p")) (.named (e "a")) (lit "5" "integer"),
        .negativeDataPropertyAssertion (.named (e "p")) (.anon "b")
          { lexical := "hi", datatype := "http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral",
            lang := some "en" }]
#guard rejects "Ontology(SameIndividual(<http://e#a>))" "syntax error: wrong number"
-- A node ID is an individual only.
#guard rejects "Ontology(SubClassOf(_:x <http://e#B>))" "syntax error: anonymous individual _:x"

-- Declarations of every entity kind; the top and bottom entities are skipped.
#guard axiomsOf "Ontology(Declaration(DataProperty(<http://e#p>)) Declaration(NamedIndividual(<http://e#a>))
  Declaration(Datatype(<http://e#d>)) Declaration(AnnotationProperty(<http://e#n>))
  Declaration(DataProperty(owl:topDataProperty)) Declaration(ObjectProperty(owl:bottomObjectProperty)))" ==
  some [.declareDataProperty (e "p"), .declareNamedIndividual (e "a"),
        .declareDatatype (e "d"), .declareAnnotationProperty (e "n")]
#guard rejects "Ontology(Declaration(Thing(<http://e#a>)))" "syntax error: unknown entity kind Thing"

-- Literals: escapes, suffix spellings, whitespace before `^^`.
#guard axiomsOf r#"Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> "a\"b\\c"))"# ==
  some [.dataPropertyAssertion (.named (e "p")) (.named (e "a")) (lit "a\"b\\c" "string")]
#guard axiomsOf "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"7\" ^^<http://www.w3.org/2001/XMLSchema#byte>))" ==
  some [.dataPropertyAssertion (.named (e "p")) (.named (e "a")) (lit "7" "byte")]
-- A datatype outside the OWL 2 datatype map is accepted (no lexical check).
#guard axiomsOf "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"q\"^^<http://e#dt>))" ==
  some [.dataPropertyAssertion (.named (e "p")) (.named (e "a"))
    { lexical := "q", datatype := e "dt", lang := none }]

-- Ill-typed literals are rejected.
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"x\"^^xsd:integer))"
  "ill-typed literal"
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"300\"^^xsd:byte))"
  "ill-typed literal"
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"1\"^^owl:real))"
  "ill-typed literal"
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"2026-02-30T00:00:00\"^^xsd:dateTime))"
  "ill-typed literal"
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"2026-02-03T10:00:00\"^^xsd:dateTimeStamp))"
  "ill-typed literal"
#guard rejects "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"x\"@1bad))"
  "ill-typed literal"
-- Well-typed forms of several datatypes.
#guard (axiomsOf "Ontology(DataPropertyAssertion(<http://e#p> <http://e#a> \"-1.5E3\"^^xsd:double)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"2024-02-29T24:00:00Z\"^^xsd:dateTimeStamp)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"3/4\"^^owl:rational)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"0aFF\"^^xsd:hexBinary)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"+.5\"^^xsd:decimal)
  DataPropertyAssertion(<http://e#p> <http://e#a> \"abc@en-GB\"^^rdf:PlainLiteral))").isSome

-- Facets: unknown or inapplicable facets and facets outside the map are rejected.
#guard rejects "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(xsd:integer xsd:foo \"1\"^^xsd:integer)))"
  "bad facet"
#guard rejects "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(xsd:string xsd:minInclusive \"1\"^^xsd:integer)))"
  "bad facet"
#guard rejects "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(<http://e#dt> xsd:minLength \"1\"^^xsd:integer)))"
  "bad facet"
#guard rejects "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(xsd:string xsd:length \"-1\"^^xsd:integer)))"
  "bad facet"
#guard rejects "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(xsd:integer)))"
  "syntax error: DatatypeRestriction needs facet and literal pairs"
#guard (axiomsOf "Ontology(DataPropertyRange(<http://e#p> DatatypeRestriction(xsd:string xsd:pattern \"a*\" xsd:maxLength \"3\"^^xsd:nonNegativeInteger)))").isSome

/-! ## Rejections -/

#guard rejects "Ontology(Import(<http://e>))" "out of fragment: Import"
#guard rejects "Ontology(DLSafeRule(Body() Head()))" "out of fragment: DLSafeRule (rule)"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectSomeValuesFrom(ObjectPropertyChain(<http://e#r> <http://e#s>) <http://e#B>)))"
  "out of fragment: object property expression ObjectPropertyChain"
#guard rejects "Ontology(SubClassOf(<http://e#A> ObjectFoo(<http://e#B>)))"
  "out of fragment: class expression ObjectFoo"

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
#guard axiomsOf "Ontology(ClassAssertion(<http://e#A> _:x))" ==
  some [.classAssertion (.cls "http://e#A") (.anon "x")]
#guard rejects "" "syntax error: no Ontology"
#guard reasonOf "Ontology()" == "accepted"

end ContextCalculus.OWL.ParseTests
