import sys, os
out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HDR = """Prefix(:=<http://example.org/t#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Ontology(<http://example.org/t>
Declaration(DataProperty(:d))
Declaration(DataProperty(:e))
"""
I = lambda v: '"%s"^^xsd:integer' % v
RANGES = {
 "E_compl_literal": "DataComplementOf(rdfs:Literal)",
 "E_int_and_string": "DataIntersectionOf(xsd:integer xsd:string)",
 "E_int_and_not_int": "DataIntersectionOf(xsd:integer DataComplementOf(xsd:integer))",
 "E_crossed_facets": "DatatypeRestriction(xsd:integer xsd:minInclusive %s xsd:maxInclusive %s)" % (I(5), I(3)),
 "E_disjoint_oneofs": "DataIntersectionOf(DataOneOf(%s) DataOneOf(%s))" % (I(1), I(2)),
 "E_compl_excluded_middle": "DataComplementOf(DataUnionOf(xsd:string DataComplementOf(xsd:string)))",
 "E_union_of_empties": "DataUnionOf(DataComplementOf(rdfs:Literal) DataIntersectionOf(xsd:boolean xsd:integer))",
 "E_defined_empty": ":Empty",
 "E_bool_and_compl_oneof": "DataIntersectionOf(xsd:boolean DataComplementOf(DataOneOf(\"true\"^^xsd:boolean \"false\"^^xsd:boolean)))",
 "U_literal": "rdfs:Literal",
 "U_double_compl": "DataComplementOf(DataComplementOf(rdfs:Literal))",
 "U_excluded_middle": "DataUnionOf(xsd:integer DataComplementOf(xsd:integer))",
 "U_compl_empty_int": "DataComplementOf(DataIntersectionOf(xsd:integer xsd:string))",
 "U_union_with_literal": "DataUnionOf(xsd:string rdfs:Literal)",
 "U_defined_top": ":Full",
 "N_integer": "xsd:integer",
 "N_compl_integer": "DataComplementOf(xsd:integer)",
}
def body(R):
    ax = []
    cls = []
    def eq(name, expr):
        cls.append(name); ax.append("EquivalentClasses(:%s %s)" % (name, expr))
    # reference classes
    eq("Has", "DataMinCardinality(1 :d)")
    eq("Two", "DataMinCardinality(2 :d)")
    eq("No", "DataMaxCardinality(0 :d)")
    eq("AtMostOne", "DataMaxCardinality(1 :d)")
    eq("Some", "DataSomeValuesFrom(:d %s)" % R)
    eq("All", "DataAllValuesFrom(:d %s)" % R)
    eq("Min1", "DataMinCardinality(1 :d %s)" % R)
    eq("Min2", "DataMinCardinality(2 :d %s)" % R)
    eq("Max0", "DataMaxCardinality(0 :d %s)" % R)
    eq("Max1", "DataMaxCardinality(1 :d %s)" % R)
    eq("Exact0", "DataExactCardinality(0 :d %s)" % R)
    eq("Exact1", "DataExactCardinality(1 :d %s)" % R)
    eq("SomeLitAllR", "ObjectIntersectionOf(DataSomeValuesFrom(:d rdfs:Literal) DataAllValuesFrom(:d %s))" % R)
    eq("HasValAllR", "ObjectIntersectionOf(DataHasValue(:d %s) DataAllValuesFrom(:d %s))" % (I(1), R))
    eq("NotSome", "ObjectComplementOf(DataSomeValuesFrom(:d %s))" % R)
    eq("NotAll", "ObjectComplementOf(DataAllValuesFrom(:d %s))" % R)
    # range axiom on e
    ax.append("DataPropertyRange(:e %s)" % R)
    eq("HasE", "DataMinCardinality(1 :e)")
    eq("HasEval", "DataHasValue(:e %s)" % I(1))
    ax.append("SubClassOf(:A :Has)")
    ax.append("SubClassOf(:B :No)")
    cls += ["A", "B"]
    return cls, ax
REFS = {"Has","Two","No","AtMostOne"}
TARGETS = ["Some","All","Min1","Min2","Max0","Max1","Exact0","Exact1","SomeLitAllR","HasValAllR","NotSome","NotAll","HasE"]
import itertools
def pick(cls, ax, target):
    keep = REFS | {target} | ({"HasEval"} if target=="HasE" else set())
    c2 = [c for c in cls if c in keep]
    a2 = [a for a in ax if any(("(:%s " % c) in a for c in c2) or (target=="HasE" and a.startswith("DataPropertyRange"))]
    a2 = [a for a in a2 if not a.startswith("SubClassOf")]
    return c2, a2
for (name, R), target in itertools.product(list(RANGES.items()), TARGETS):
    cls, ax = pick(*body(R), target)
    name = name + "__" + target
    decl = ["Declaration(Class(:%s))" % c for c in cls]
    extra = []
    if ":Empty" in R:
        extra += ["Declaration(Datatype(:Empty))", "DatatypeDefinition(:Empty DataComplementOf(rdfs:Literal))"]
    if ":Full" in R:
        extra += ["Declaration(Datatype(:Full))", "DatatypeDefinition(:Full DataUnionOf(xsd:string DataComplementOf(xsd:string)))"]
    with open(os.path.join(out, name + ".ofn"), "w") as f:
        f.write(HDR + "\n".join(decl + extra + ax) + "\n)\n")
# bottom/top data property
bt = HDR + """Declaration(DataProperty(:f))
Declaration(Class(:Bs))
Declaration(Class(:Bm))
Declaration(Class(:Bv))
Declaration(Class(:Fs))
Declaration(Class(:Fa))
Declaration(Class(:Ball))
Declaration(Class(:Bmax))
Declaration(Class(:Ts))
Declaration(Class(:A))
EquivalentClasses(:Bs DataSomeValuesFrom(owl:bottomDataProperty rdfs:Literal))
EquivalentClasses(:Bm DataMinCardinality(1 owl:bottomDataProperty))
EquivalentClasses(:Bv DataHasValue(owl:bottomDataProperty "1"^^xsd:integer))
EquivalentClasses(:Ball DataAllValuesFrom(owl:bottomDataProperty DataComplementOf(rdfs:Literal)))
EquivalentClasses(:Bmax DataMaxCardinality(0 owl:bottomDataProperty))
SubDataPropertyOf(:f owl:bottomDataProperty)
EquivalentClasses(:Fs DataSomeValuesFrom(:f xsd:integer))
EquivalentClasses(:Fa DataAllValuesFrom(:f DataComplementOf(rdfs:Literal)))
EquivalentClasses(:Ts DataSomeValuesFrom(owl:topDataProperty rdfs:Literal))
SubClassOf(:A DataHasValue(:d "1"^^xsd:integer))
)
"""
open(os.path.join(out, "bottom_data_property.ofn"), "w").write(bt.replace("Declaration(Class(:Ts))\n","").replace("EquivalentClasses(:Ts DataSomeValuesFrom(owl:topDataProperty rdfs:Literal))\n",""))
