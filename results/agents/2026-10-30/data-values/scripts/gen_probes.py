"""Write the data-value probe ontologies (OWL functional syntax).

Each probe exists in a small form and, with `-pad`, padded by 1,100
individuals carrying distinct values of an unrelated or the same property,
so that the value vocabulary exceeds the pairwise limit (1,024) and the
linear relation form runs.
"""
import sys, os
out = sys.argv[1]
H = """Prefix(:=<http://example.org/t#>)
Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)
Prefix(owl:=<http://www.w3.org/2002/07/owl#>)
Ontology(<http://example.org/t>
Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D)) Declaration(Class(:E)) Declaration(Class(:F))
Declaration(DataProperty(:u)) Declaration(DataProperty(:w)) Declaration(DataProperty(:v)) Declaration(DataProperty(:pad))
Declaration(ObjectProperty(:r))
Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b)) Declaration(NamedIndividual(:x))
"""
def i(v): return f'"{v}"^^xsd:integer'
P = {}
P['functional_merge_clash'] = f"""FunctionalDataProperty(:u) FunctionalObjectProperty(:r)
ObjectPropertyAssertion(:r :x :a) ObjectPropertyAssertion(:r :x :b)
DataPropertyAssertion(:u :a {i(1)}) DataPropertyAssertion(:u :b {i(2)})
"""
P['functional_merge_equal'] = f"""FunctionalDataProperty(:u) FunctionalObjectProperty(:r)
ObjectPropertyAssertion(:r :x :a) ObjectPropertyAssertion(:r :x :b)
DataPropertyAssertion(:u :a {i(1)}) DataPropertyAssertion(:u :b "1.0"^^xsd:decimal)
EquivalentClasses(:E ObjectOneOf(:a)) SubClassOf(DataHasValue(:u {i(1)}) :D)
"""
P['functional_two_values'] = f"""SubClassOf(:A DataMaxCardinality(1 :u))
ClassAssertion(:A :a) DataPropertyAssertion(:u :a "p"^^xsd:string) DataPropertyAssertion(:u :a "q"^^xsd:string)
"""
P['qualified_atmost'] = f"""SubClassOf(:A DataMaxCardinality(1 :u DatatypeRestriction(xsd:integer xsd:minInclusive {i(10)})))
ClassAssertion(:A :a) DataPropertyAssertion(:u :a {i(5)}) DataPropertyAssertion(:u :a {i(20)})
ClassAssertion(:A :b) DataPropertyAssertion(:u :b {i(15)}) DataPropertyAssertion(:u :b {i(25)})
"""
P['qualified_atmost_ok'] = f"""SubClassOf(:A DataMaxCardinality(1 :u DatatypeRestriction(xsd:integer xsd:minInclusive {i(10)})))
ClassAssertion(:A :a) DataPropertyAssertion(:u :a {i(5)}) DataPropertyAssertion(:u :a {i(20)})
EquivalentClasses(:E ObjectOneOf(:a)) EquivalentClasses(:F DataSomeValuesFrom(:u DatatypeRestriction(xsd:integer xsd:maxExclusive {i(10)})))
"""
P['subproperty_functional'] = f"""SubDataPropertyOf(:u :w) SubDataPropertyOf(:v :w) FunctionalDataProperty(:w)
DataPropertyAssertion(:u :a {i(3)}) DataPropertyAssertion(:v :a "3.0"^^xsd:decimal)
DataPropertyAssertion(:u :b {i(3)}) DataPropertyAssertion(:v :b {i(4)})
"""
P['hasvalue_nominal'] = f"""EquivalentClasses(:C DataHasValue(:u "x"^^xsd:string)) EquivalentClasses(:E ObjectOneOf(:a))
DataPropertyAssertion(:u :a "x"^^xsd:string) EquivalentClasses(:F ObjectOneOf(:b)) DataPropertyAssertion(:u :b "y")
"""
P['facet_exists'] = f"""EquivalentClasses(:D DataSomeValuesFrom(:u DatatypeRestriction(xsd:integer xsd:minInclusive {i(500)})))
EquivalentClasses(:E ObjectOneOf(:a)) EquivalentClasses(:F ObjectOneOf(:b))
DataPropertyAssertion(:u :a {i(550)}) DataPropertyAssertion(:u :b {i(3)})
"""
P['range_clash'] = f"""DataPropertyRange(:u xsd:integer) DataPropertyAssertion(:u :a "z"^^xsd:string)
"""
P['count_finite_range'] = f"""SubClassOf(:A DataMinCardinality(10 :u DatatypeRestriction(xsd:integer xsd:minInclusive {i(1)} xsd:maxInclusive {i(9)})))
SubClassOf(:B DataMinCardinality(9 :u DatatypeRestriction(xsd:integer xsd:minInclusive {i(1)} xsd:maxInclusive {i(9)})))
"""
P['count_byte'] = f"""SubClassOf(:A DataMinCardinality(257 :u xsd:unsignedByte)) SubClassOf(:B DataMinCardinality(256 :u xsd:unsignedByte))
"""
P['count_float_point'] = f"""SubClassOf(:A DataMinCardinality(2 :u DatatypeRestriction(xsd:float xsd:minInclusive "1.0"^^xsd:float xsd:maxInclusive "1.0"^^xsd:float)))
SubClassOf(:B DataMinCardinality(2 :u DatatypeRestriction(xsd:float xsd:minInclusive "0.0"^^xsd:float xsd:maxInclusive "0.0"^^xsd:float)))
"""
P['count_with_assertions'] = f"""DataPropertyRange(:u DataOneOf({i(1)} {i(2)})) ClassAssertion(DataMinCardinality(3 :u) :a)
"""
P['count_with_assertions_ok'] = f"""DataPropertyRange(:u DataOneOf({i(1)} {i(2)} {i(3)})) ClassAssertion(DataMinCardinality(3 :u) :a)
DataPropertyAssertion(:u :a {i(1)}) EquivalentClasses(:E ObjectOneOf(:a))
EquivalentClasses(:F DataHasValue(:u {i(3)}))
"""
P['disjoint_data_properties'] = f"""DisjointDataProperties(:u :v) DataPropertyAssertion(:u :a {i(1)}) DataPropertyAssertion(:v :a "1.0"^^xsd:decimal)
"""
P['disjoint_data_properties_ok'] = f"""DisjointDataProperties(:u :v) DataPropertyAssertion(:u :a {i(1)}) DataPropertyAssertion(:v :a {i(2)})
EquivalentClasses(:E ObjectOneOf(:a)) SubClassOf(DataHasValue(:v {i(2)}) :D)
"""
P['atleast_two_shared'] = f"""SubDataPropertyOf(:u :w) SubDataPropertyOf(:v :w) EquivalentClasses(:D DataMinCardinality(2 :w))
DataPropertyAssertion(:u :a {i(7)}) DataPropertyAssertion(:v :a {i(7)}) EquivalentClasses(:E ObjectOneOf(:a))
DataPropertyAssertion(:u :b {i(7)}) DataPropertyAssertion(:v :b {i(8)}) EquivalentClasses(:F ObjectOneOf(:b))
"""
P['inverse_functional_merge'] = f"""Declaration(ObjectProperty(:s)) InverseFunctionalObjectProperty(:s) SubClassOf(owl:Thing DataMaxCardinality(1 :u))
ObjectPropertyAssertion(:s :a :x) ObjectPropertyAssertion(:s :b :x)
DataPropertyAssertion(:u :a "k1") DataPropertyAssertion(:u :b "k2")
"""
P['negative_assertion'] = f"""NegativeDataPropertyAssertion(:u :a {i(1)}) EquivalentClasses(:E ObjectOneOf(:a))
EquivalentClasses(:F DataHasValue(:u {i(1)})) SubClassOf(:E DataSomeValuesFrom(:u DataOneOf({i(1)} {i(2)})))
EquivalentClasses(:D DataHasValue(:u {i(2)}))
"""
os.makedirs(out, exist_ok=True)
for name, body in P.items():
    for pad in (False, True):
        text = H + body
        if pad:
            prop = ':u' if 'functional' in name or 'merge' in name else ':pad'
            text += ''.join(f'Declaration(NamedIndividual(:p{k}))\nDataPropertyAssertion({prop} :p{k} {i(1000+k)})\n' for k in range(1100))
        text += ')\n'
        open(os.path.join(out, name + ('-pad' if pad else '') + '.ofn'), 'w').write(text)
print(len(P) * 2, 'probes')
