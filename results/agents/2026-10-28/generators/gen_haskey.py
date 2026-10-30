import sys
def I(n): return f"<urn:t#{n}>"
P="Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
DECL=" ".join([f"Declaration(Class({I(c)}))" for c in "AB"]+[f"Declaration(ObjectProperty({I('r')}))",f"Declaration(DataProperty({I('d')}))"]+[f"Declaration(NamedIndividual({I(i)}))" for i in "abc"])
V=lambda n:f"Variable({I(n)})"
ORULE=f"DLSafeRule(Body(ClassAtom({I('A')} {V('x')}) ClassAtom({I('A')} {V('y')}) ObjectPropertyAtom({I('r')} {V('x')} {V('z')}) ObjectPropertyAtom({I('r')} {V('y')} {V('z')})) Head(SameIndividualAtom({V('x')} {V('y')})))"
DRULE=f"DLSafeRule(Body(ClassAtom({I('A')} {V('x')}) ClassAtom({I('A')} {V('y')}) DataPropertyAtom({I('d')} {V('x')} {V('v')}) DataPropertyAtom({I('d')} {V('y')} {V('v')})) Head(SameIndividualAtom({V('x')} {V('y')})))"
AB=f"ClassAssertion({I('A')} {I('a')}) ClassAssertion({I('A')} {I('b')}) ClassAssertion({I('B')} {I('a')})"
NEG=f"ClassAssertion(ObjectComplementOf({I('B')}) {I('b')})"
ROBJ=f"ObjectPropertyAssertion({I('r')} {I('a')} {I('c')}) ObjectPropertyAssertion({I('r')} {I('b')} {I('c')})"
def dat(va,vb): return f"DataPropertyAssertion({I('d')} {I('a')} {va}) DataPropertyAssertion({I('d')} {I('b')} {vb})"
OKEY=f"HasKey({I('A')} ({I('r')}) ())"; DKEY=f"HasKey({I('A')} () ({I('d')}))"
cases={
 "obj_rule":[ORULE,ROBJ],"obj_key":[OKEY,ROBJ],
 "dat_rule_same":[DRULE,dat('"1"^^xsd:integer','"1"^^xsd:integer')],
 "dat_rule_int":[DRULE,dat('"1"^^xsd:integer','"01"^^xsd:integer')],
 "dat_rule_dec":[DRULE,dat('"1"^^xsd:integer','"1.0"^^xsd:decimal')],
 "dat_rule_diff":[DRULE,dat('"1"^^xsd:integer','"2"^^xsd:integer')],
 "dat_key_same":[DKEY,dat('"1"^^xsd:integer','"1"^^xsd:integer')],
 "dat_key_int":[DKEY,dat('"1"^^xsd:integer','"01"^^xsd:integer')],
 "dat_key_dec":[DKEY,dat('"1"^^xsd:integer','"1.0"^^xsd:decimal')],
 "dat_key_diff":[DKEY,dat('"1"^^xsd:integer','"2"^^xsd:integer')],
}
for n,parts in cases.items():
  for neg in (True,False):
    body=" ".join([DECL]+parts+[AB]+([NEG] if neg else []))
    open(f"{n}{'' if neg else '_ctl'}.ofn","w").write(P+f"Ontology(<urn:t>\n{body}\n)\n")
# anonymous: Q is an A with r-value c, disjoint from B; a is a named A with r(a,c) and B(a).
ANON=f"SubClassOf({I('Q')} ObjectIntersectionOf({I('A')} ObjectHasValue({I('r')} {I('c')}))) DisjointClasses({I('Q')} {I('B')}) Declaration(Class({I('Q')}))"
ANONABOX=f"ClassAssertion({I('A')} {I('a')}) ClassAssertion({I('B')} {I('a')}) ObjectPropertyAssertion({I('r')} {I('a')} {I('c')}) ClassAssertion(ObjectSomeValuesFrom({I('r')} {I('Q')}) {I('b')})"
for n,k in (("anon_key",OKEY),("anon_rule",ORULE)):
  open(f"{n}.ofn","w").write(P+f"Ontology(<urn:t>\n{DECL} {k} {ANON} {ANONABOX}\n)\n")
# prefixed spelling of a data key
open("dat_key_int_prefixed.ofn","w").write(P.replace("Prefix(xsd","Prefix(:=<urn:t#>)\nPrefix(xsd")+"Ontology(<urn:t>\n"+(" ".join([DECL,DKEY,dat('"1"^^xsd:integer','"01"^^xsd:integer'),AB,NEG])).replace("<urn:t#",":").replace(">)",")").replace("> "," ")+"\n)\n")
