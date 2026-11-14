"""Count the axiom heads of an OFN document with an independent tokenizer
(for the structural part of the v1.7.0 C0 differential test).

usage: heads.py FILE  -> prints a JSON object {kind: count} keyed like the
Lean `km-owl-parse` axiomCounts (Declaration split by entity kind; the
declarations of owl:Thing, owl:Nothing and the top and bottom properties
are not counted, as the Lean parser skips them)."""
import json, re, sys

KIND = {"SubClassOf": "subClassOf", "EquivalentClasses": "equivalentClasses",
        "DisjointClasses": "disjointClasses", "ObjectPropertyDomain": "domain",
        "ObjectPropertyRange": "range", "SubObjectPropertyOf": "subObjectPropertyOf",
        "EquivalentObjectProperties": "equivalentObjectProperties",
        "InverseObjectProperties": "inverseObjectProperties",
        "TransitiveObjectProperty": "transitive", "SymmetricObjectProperty": "symmetric",
        "DisjointUnion": "disjointUnion", "DisjointObjectProperties": "disjointObjectProperties",
        "FunctionalObjectProperty": "functional",
        "InverseFunctionalObjectProperty": "inverseFunctional",
        "ReflexiveObjectProperty": "reflexive", "IrreflexiveObjectProperty": "irreflexive",
        "AsymmetricObjectProperty": "asymmetric", "SubDataPropertyOf": "subDataPropertyOf",
        "EquivalentDataProperties": "equivalentDataProperties",
        "DisjointDataProperties": "disjointDataProperties", "DataPropertyDomain": "dataDomain",
        "DataPropertyRange": "dataRange", "FunctionalDataProperty": "functionalData",
        "DatatypeDefinition": "datatypeDefinition", "HasKey": "hasKey",
        "SameIndividual": "sameIndividual", "DifferentIndividuals": "differentIndividuals",
        "ClassAssertion": "classAssertion", "ObjectPropertyAssertion": "objectPropertyAssertion",
        "NegativeObjectPropertyAssertion": "negativeObjectPropertyAssertion",
        "DataPropertyAssertion": "dataPropertyAssertion",
        "NegativeDataPropertyAssertion": "negativeDataPropertyAssertion"}
DECL = {"Class": "declareClass", "ObjectProperty": "declareObjectProperty",
        "DataProperty": "declareDataProperty", "NamedIndividual": "declareNamedIndividual",
        "Datatype": "declareDatatype", "AnnotationProperty": "declareAnnotationProperty"}
OWL = "http://www.w3.org/2002/07/owl#"
SKIP_DECL = {OWL + x for x in ["Thing", "Nothing", "topObjectProperty", "bottomObjectProperty",
                               "topDataProperty", "bottomDataProperty"]}
TOK = re.compile(rb'\s+|#[^\n\r]*|<[^>]*>|"(?:\\.|[^"\\])*"|\(|\)|[^\s()]+')

def read(data):
    """The document as nested lists [head, args...]; atoms are bytes."""
    root = ["", []]
    stack = [root]
    pending = None
    for m in TOK.finditer(data):
        t = m.group(0)
        if t[:1].isspace() or t[:1] == b"#":
            continue
        top = stack[-1][1]
        if t == b"(":
            head = ""
            if top and isinstance(top[-1], bytes) and re.fullmatch(rb"[A-Za-z]+", top[-1]) and pending is top[-1]:
                head = top.pop().decode()
            node = [head, []]
            top.append(node)
            stack.append(node)
            pending = None
        elif t == b")":
            stack.pop()
            pending = None
        else:
            top.append(t)
            pending = t
    return root[1]

def main():
    nodes = read(open(sys.argv[1], "rb").read())
    prefixes = {"owl": OWL}
    counts = {}
    for n in nodes:
        if isinstance(n, list) and n[0] == "Prefix":
            txt = b"".join(a for a in n[1] if isinstance(a, bytes)).decode(errors="replace")
            p, _, v = txt.partition(":=")
            prefixes[p] = v.strip("<>")
    onto = [n for n in nodes if isinstance(n, list) and n[0] == "Ontology"]
    for ax in (onto[0][1] if onto else []):
        if not isinstance(ax, list):
            continue
        h, args = ax
        if h in KIND:
            counts[KIND[h]] = counts.get(KIND[h], 0) + 1
        elif h == "Declaration":
            ent = [a for a in args if isinstance(a, list) and a[0] != "Annotation"]
            if ent and ent[0][0] in DECL and ent[0][1]:
                s = ent[0][1][0].decode(errors="replace")
                if s.startswith("<"):
                    iri = s[1:-1]
                else:
                    p, _, l = s.partition(":")
                    iri = prefixes.get(p, p + ":") + l
                if iri not in SKIP_DECL:
                    k = DECL[ent[0][0]]
                    counts[k] = counts.get(k, 0) + 1
    print(json.dumps(counts))

if __name__ == "__main__":
    main()
