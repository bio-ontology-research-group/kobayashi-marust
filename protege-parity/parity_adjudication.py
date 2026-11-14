#!/usr/bin/env python3
"""Write the adjudication sections of PARITY.md from the ParityRun results.

  parity_adjudication.py <json dir> <adjudication.md> [--diff-tsv diffs.tsv]

Each entry names an ontology and one call (the minimal reproduction), a verdict decided by the OWL 2
direct semantics, and the argument. The answers are read from the result files, so rerunning after a
fix shows the call as "now agrees". Reproduce a single entry with
  parity_show.py <json dir>/<ontology>.json '<call>'
The verdicts are hand-written: they record what was checked in the ontology source or in the
semantics, and need a human decision when a new difference shape appears.
"""
import argparse, csv, json, os, re
from collections import Counter, defaultdict

C = "http://www.w3.org/2002/07/owl#"

# (id, verdict, title, ontology, call, argument)
ENTRIES = [
    # ---------------------------------------------------------------- KM wrong
    ("K1", "KM wrong", "Property assertion queries answer empty sets",
     "ore_ont_13885", "getObjectPropertyValues(http://creativecommons.org/licenses/by/2.0/uk/,http://web.resource.org/cc/permits)",
     "The ontology asserts `ObjectPropertyAssertion(cc:permits <licenses/by/2.0/uk/> cc:DerivativeWorks)` and two more, so the three values are entailed. KM returns the empty node set instead of throwing. "
     "Same shape for `getDataPropertyValues` (next entry) and for every ontology with assertions: `getObjectPropertyValues` 824 calls in 12 ontologies, `getDataPropertyValues` 305 calls in 11."),
    ("K2", "KM wrong", "Data property values: empty set",
     "ore_ont_13885", "getDataPropertyValues(http://purl.org/vocab/frbr/core,http://purl.org/dc/elements/1.1/date)",
     "The ontology asserts `DataPropertyAssertion(dc:date <frbr/core> \"2009-05-16\")`. KM answers the empty set."),
    ("K3", "KM wrong", "Data property domains: empty set",
     "ore_ont_15667", "getDataPropertyDomains(http://www.topbraid.org/2007/01/visual.owl#childIndex,true)",
     "The ontology states `DataPropertyDomain(visual:childIndex visual:Shape)`. KM answers the empty node set; HermiT answers `Shape`. 248 calls in 15 ontologies."),
    ("K4", "KM wrong", "Data property hierarchy: sub and super data properties are empty",
     "ore_ont_13153", "getSubDataProperties(http://sweet.jpl.nasa.gov/2.0/mathOperation.owl#unaryOperation,true)",
     "The ontology states `SubDataPropertyOf(half unaryOperation)`, `SubDataPropertyOf(square unaryOperation)` and `SubDataPropertyOf(squareRoot unaryOperation)`. KM answers the empty node set. "
     "`getSubDataProperties` 46 calls in 8 ontologies and `getSuperDataProperties` 68 calls in 8 ontologies with real hierarchies."),
    ("K5", "KM wrong", "Equivalent data properties are not merged",
     "ore_ont_13153", "getEquivalentDataProperties(http://sweet.jpl.nasa.gov/2.0/chemElement.owl#atomicNumber)",
     "The ontology states `EquivalentDataProperties(atomicNumber hasProtons)`. KM returns the singleton node. 16 calls in 3 ontologies."),
    ("K6", "KM wrong", "Disjoint data properties: empty set",
     "ore_ont_14379", "getDisjointDataProperties(http://www.csiro.au/EventOntology#hasDestinationMail)",
     "The ontology states `DisjointDataProperties(hasDestinationMail hasDestinationSMS)`. KM answers the empty node set. 26 calls in 8 ontologies."),
    ("K7", "KM wrong", "Disjoint classes: empty set",
     "ore_ont_12824", "getDisjointClasses(http://www.ontologydesignpatterns.org/ont/framenet/tbox/AnnotationSet)",
     "The ontology states `DisjointClasses(AnnotationSet CorpDoc Document FECoreSet ...)`. KM answers the empty node set. 30 calls in 9 ontologies for named classes."),
    ("K8", "KM wrong", "Different individuals: empty set",
     "ore_ont_15291", "getDifferentIndividuals(http://ontology.dumontierlab.com/III_2004)",
     "The ontology states `DifferentIndividuals(III_2004 III_2005 III_2006 III_2007 ...)`. KM answers the empty node set. 35 calls in 7 ontologies."),
    ("K9", "KM wrong", "Disjoint object properties: empty set",
     "ore_ont_13885", "getDisjointObjectProperties(http://purl.org/vocab/frbr/core#abridgement)",
     "`abridgement` has domain `Expression` and `creator` has domain `Work`, and the ontology states `DisjointClasses(Expression Work)`. "
     "A pair that cannot share a subject is disjoint, so `creator` is in the answer. KM answers the empty node set. 20 calls in 12 ontologies."),
    ("K10", "KM wrong", "Anonymous class expressions: instances are empty",
     "ore_ont_9666", "getInstances(ObjectOneOf(<http://www.ontologydesignpatterns.org/cp/owl/sequence.owl>),true)",
     "`{a}` has exactly the instance `a`. KM answers the empty node set for every anonymous class expression (49 `getInstances` calls with a non-empty HermiT answer, 13 ontologies)."),
    ("K11", "KM wrong", "Anonymous class expressions: super classes are empty",
     "ore_ont_13759", "getSuperClasses(ObjectIntersectionOf(<http://ontology.dumontierlab.com/yowl-primitive-1.0.owl#Co-crystallography> <http://ontology.dumontierlab.com/yowl-primitive-1.0.owl#NotPhysicallyMappedFeature>),true)",
     "`A and B` is a subclass of `A` and of `B`, so both are super classes of the conjunction. KM answers the empty node set, as it does for every anonymous argument: "
     "`getSuperClasses` 348 calls in 32 ontologies, `getSubClasses` 217 calls in 34, `getDisjointClasses` 57 calls in 28, `getEquivalentClasses` 9 calls in 5. "
     "`isSatisfiable` of such expressions throws `ClassExpressionNotInProfileException` (listed under KM unsupported)."),
    ("K12", "KM wrong", "Equivalent classes of an unsatisfiable expression: node without a member",
     "ore_ont_13885", "getEquivalentClasses(ObjectIntersectionOf(<http://purl.org/vocab/frbr/core#Person> <http://purl.org/vocab/frbr/core#Place>))",
     "`Person` and `Place` are disjoint (`DisjointClasses` in the source), so the conjunction is equivalent to `owl:Nothing`. HermiT answers the node `{owl:Nothing}`. "
     "KM answers a node with no entity, which the OWL API does not allow (a node holds at least one entity). 38 calls in 11 ontologies."),
    ("K13", "KM wrong (cosmetic)", "Super classes of owl:Nothing",
     "ore_ont_12007", "getSuperClasses(http://www.w3.org/2002/07/owl#Nothing,false)",
     "Every class is a super class of `owl:Nothing`, so the non-direct answer is the whole class set. KM answers `{owl:Thing}` for both the direct and the non-direct query; "
     "`getSuperClasses(owl:Nothing, true)` should be the leaf classes. 70 calls, one per ontology and flag, in 35 ontologies. Protégé does not ask this."),
    ("K14", "KM wrong (cosmetic)", "owl:Nothing missing as strict subclass; wrongly direct below owl:Thing",
     "food", "getSubClasses(http://www.w3.org/TR/2003/PR-owl-guide-20031209/food#BlandFish,true)",
     "`owl:Nothing` is a strict subclass of every satisfiable class (OWL API javadoc: `StrictSubClassOf(C, ce)`) and a direct subclass of each leaf. HermiT lists it, KM does not "
     "(7,945 `getSubClasses` calls in 35 ontologies; the same for `getDisjointClasses`, which should contain `owl:Nothing`, 82 calls, and for `getSubDataProperties`/`getSuperDataProperties`/`getDisjoint*Properties` with `owl:bottom*Property`). "
     "In the other direction KM puts `owl:Nothing` directly below `owl:Thing` although `Thing` has other direct subclasses (35 calls, one per ontology): `getSubClasses(owl:Thing, true)`. "
     "Protégé hides `owl:Nothing`; the OWL API contract requires it."),
    ("K15", "KM wrong (cosmetic)", "Domain of the top data property",
     "ore_ont_15667", "getDataPropertyDomains(http://www.w3.org/2002/07/owl#topDataProperty,true)",
     "`owl:Thing` is a domain of every data property, so HermiT's `{owl:Thing}` is right for `owl:topDataProperty`; KM answers the empty node set. 136 calls in 34 ontologies for the top and bottom data property."),
    # ------------------------------------------------------------- HermiT wrong
    ("H1", "HermiT wrong", "Direct types contain a class above another class of the same answer",
     "food", "getTypes(http://www.w3.org/TR/2003/PR-owl-guide-20031209/wine#BancroftChardonnay,true)",
     "A direct answer keeps only the most specific classes. HermiT returns `WhiteWine` next to `Chardonnay` and `DryWhiteWine`, although `Chardonnay` is below `WhiteWine` in the ontology (it is the quirk already recorded in `HermitDifferentialTest`). "
     "KM's answer is the set of most specific types. 16 calls in 2 ontologies (food, wine)."),
    ("H2", "HermiT wrong", "Domain and range of owl:bottomObjectProperty",
     "ore_ont_12007", "getObjectPropertyDomains(http://www.w3.org/2002/07/owl#bottomObjectProperty,false)",
     "The bottom property has no pairs, so every class is a domain and a range (`SubClassOf(ObjectSomeValuesFrom(bottom owl:Thing) C)` holds for all `C`); the direct domain is `owl:Nothing`. "
     "HermiT answers the empty set for the non-direct query and `{owl:Thing}` for the direct one. KM answers all classes and `{owl:Nothing}`. The same flaw is already recorded in `HermitDifferentialTest`. "
     "`getObjectPropertyDomains` and `getObjectPropertyRanges` each differ on all 34 ontologies this way; HermiT shows the same flaw for `getDataPropertyDomains(owl:bottomDataProperty)` (KM answers the empty set there, so both are wrong; see K15)."),
    ("H3", "HermiT wrong", "isEntailed(DisjointDataProperties) throws",
     "ore_ont_11401", "isEntailed(DisjointDataProperties(<http://ontology.dumontierlab.com/ends> <http://ontology.dumontierlab.com/hasValue>))",
     "A valid axiom between two named data properties. HermiT answers `IllegalArgumentException: In OWL 2 DL, owl:topDataProperty is only allowed to occur in the super property position` (its own rewriting uses the top data property). "
     "48 calls in 25 ontologies. KM answers `UnsupportedEntailmentTypeException` for this axiom type, so neither answers."),
    ("H4", "HermiT wrong", "isEntailed(InverseObjectProperties(p, p)) throws NullPointerException",
     "ore_ont_15985", "isEntailed(InverseObjectProperties(<http://purl.obolibrary.org/obo/OBO_REL_part_of> <http://purl.obolibrary.org/obo/OBO_REL_part_of>))",
     "`InverseObjectProperties(p, q)` is a valid axiom; HermiT dereferences a missing role node when the ontology has no inverse roles (the bug recorded in `HermitDifferentialTest`). 7 calls in 6 ontologies; KM answers each of them."),
    # ----------------------------------------------------------- convention only
    ("C1", "convention only", "Same-individual nodes in getInstances",
     "food", "getInstances(http://www.w3.org/TR/2003/PR-owl-guide-20031209/wine#WineBody,true)",
     "Both reasoners return the same six individuals. HermiT (policy `BY_NAME`, which both report) puts each in its own node; KM groups `food:Full` with `wine:Full` because the ontologies state them equal. "
     "The OWL API allows grouping only under `BY_SAME_AS`, so KM deviates from the policy it reports; the content is the same. 39 calls in 5 ontologies."),
    ("C2", "convention only", "getTimeOut",
     "ore_ont_12007", "getTimeOut()",
     "HermiT with the configuration used here reports -1, KM reports `Long.MAX_VALUE`; both mean no limit."),
    ("C3", "convention only", "Precomputed state and precomputable types",
     "ore_ont_12007", "getPrecomputableInferenceTypes()",
     "HermiT lists every type it can compute, including `DATA_PROPERTY_HIERARCHY` and `OBJECT_PROPERTY_ASSERTIONS`; KM lists four. The `isPrecomputed` differences follow from what each reasoner computes eagerly "
     "(37 calls where KM is true and HermiT false, 59 the other way). The shorter list is a coverage gap (see K1 to K5), the flags are laziness."),
    ("C4", "convention only", "Inconsistent ontology: top and bottom queries",
     "ore_ont_5014", "getTopClassNode()",
     "On an inconsistent ontology HermiT throws `InconsistentOntologyException` from `getTopClassNode`, `getBottomClassNode`, `getUnsatisfiableClasses` and the data property top and bottom nodes. KM answers them. "
     "`protege/README.md` lists this set as one that does not throw, as in HermiT; with HermiT 1.4.3.456 and its default configuration it does throw. One ontology."),
]


def short(x):
    return re.sub(r"https?://[^\s\",\]\)<>]*[#/]", "", x)


def render_answer(x):
    if x.get("status") != "ok":
        return f"{x.get('status')} {x.get('exc', '')}"
    a = x["ans"]
    t = a["t"]
    if t in ("node", "nodeset"):
        ns = ["{" + ", ".join(short(e) for e in n) + "}" for n in a["nodes"]]
        body = ", ".join(ns[:8]) + (f", ... ({len(ns)} nodes)" if len(ns) > 8 else "")
        return "[" + body + "]"
    if t == "set":
        it = [short(e) for e in a["items"]]
        return "{" + ", ".join(it[:8]) + (f", ... ({len(it)})" if len(it) > 8 else "") + "}"
    if t == "bool":
        return str(a["v"]).lower()
    return str(a.get("v"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("report")
    a = ap.parse_args()
    cache = {}
    sections = defaultdict(list)
    for eid, verdict, title, ont, call, arg in ENTRIES:
        path = os.path.join(a.outdir, ont + ".json")
        if not os.path.exists(path):
            continue
        d = cache.setdefault(ont, json.load(open(path)))
        c = next((x for x in d["calls"] if x["id"] == call), None)
        if c is None:
            sections[verdict.split(" (")[0]].append(f"- **{eid}. {title}.** Call `{short(call)}` not in the plan of `{ont}`.")
            continue
        state = c.get("verdict")
        now = "now agrees" if state in ("agree", "both_error_same") else f"verdict: {state}"
        sections[verdict.split(" (")[0]].append(
            f"- **{eid}. {title}** ({verdict}; {now}).\n"
            f"  - Ontology `{ont}`, call `{short(call)}`.\n"
            f"  - HermiT: `{render_answer(c['hermit'])[:300]}`\n"
            f"  - KM: `{render_answer(c['km'])[:300]}`\n"
            f"  - Reproduce: `parity_show.py {ont}.json '{call[:80]}'`.\n"
            f"  - Why: {arg}")
    out = ["## Adjudication\n",
           "Each difference shape of the top-differences table was decided by the OWL 2 direct semantics, checking the ontology source "
           "(`v150-corpus/files/<ontology>.owl`) where the answer rests on an asserted axiom. Counts are over this run. "
           "A \"KM wrong\" entry means KM's answer is not what the semantics entails, whatever HermiT does. "
           "The entries are written by hand in `parity_adjudication.py`; a new difference shape needs a new entry.\n"]
    for title, key in (("KM wrong", "KM wrong"), ("HermiT wrong", "HermiT wrong"), ("Convention only", "convention only")):
        out.append(f"### {title}\n")
        out.extend(sections.get(key, ["None."]))
        out.append("")
    open(a.report, "w").write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
