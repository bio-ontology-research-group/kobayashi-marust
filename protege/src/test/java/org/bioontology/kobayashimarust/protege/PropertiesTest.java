package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.*;

import static org.junit.Assert.*;

/**
 * Object property queries answered from {@code km classify --properties}:
 * hand-written expectations on small ontologies. The comparison with HermiT
 * on the same ontologies is in {@link HermitDifferentialTest}.
 */
public class PropertiesTest {

    static final String NS = "http://example.org/prop#";
    private static final String HEAD = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n";

    /** Sub-properties, a chain, transitivity and a declared inverse. */
    static final String CHAIN = HEAD + "Ontology(<http://example.org/prop-chain>\n"
            + "Declaration(Class(:Person)) Declaration(Class(:Adult))\n"
            + "Declaration(ObjectProperty(:hasMother)) Declaration(ObjectProperty(:hasParent))\n"
            + "Declaration(ObjectProperty(:hasGrandparent)) Declaration(ObjectProperty(:ancestorOf))\n"
            + "Declaration(ObjectProperty(:descendantOf)) Declaration(ObjectProperty(:parentOf))\n"
            + "SubObjectPropertyOf(:hasMother :hasParent)\n"
            + "SubObjectPropertyOf(ObjectPropertyChain(:hasParent :hasParent) :hasGrandparent)\n"
            + "SubObjectPropertyOf(:parentOf :ancestorOf)\nTransitiveObjectProperty(:ancestorOf)\n"
            + "InverseObjectProperties(:hasParent :parentOf)\n"
            + "InverseObjectProperties(:descendantOf :ancestorOf)\n"
            + "ObjectPropertyDomain(:hasParent :Person)\nObjectPropertyRange(:hasParent :Adult)\n"
            + "SubClassOf(:Adult :Person)\n"
            + ")\n";

    /** An inferred inverse (a is the inverse of b through x, without saying so), a symmetric property and an inferred one. */
    static final String INVERSES = HEAD + "Ontology(<http://example.org/prop-inv>\n"
            + "Declaration(ObjectProperty(:a)) Declaration(ObjectProperty(:b))\n"
            + "Declaration(ObjectProperty(:sym)) Declaration(ObjectProperty(:selfInv))\n"
            + "Declaration(ObjectProperty(:c)) Declaration(ObjectProperty(:d))\n"
            + "Declaration(Class(:A)) Declaration(Class(:B))\n"
            + "Declaration(ObjectProperty(:x))\n"
            + "InverseObjectProperties(:a :x)\nEquivalentObjectProperties(:x :b)\n"
            + "SymmetricObjectProperty(:sym)\n"
            + "Declaration(ObjectProperty(:y))\n"
            + "InverseObjectProperties(:selfInv :y)\nEquivalentObjectProperties(:selfInv :y)\n"
            + "EquivalentObjectProperties(:c :d)\n"
            + "ObjectPropertyDomain(:a :A)\nObjectPropertyRange(:a :B)\n"
            + ")\n";

    /** An empty property: its domain is disjoint from itself. */
    static final String EMPTY = HEAD + "Ontology(<http://example.org/prop-empty>\n"
            + "Declaration(Class(:A)) Declaration(Class(:B))\n"
            + "Declaration(ObjectProperty(:e)) Declaration(ObjectProperty(:f)) Declaration(ObjectProperty(:g))\n"
            + "DisjointClasses(:A :B)\n"
            + "ObjectPropertyDomain(:e :A)\nObjectPropertyDomain(:e :B)\n"
            + "SubObjectPropertyOf(:f :e)\nSubObjectPropertyOf(:g :f)\n"
            + ")\n";

    /** One individual in every model: a property is empty or universal, and here u and v are universal. */
    static final String UNIVERSAL = HEAD + "Ontology(<http://example.org/prop-top>\n"
            + "Declaration(Class(:A)) Declaration(NamedIndividual(:n))\n"
            + "Declaration(ObjectProperty(:u)) Declaration(ObjectProperty(:v)) Declaration(ObjectProperty(:w))\n"
            + "SubClassOf(owl:Thing ObjectOneOf(:n))\n"
            + "ReflexiveObjectProperty(:u)\nReflexiveObjectProperty(:v)\n"
            + "ObjectPropertyDomain(:w :A)\n"
            + ")\n";

    /** The universal ontology with an inverse role, so HermiT puts inverse expressions into its hierarchy. */
    static final String UNIVERSAL_INVERSE = UNIVERSAL.replace("ObjectPropertyDomain(:w :A)\n",
            "ObjectPropertyDomain(:w :A)\nDeclaration(ObjectProperty(:wi)) InverseObjectProperties(:w :wi)\n");

    /** Properties with no inverse roles anywhere: HermiT keeps inverse expressions out of its hierarchy. */
    static final String PLAIN = HEAD + "Ontology(<http://example.org/prop-plain>\n"
            + "Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:s))\n"
            + "Declaration(Class(:A))\n"
            + "SubObjectPropertyOf(:p :q)\nSubObjectPropertyOf(:q :s)\n"
            + "ObjectPropertyDomain(:s :A)\n"
            + ")\n";

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();

    @After
    public void closeReasoners() {
        for (OWLReasoner r : open) r.dispose();
    }

    private KMReasoner km(OWLOntology ontology) {
        KMReasoner r = (KMReasoner) new KMReasonerFactory().createReasoner(ontology);
        open.add(r);
        return r;
    }

    private static OWLDataFactory factory(OWLOntology o) { return o.getOWLOntologyManager().getOWLDataFactory(); }

    private static OWLObjectProperty p(OWLDataFactory df, String name) {
        return df.getOWLObjectProperty(IRI.create(NS + name));
    }

    private static OWLClass c(OWLDataFactory df, String name) { return df.getOWLClass(IRI.create(NS + name)); }

    private static String name(OWLObjectPropertyExpression e) {
        if (e.isOWLTopObjectProperty()) return "top";
        if (e.isOWLBottomObjectProperty()) return "bot";
        String base = e.getNamedProperty().getIRI().getShortForm();
        return e.isAnonymous() ? base + "-" : base;
    }

    static Set<String> nodeNames(Node<OWLObjectPropertyExpression> n) {
        Set<String> out = new TreeSet<>();
        for (OWLObjectPropertyExpression e : n.getEntities()) out.add(name(e));
        return out;
    }

    static Set<String> nodes(NodeSet<OWLObjectPropertyExpression> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<OWLObjectPropertyExpression> n : ns.getNodes()) out.add(nodeNames(n).toString());
        return out;
    }

    private static Set<String> classNodes(NodeSet<OWLClass> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<OWLClass> n : ns.getNodes()) {
            Set<String> one = new TreeSet<>();
            for (OWLClass k : n.getEntities()) one.add(k.getIRI().getShortForm());
            out.add(one.toString());
        }
        return out;
    }

    private static Set<String> set(String... items) { return new TreeSet<>(Arrays.asList(items)); }

    @Test
    public void hierarchyWithSubPropertiesChainsTransitivityAndInverses() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        // The chain does not change the hierarchy. hasParent is the inverse of parentOf, so its
        // node holds both spellings, and its inverse hierarchy mirrors the named one.
        assertEquals(set("[hasParent, parentOf-]"), nodes(r.getSuperObjectProperties(p(df, "hasMother"), true)));
        assertEquals(set("[hasParent, parentOf-]", "[ancestorOf-, descendantOf]", "[top]"),
                nodes(r.getSuperObjectProperties(p(df, "hasMother"), false)));
        assertEquals(set("[hasMother]"), nodes(r.getSubObjectProperties(p(df, "hasParent"), true)));
        assertEquals(set("[hasMother]", "[bot]"), nodes(r.getSubObjectProperties(p(df, "hasParent"), false)));
        assertEquals(set("[hasMother-]"), nodes(r.getSubObjectProperties(p(df, "parentOf"), true)));
        // parentOf is below ancestorOf (equivalent to descendantOf-).
        assertEquals(set("[ancestorOf, descendantOf-]"), nodes(r.getSuperObjectProperties(p(df, "parentOf"), true)));
        assertEquals(set("[ancestorOf-, descendantOf]"), nodes(r.getSuperObjectProperties(p(df, "hasParent"), true)));
        // The inverse of hasParent is parentOf, written either way.
        assertEquals(set("hasParent-", "parentOf"), nodeNames(r.getEquivalentObjectProperties(p(df, "parentOf"))));
        assertEquals(set("hasParent-", "parentOf"), nodeNames(r.getInverseObjectProperties(p(df, "hasParent"))));
        assertEquals(set("hasParent", "parentOf-"), nodeNames(r.getInverseObjectProperties(p(df, "parentOf"))));
        // Equivalent property of a property that is its own node.
        assertEquals(set("hasGrandparent"), nodeNames(r.getEquivalentObjectProperties(p(df, "hasGrandparent"))));
        // Top and bottom.
        assertEquals(set("top"), nodeNames(r.getTopObjectPropertyNode()));
        assertEquals(set("bot"), nodeNames(r.getBottomObjectPropertyNode()));
    }

    @Test
    public void domainsAndRanges() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertEquals(set("[Person]"), classNodes(r.getObjectPropertyDomains(p(df, "hasParent"), true)));
        assertEquals(set("[Person]", "[Thing]"), classNodes(r.getObjectPropertyDomains(p(df, "hasParent"), false)));
        assertEquals(set("[Adult]"), classNodes(r.getObjectPropertyRanges(p(df, "hasParent"), true)));
        assertEquals(set("[Adult]", "[Person]", "[Thing]"),
                classNodes(r.getObjectPropertyRanges(p(df, "hasParent"), false)));
        // hasMother inherits both from hasParent.
        assertEquals(set("[Person]"), classNodes(r.getObjectPropertyDomains(p(df, "hasMother"), true)));
        assertEquals(set("[Adult]"), classNodes(r.getObjectPropertyRanges(p(df, "hasMother"), true)));
        // Domain of the inverse is the range.
        assertEquals(set("[Adult]"), classNodes(r.getObjectPropertyDomains(
                df.getOWLObjectInverseOf(p(df, "hasParent")), true)));
        assertEquals(set("[Person]"), classNodes(r.getObjectPropertyRanges(
                df.getOWLObjectInverseOf(p(df, "hasParent")), true)));
        // parentOf is the inverse of hasParent, so its domain is Adult.
        assertEquals(set("[Adult]"), classNodes(r.getObjectPropertyDomains(p(df, "parentOf"), true)));
        // No domain declared: owl:Thing only.
        assertEquals(set("[Thing]"), classNodes(r.getObjectPropertyDomains(p(df, "ancestorOf"), true)));
    }

    @Test
    public void inferredInversesSymmetryAndEquivalence() throws Exception {
        OWLOntology o = IndividualsTest.parse(INVERSES);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertEquals(set("a", "b-", "x-"), nodeNames(r.getEquivalentObjectProperties(p(df, "a"))));
        assertEquals(set("a-", "b", "x"), nodeNames(r.getEquivalentObjectProperties(p(df, "b"))));
        assertEquals(set("a", "b-", "x-"), nodeNames(r.getInverseObjectProperties(p(df, "b"))));
        assertEquals(set("a-", "b", "x"), nodeNames(r.getInverseObjectProperties(p(df, "a"))));
        assertEquals(set("sym", "sym-"), nodeNames(r.getEquivalentObjectProperties(p(df, "sym"))));
        assertEquals(set("sym", "sym-"), nodeNames(r.getInverseObjectProperties(p(df, "sym"))));
        assertEquals(set("selfInv", "selfInv-", "y", "y-"), nodeNames(r.getEquivalentObjectProperties(p(df, "selfInv"))));
        assertEquals(set("c", "d"), nodeNames(r.getEquivalentObjectProperties(p(df, "c"))));
        assertEquals(set("c-", "d-"), nodeNames(r.getEquivalentObjectProperties(p(df, "c").getInverseProperty())));
        // Domain and range of b come from a (b = a inverse).
        assertEquals(set("[B]"), classNodes(r.getObjectPropertyDomains(p(df, "b"), true)));
        assertEquals(set("[A]"), classNodes(r.getObjectPropertyRanges(p(df, "b"), true)));
    }

    @Test
    public void emptyProperty() throws Exception {
        OWLOntology o = IndividualsTest.parse(EMPTY);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        // No inverse role in this ontology, so HermiT's hierarchy holds the named properties only.
        assertEquals(set("bot", "e", "f", "g"), nodeNames(r.getBottomObjectPropertyNode()));
        assertEquals(set("bot", "e", "f", "g"), nodeNames(r.getEquivalentObjectProperties(p(df, "g"))));
        // An empty property has every class as domain; the most specific one is owl:Nothing.
        assertEquals(set("[Nothing]"), classNodes(r.getObjectPropertyDomains(p(df, "e"), true)));
        assertTrue(classNodes(r.getObjectPropertyRanges(p(df, "e"), false)).containsAll(set("[A]", "[B]", "[Thing]")));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(p(df, "e"), c(df, "A"))));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "e"), p(df, "g"))));
    }

    @Test
    public void universalProperty() throws Exception {
        OWLOntology o = IndividualsTest.parse(UNIVERSAL);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        Set<String> top = nodeNames(r.getTopObjectPropertyNode());
        assertTrue(top.toString(), top.containsAll(set("top", "u", "v")));
        assertEquals(top, nodeNames(r.getEquivalentObjectProperties(p(df, "u"))));
        // w holds for the one individual or for none; a domain A does not decide it.
        assertFalse(top.contains("w"));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "w"), p(df, "u"))));
        assertFalse(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "u"), p(df, "w"))));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "u"), p(df, "v"))));
        assertTrue(r.isEntailed(df.getOWLSymmetricObjectPropertyAxiom(p(df, "u"))));
    }

    @Test
    public void inverseExpressionsAreNodesOfTheirOwnWithoutInverseRoles() throws Exception {
        OWLOntology o = IndividualsTest.parse(PLAIN);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertEquals(set("[q]"), nodes(r.getSuperObjectProperties(p(df, "p"), true)));
        assertEquals(set("[q]", "[s]", "[top]"), nodes(r.getSuperObjectProperties(p(df, "p"), false)));
        // HermiT: an inverse expression is outside the role hierarchy when no inverse role exists.
        assertEquals(set("p-"), nodeNames(r.getEquivalentObjectProperties(p(df, "p").getInverseProperty())));
        assertEquals(set("[top]"), nodes(r.getSuperObjectProperties(p(df, "p").getInverseProperty(), false)));
        assertEquals(set("[bot]"), nodes(r.getSubObjectProperties(p(df, "p").getInverseProperty(), false)));
        assertEquals(set("p-"), nodeNames(r.getInverseObjectProperties(p(df, "p"))));
    }

    @Test
    public void freshPropertySitsBetweenTopAndBottom() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        OWLObjectProperty fresh = p(df, "neverDeclared");
        assertEquals(set("neverDeclared"), nodeNames(r.getEquivalentObjectProperties(fresh)));
        assertEquals(set("[top]"), nodes(r.getSuperObjectProperties(fresh, false)));
        assertEquals(set("[bot]"), nodes(r.getSubObjectProperties(fresh, true)));
        assertEquals(set("[Thing]"), classNodes(r.getObjectPropertyDomains(fresh, true)));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(fresh, fresh)));
        assertFalse(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(fresh, p(df, "hasParent"))));
        assertFalse(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "hasParent"), fresh)));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(fresh, df.getOWLTopObjectProperty())));
    }

    @Test
    public void entailmentChecks() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        OWLObjectProperty hasMother = p(df, "hasMother"), hasParent = p(df, "hasParent");
        OWLObjectProperty parentOf = p(df, "parentOf"), ancestorOf = p(df, "ancestorOf");
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(hasMother, hasParent)));
        assertFalse(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(hasParent, hasMother)));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(hasMother, df.getOWLObjectInverseOf(parentOf))));
        assertTrue(r.isEntailed(df.getOWLInverseObjectPropertiesAxiom(hasParent, parentOf)));
        assertTrue(r.isEntailed(df.getOWLInverseObjectPropertiesAxiom(parentOf, hasParent)));
        assertFalse(r.isEntailed(df.getOWLInverseObjectPropertiesAxiom(hasMother, parentOf)));
        assertTrue(r.isEntailed(df.getOWLEquivalentObjectPropertiesAxiom(
                parentOf, df.getOWLObjectInverseOf(hasParent))));
        assertFalse(r.isEntailed(df.getOWLEquivalentObjectPropertiesAxiom(parentOf, ancestorOf)));
        assertFalse(r.isEntailed(df.getOWLSymmetricObjectPropertyAxiom(hasParent)));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(hasParent, c(df, "Person"))));
        assertFalse(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(hasParent, c(df, "Adult"))));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyRangeAxiom(hasParent, c(df, "Adult"))));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyRangeAxiom(hasParent, c(df, "Person"))));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(parentOf, c(df, "Adult"))));
        assertTrue(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(hasParent, df.getOWLThing())));
        // Chains are answered by refutation with fresh individuals.
        assertTrue(r.isEntailmentCheckingSupported(AxiomType.SUB_PROPERTY_CHAIN_OF));
        assertTrue(r.isEntailmentCheckingSupported(AxiomType.SUB_OBJECT_PROPERTY));
        assertTrue(r.isEntailmentCheckingSupported(AxiomType.OBJECT_PROPERTY_RANGE));
        // A domain with a class expression: ∃r.⊤ ⊓ ¬C unsatisfiable.
        assertTrue(r.isEntailed(df.getOWLObjectPropertyDomainAxiom(hasParent,
                df.getOWLObjectSomeValuesFrom(hasParent, df.getOWLThing()))));
    }

    @Test
    public void symmetryIsEntailedWhenSubPropertyOfItsInverse() throws Exception {
        OWLOntology o = IndividualsTest.parse(INVERSES);
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertTrue(r.isEntailed(df.getOWLSymmetricObjectPropertyAxiom(p(df, "sym"))));
        assertTrue(r.isEntailed(df.getOWLSymmetricObjectPropertyAxiom(p(df, "selfInv"))));
        assertFalse(r.isEntailed(df.getOWLSymmetricObjectPropertyAxiom(p(df, "a"))));
    }

    @Test
    public void propertyRunIsLazyCachedAndInvalidatedByFlush() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        OWLDataFactory df = factory(o);
        KMReasoner r = km(o);
        // Class and individual queries never run the property classification.
        r.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS,
                InferenceType.SAME_INDIVIDUAL);
        r.getSubClasses(c(df, "Person"), false);
        r.getTypes(df.getOWLNamedIndividual(IRI.create(NS + "x")), false);
        assertEquals(0, r.propertyRunCount());
        assertFalse(r.isPrecomputed(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        assertTrue(r.getPrecomputableInferenceTypes().contains(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        r.getSuperObjectProperties(p(df, "hasMother"), true);
        assertEquals(1, r.propertyRunCount());
        assertTrue(r.isPrecomputed(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        r.getEquivalentObjectProperties(p(df, "hasParent"));
        r.getObjectPropertyDomains(p(df, "hasParent"), true);
        r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "hasMother"), p(df, "hasParent")));
        r.precomputeInferences(InferenceType.OBJECT_PROPERTY_HIERARCHY);
        assertEquals("one run per committed revision", 1, r.propertyRunCount());
        // A change is invisible until flush, and a flush drops the cache.
        o.getOWLOntologyManager().addAxiom(o, df.getOWLSubObjectPropertyOfAxiom(p(df, "hasGrandparent"), p(df, "ancestorOf")));
        assertEquals(1, r.propertyRunCount());
        assertEquals(set("[top]"), nodes(r.getSuperObjectProperties(p(df, "hasGrandparent"), true)));
        r.flush();
        assertFalse(r.isPrecomputed(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        assertEquals(set("[ancestorOf, descendantOf-]"), nodes(r.getSuperObjectProperties(p(df, "hasGrandparent"), true)));
        assertEquals(2, r.propertyRunCount());
    }

    @Test
    public void precomputeRunsOnlyWhenAsked() throws Exception {
        OWLOntology o = IndividualsTest.parse(CHAIN);
        KMReasoner r = km(o);
        r.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        assertEquals(0, r.propertyRunCount());
        r.precomputeInferences(InferenceType.OBJECT_PROPERTY_HIERARCHY);
        assertTrue(r.isPrecomputed(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        assertEquals("lazy precompute defers the native run until the first property query", 0, r.propertyRunCount());
        r.getTopObjectPropertyNode();
        assertEquals(1, r.propertyRunCount());
    }

    @Test
    public void ontologyWithoutObjectPropertiesNeedsNoRun() throws Exception {
        OWLOntology o = IndividualsTest.parse(HEAD + "Ontology(<http://example.org/noprop>\n"
                + "Declaration(Class(:A)) Declaration(Class(:B)) SubClassOf(:A :B))\n");
        KMReasoner r = km(o);
        assertEquals(set("top"), nodeNames(r.getTopObjectPropertyNode()));
        assertEquals(set("bot"), nodeNames(r.getBottomObjectPropertyNode()));
        assertEquals(0, r.propertyRunCount());
    }

    @Test
    public void inconsistentOntologyThrowsLikeHermit() throws Exception {
        OWLOntology o = IndividualsTest.parse(HEAD + "Ontology(<http://example.org/incons>\n"
                + "Declaration(ObjectProperty(:p)) Declaration(Class(:A))\n"
                + "SubClassOf(:A owl:Nothing) ClassAssertion(:A :x))\n");
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertFalse(r.isConsistent());
        try {
            r.getSuperObjectProperties(p(df, "p"), true);
            fail("expected InconsistentOntologyException");
        } catch (InconsistentOntologyException expected) {
            // as HermiT
        }
        try {
            r.getTopObjectPropertyNode();
            fail("expected InconsistentOntologyException");
        } catch (InconsistentOntologyException expected) {
            // as HermiT
        }
    }

    @Test
    public void subObjectPropertyWithInverseSubProperty() throws Exception {
        OWLOntology o = IndividualsTest.parse(HEAD + "Ontology(<http://example.org/inv-sub>\n"
                + "Declaration(Class(:A)) Declaration(Class(:B))\n"
                + "Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s))\n"
                + "SubObjectPropertyOf(ObjectInverseOf(:r) :s)\n"
                + "SubClassOf(:A ObjectSomeValuesFrom(ObjectInverseOf(:r) :B))\n"
                + ")\n");
        OWLDataFactory df = factory(o);
        OWLReasoner r = km(o);
        assertEquals(set("[s-]"), nodes(r.getSuperObjectProperties(p(df, "r"), true)));
        assertEquals(set("[s]"), nodes(r.getSuperObjectProperties(p(df, "r").getInverseProperty(), true)));
        assertTrue(r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p(df, "r").getInverseProperty(), p(df, "s"))));
        assertTrue(r.isEntailed(df.getOWLSubClassOfAxiom(c(df, "A"),
                df.getOWLObjectSomeValuesFrom(p(df, "s"), c(df, "B")))));
    }
}
