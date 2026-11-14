package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

import static org.junit.Assert.*;

/**
 * HermiT's conventions for owl:Thing, owl:Nothing and the top and bottom
 * properties, the queries the plugin refuses instead of answering empty, the
 * data property hierarchy, the cached failure and the convention methods.
 * The expectation is HermiT's answer on the same ontology wherever HermiT is
 * right; where it is wrong the test states the correct answer.
 */
public class ConventionsTest {

    static final String NS = "http://example.org/conv#";
    private static final String HEAD = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n";

    /** A taxonomy with an equivalence, a disjointness, a deep chain and an unsatisfiable class. */
    static final String CLASSES = HEAD + "Ontology(<http://example.org/conv-classes>\n"
            + "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n"
            + "Declaration(Class(:E)) Declaration(Class(:U)) Declaration(Class(:V))\n"
            + "SubClassOf(:B :A) SubClassOf(:C :A) SubClassOf(:D :B) EquivalentClasses(:A :E)\n"
            + "DisjointClasses(:B :C)\n"
            + "SubClassOf(:U owl:Nothing) SubClassOf(:V :U)\n"
            + ")\n";

    /** Nothing but owl:Thing and owl:Nothing. */
    static final String BARE = HEAD + "Ontology(<http://example.org/conv-bare>\n"
            + "Declaration(NamedIndividual(:i))\n)\n";

    static final String PROPERTIES = HEAD + "Ontology(<http://example.org/conv-props>\n"
            + "Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:e))\n"
            + "SubObjectPropertyOf(:p :q)\n"
            + "SubObjectPropertyOf(:e owl:bottomObjectProperty)\n"
            + ")\n";

    /** Inside the fragment of DataPropertyModel. */
    static final String DATA = HEAD + "Ontology(<http://example.org/conv-data>\n"
            + "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:U))\n"
            + "SubClassOf(:B :A) SubClassOf(:U owl:Nothing)\n"
            + "Declaration(DataProperty(:p)) Declaration(DataProperty(:q)) Declaration(DataProperty(:r))\n"
            + "Declaration(DataProperty(:s)) Declaration(DataProperty(:t)) Declaration(DataProperty(:z))\n"
            + "Declaration(DataProperty(:y)) Declaration(DataProperty(:leaf))\n"
            + "SubDataPropertyOf(:p :q)\n"
            + "SubDataPropertyOf(:s :t) SubDataPropertyOf(:t :s) EquivalentDataProperties(:r :t)\n"
            + "DataPropertyDomain(:p :B) DataPropertyDomain(:q :A)\n"
            + "DataPropertyRange(:p xsd:string) FunctionalDataProperty(:q)\n"
            + "SubDataPropertyOf(:z owl:bottomDataProperty)\n"
            + "DataPropertyDomain(:y :U)\n"
            + "SubDataPropertyOf(:leaf :p)\n"
            + "ClassAssertion(:B :i) DataPropertyAssertion(:q :i \"x\")\n"
            + ")\n";

    /** A class axiom mentions a data property: outside the fragment. */
    static final String DATA_OUTSIDE = HEAD + "Ontology(<http://example.org/conv-data-out>\n"
            + "Declaration(Class(:A)) Declaration(DataProperty(:p)) Declaration(DataProperty(:q))\n"
            + "SubDataPropertyOf(:p :q)\n"
            + "SubClassOf(:A DataSomeValuesFrom(:p rdfs:Literal))\n"
            + ")\n";

    /** Two domains that are disjoint classes: the intersection is empty, which the taxonomy cannot show for a property. */
    static final String DATA_DOMAINS = HEAD + "Ontology(<http://example.org/conv-data-dom>\n"
            + "Declaration(Class(:B)) Declaration(Class(:C)) Declaration(DataProperty(:p))\n"
            + "DisjointClasses(:B :C) DataPropertyDomain(:p :B) DataPropertyDomain(:p :C)\n"
            + ")\n";

    static final String DATA_RANGES = HEAD + "Ontology(<http://example.org/conv-data-ran>\n"
            + "Declaration(DataProperty(:p)) DataPropertyRange(:p xsd:string) DataPropertyRange(:p xsd:integer)\n"
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

    private KMReasoner km(OWLOntology o) {
        KMReasoner r = (KMReasoner) new KMReasonerFactory().createReasoner(o);
        open.add(r);
        return r;
    }

    private OWLReasoner hermit(OWLOntology o) {
        org.semanticweb.HermiT.Configuration c = new org.semanticweb.HermiT.Configuration();
        c.ignoreUnsupportedDatatypes = true;
        OWLReasoner r = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o, c);
        open.add(r);
        return r;
    }

    private static OWLDataFactory df(OWLOntology o) { return o.getOWLOntologyManager().getOWLDataFactory(); }
    private static OWLClass cls(OWLDataFactory df, String f) { return df.getOWLClass(IRI.create(NS + f)); }
    private static OWLDataProperty dp(OWLDataFactory df, String f) { return df.getOWLDataProperty(IRI.create(NS + f)); }
    private static OWLObjectProperty op(OWLDataFactory df, String f) { return df.getOWLObjectProperty(IRI.create(NS + f)); }

    private static String name(OWLEntity e) {
        if (e.getIRI().toString().startsWith("http://www.w3.org/2002/07/owl#")) return "owl:" + e.getIRI().getShortForm();
        return e.getIRI().getShortForm();
    }

    private static String expressionName(OWLObjectPropertyExpression e) {
        return e.isAnonymous() ? "inv(" + name((OWLEntity) e.getNamedProperty()) + ")" : name((OWLEntity) e.asOWLObjectProperty());
    }

    static Set<String> nodes(NodeSet<? extends OWLObject> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<? extends OWLObject> n : ns.getNodes()) out.add(node(n));
        return out;
    }

    static String node(Node<? extends OWLObject> n) {
        List<String> one = new ArrayList<>();
        for (OWLObject e : n.getEntities()) {
            one.add(e instanceof OWLEntity ? name((OWLEntity) e) : expressionName((OWLObjectPropertyExpression) e));
        }
        Collections.sort(one);
        return one.toString();
    }

    // ---- item 1: owl:Thing and owl:Nothing in the class hierarchy -------

    @Test
    public void classHierarchyAgreesWithHermitOnEveryNamedClassAndTheTopAndBottom() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLDataFactory df = df(o);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<OWLClass> classes = new ArrayList<>(Arrays.asList(df.getOWLThing(), df.getOWLNothing()));
        for (String n : new String[]{"A", "B", "C", "D", "E", "U", "V", "NotInTheSignature"}) classes.add(cls(df, n));
        for (OWLClass c : classes) {
            for (boolean direct : new boolean[]{true, false}) {
                assertEquals("getSuperClasses(" + c + "," + direct + ")",
                        nodes(h.getSuperClasses(c, direct)), nodes(k.getSuperClasses(c, direct)));
                assertEquals("getSubClasses(" + c + "," + direct + ")",
                        nodes(h.getSubClasses(c, direct)), nodes(k.getSubClasses(c, direct)));
            }
            assertEquals("getEquivalentClasses(" + c + ")",
                    node(h.getEquivalentClasses(c)), node(k.getEquivalentClasses(c)));
        }
        assertEquals(node(h.getTopClassNode()), node(k.getTopClassNode()));
        assertEquals(node(h.getBottomClassNode()), node(k.getBottomClassNode()));
        assertEquals(node(h.getUnsatisfiableClasses()), node(k.getUnsatisfiableClasses()));
    }

    @Test
    public void nothingIsAStrictSubclassAndBelowTheLeaves() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        // The unsatisfiable classes sit in the bottom node.
        assertEquals("[V, U, owl:Nothing]".length(), node(k.getBottomClassNode()).length());
        assertTrue(k.getBottomClassNode().contains(cls(df, "U")));
        assertTrue(k.getBottomClassNode().contains(cls(df, "V")));
        // A leaf: the bottom node is its direct subclass.
        assertEquals(Collections.singleton(node(k.getBottomClassNode())), nodes(k.getSubClasses(cls(df, "D"), true)));
        assertEquals(Collections.singleton(node(k.getBottomClassNode())), nodes(k.getSubClasses(cls(df, "C"), true)));
        // A class with sub classes has the bottom node only in the non-direct answer.
        assertFalse(k.getSubClasses(cls(df, "B"), true).containsEntity(df.getOWLNothing()));
        assertTrue(k.getSubClasses(cls(df, "B"), false).containsEntity(df.getOWLNothing()));
        // owl:Thing has other direct subclasses, so the bottom node is not among them.
        assertFalse(k.getSubClasses(df.getOWLThing(), true).containsEntity(df.getOWLNothing()));
        assertTrue(k.getSubClasses(df.getOWLThing(), false).containsEntity(df.getOWLNothing()));
        // The super classes of owl:Nothing: every other class; the direct ones are the leaves.
        assertEquals(new TreeSet<>(Arrays.asList("[C]", "[D]")), nodes(k.getSuperClasses(df.getOWLNothing(), true)));
        assertEquals(new TreeSet<>(Arrays.asList("[A, E]", "[B]", "[C]", "[D]", "[owl:Thing]")),
                nodes(k.getSuperClasses(df.getOWLNothing(), false)));
        // An unsatisfiable class is in the bottom node and answers like owl:Nothing.
        assertEquals(nodes(k.getSuperClasses(df.getOWLNothing(), false)),
                nodes(k.getSuperClasses(cls(df, "V"), false)));
        assertTrue(k.getSubClasses(cls(df, "U"), false).isEmpty());
    }

    @Test
    public void anOntologyWithoutClassesPutsNothingDirectlyBelowThing() throws Exception {
        OWLOntology o = IndividualsTest.parse(BARE);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        OWLReasoner h = hermit(o);
        assertEquals(nodes(h.getSubClasses(df.getOWLThing(), true)), nodes(k.getSubClasses(df.getOWLThing(), true)));
        assertEquals(Collections.singleton("[owl:Nothing]"), nodes(k.getSubClasses(df.getOWLThing(), true)));
        assertEquals(Collections.singleton("[owl:Thing]"), nodes(k.getSuperClasses(df.getOWLNothing(), true)));
    }

    @Test
    public void disjointClassesOfThingAndNothingAreDecidedAndTheRestRefuses() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLDataFactory df = df(o);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        for (OWLClass c : new OWLClass[]{df.getOWLThing(), df.getOWLNothing(), cls(df, "U"), cls(df, "NotInTheSignature")}) {
            assertEquals("getDisjointClasses(" + c + ")", nodes(h.getDisjointClasses(c)), nodes(k.getDisjointClasses(c)));
        }
        // B and C are disjoint, but the taxonomy does not hold that: no answer rather than a wrong one.
        for (String n : new String[]{"A", "B", "C", "D"}) {
            try {
                k.getDisjointClasses(cls(df, n));
                fail("getDisjointClasses(" + n + ") must not answer");
            } catch (UnsupportedOperationException expected) {
                assertTrue(expected.getMessage(), expected.getMessage().contains("getDisjointClasses"));
            }
        }
    }

    // ---- item 1: properties ---------------------------------------------------

    @Test
    public void objectPropertyConventionsAgreeWithHermit() throws Exception {
        OWLOntology o = IndividualsTest.parse(PROPERTIES);
        OWLDataFactory df = df(o);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<OWLObjectPropertyExpression> props = new ArrayList<>(Arrays.asList(df.getOWLTopObjectProperty(),
                df.getOWLBottomObjectProperty(), op(df, "p"), op(df, "q"), op(df, "e"), op(df, "fresh")));
        for (OWLObjectPropertyExpression p : props) {
            for (boolean direct : new boolean[]{true, false}) {
                assertEquals("sub " + p + " " + direct, nodes(h.getSubObjectProperties(p, direct)), nodes(k.getSubObjectProperties(p, direct)));
                assertEquals("super " + p + " " + direct, nodes(h.getSuperObjectProperties(p, direct)), nodes(k.getSuperObjectProperties(p, direct)));
            }
            assertEquals(node(h.getEquivalentObjectProperties(p)), node(k.getEquivalentObjectProperties(p)));
        }
        assertEquals(node(h.getTopObjectPropertyNode()), node(k.getTopObjectPropertyNode()));
        assertEquals(node(h.getBottomObjectPropertyNode()), node(k.getBottomObjectPropertyNode()));
        // Disjointness with the top, the bottom, an empty and a fresh property is decided.
        for (OWLObjectPropertyExpression p : new OWLObjectPropertyExpression[]{df.getOWLTopObjectProperty(),
                df.getOWLBottomObjectProperty(), op(df, "fresh")}) {
            assertEquals("disjoint " + p, nodes(h.getDisjointObjectProperties(p)), nodes(k.getDisjointObjectProperties(p)));
        }
        // An empty property other than owl:bottomObjectProperty: HermiT omits the top property, which
        // is disjoint with it (the intersection is empty); KM lists every node.
        Set<String> expected = new TreeSet<>(nodes(h.getDisjointObjectProperties(op(df, "e"))));
        assertFalse(expected.contains("[owl:topObjectProperty]"));
        expected.add("[owl:topObjectProperty]");
        assertEquals(expected, nodes(k.getDisjointObjectProperties(op(df, "e"))));
        assertEquals(nodes(k.getDisjointObjectProperties(df.getOWLBottomObjectProperty())),
                nodes(k.getDisjointObjectProperties(op(df, "e"))));
        for (String n : new String[]{"p", "q"}) {
            try {
                k.getDisjointObjectProperties(op(df, n));
                fail("getDisjointObjectProperties(" + n + ") must not answer");
            } catch (UnsupportedOperationException refused) {
                // the answer needs the domains, ranges and disjointness axioms
            }
        }
    }

    @Test
    public void theBottomPropertyHasEveryClassAsDomainAndRange() throws Exception {
        // HermiT answers {owl:Thing} (direct) and the empty set (non-direct) here; both are wrong:
        // the bottom property has no pair, so every class is a domain and a range.
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        OWLObjectProperty bottom = df.getOWLBottomObjectProperty();
        assertEquals(Collections.singleton(node(k.getBottomClassNode())), nodes(k.getObjectPropertyDomains(bottom, true)));
        assertEquals(Collections.singleton(node(k.getBottomClassNode())), nodes(k.getObjectPropertyRanges(bottom, true)));
        Set<String> all = nodes(k.getObjectPropertyDomains(bottom, false));
        assertTrue(all.contains("[owl:Thing]"));
        assertTrue(all.contains("[D]"));
        assertTrue(all.contains(node(k.getBottomClassNode())));
        assertEquals(all, nodes(k.getObjectPropertyRanges(bottom, false)));
        assertEquals(Collections.singleton("[owl:Thing]"), nodes(k.getObjectPropertyDomains(df.getOWLTopObjectProperty(), true)));
        assertEquals(nodes(hermit(o).getObjectPropertyDomains(df.getOWLTopObjectProperty(), false)),
                nodes(k.getObjectPropertyDomains(df.getOWLTopObjectProperty(), false)));
    }

    // ---- item 1: data properties -----------------------------------------------

    @Test
    public void dataPropertyHierarchyAgreesWithHermitInsideTheFragment() throws Exception {
        OWLOntology o = IndividualsTest.parse(DATA);
        OWLDataFactory df = df(o);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<OWLDataProperty> props = new ArrayList<>(Arrays.asList(df.getOWLTopDataProperty(), df.getOWLBottomDataProperty()));
        for (String n : new String[]{"p", "q", "r", "s", "t", "z", "y", "leaf", "fresh"}) props.add(dp(df, n));
        for (OWLDataProperty p : props) {
            for (boolean direct : new boolean[]{true, false}) {
                assertEquals("sub " + p + " " + direct, nodes(h.getSubDataProperties(p, direct)), nodes(k.getSubDataProperties(p, direct)));
                assertEquals("super " + p + " " + direct, nodes(h.getSuperDataProperties(p, direct)), nodes(k.getSuperDataProperties(p, direct)));
                if (!p.isOWLBottomDataProperty()) {
                    assertEquals("domain " + p + " " + direct, nodes(h.getDataPropertyDomains(p, direct)), nodes(k.getDataPropertyDomains(p, direct)));
                }
            }
            assertEquals("equivalent " + p, node(h.getEquivalentDataProperties(p)), node(k.getEquivalentDataProperties(p)));
        }
        assertEquals(node(h.getTopDataPropertyNode()), node(k.getTopDataPropertyNode()));
        assertEquals(node(h.getBottomDataPropertyNode()), node(k.getBottomDataPropertyNode()));
        for (OWLDataProperty p : new OWLDataProperty[]{df.getOWLTopDataProperty(), df.getOWLBottomDataProperty(),
                dp(df, "fresh")}) {
            assertEquals("disjoint " + p, nodes(h.getDisjointDataProperties(p)), nodes(k.getDisjointDataProperties(p)));
        }
        // Empty properties other than owl:bottomDataProperty: HermiT omits the top property, which is
        // disjoint with them; KM lists every node, as it does for owl:bottomDataProperty.
        for (String empty : new String[]{"z", "y"}) {
            Set<String> expected = new TreeSet<>(nodes(h.getDisjointDataProperties(dp(df, empty))));
            assertFalse(expected.contains("[owl:topDataProperty]"));
            expected.add("[owl:topDataProperty]");
            assertEquals(expected, nodes(k.getDisjointDataProperties(dp(df, empty))));
        }
        // Spot checks of the shape: s, t, r are one node; z and y (empty domain class) are in the bottom node.
        assertEquals("[r, s, t]", node(k.getEquivalentDataProperties(dp(df, "s"))));
        assertTrue(k.getBottomDataPropertyNode().contains(dp(df, "z")));
        assertTrue("an unsatisfiable domain makes the property empty", k.getBottomDataPropertyNode().contains(dp(df, "y")));
        assertEquals(Collections.singleton("[B]"), nodes(k.getDataPropertyDomains(dp(df, "p"), true)));
        assertEquals(new TreeSet<>(Arrays.asList("[A]", "[B]", "[owl:Thing]")), nodes(k.getDataPropertyDomains(dp(df, "p"), false)));
        assertEquals(Collections.singleton("[A]"), nodes(k.getDataPropertyDomains(dp(df, "q"), true)));
    }

    @Test
    public void theBottomDataPropertyHasEveryClassAsDomain() throws Exception {
        // HermiT answers {owl:Thing}; the bottom property has no pair, so every class is a domain.
        OWLOntology o = IndividualsTest.parse(DATA);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        assertEquals(Collections.singleton(node(k.getBottomClassNode())),
                nodes(k.getDataPropertyDomains(df.getOWLBottomDataProperty(), true)));
        Set<String> all = nodes(k.getDataPropertyDomains(df.getOWLBottomDataProperty(), false));
        assertTrue(all.contains("[owl:Thing]") && all.contains("[A]") && all.contains("[C]"));
        assertTrue(all.contains(node(k.getBottomClassNode())));
        // A property with an unsatisfiable domain is empty too.
        assertEquals(all, nodes(k.getDataPropertyDomains(dp(df, "y"), false)));
        assertEquals(Collections.singleton("[owl:Thing]"), nodes(k.getDataPropertyDomains(df.getOWLTopDataProperty(), true)));
    }

    @Test
    public void theDataPropertyHierarchyRefusesOutsideItsFragment() throws Exception {
        for (String source : new String[]{DATA_OUTSIDE, DATA_DOMAINS, DATA_RANGES}) {
            OWLOntology o = IndividualsTest.parse(source);
            OWLDataFactory df = df(o);
            KMReasoner k = km(o);
            OWLDataProperty p = dp(df, "p");
            List<Query> queries = Arrays.<Query>asList(
                    r -> r.getSubDataProperties(p, true), r -> r.getSuperDataProperties(p, false),
                    r -> r.getEquivalentDataProperties(p), r -> r.getDataPropertyDomains(p, true),
                    r -> r.getTopDataPropertyNode(), r -> r.getBottomDataPropertyNode(),
                    r -> r.getDisjointDataProperties(p));
            for (Query q : queries) {
                try {
                    q.run(k);
                    fail("a data property query outside the fragment must not answer: " + source);
                } catch (UnsupportedOperationException expected) {
                    // refused
                }
            }
            assertFalse(k.getPrecomputableInferenceTypes().contains(InferenceType.DATA_PROPERTY_HIERARCHY)
                    && source == DATA_OUTSIDE);
            k.precomputeInferences(InferenceType.DATA_PROPERTY_HIERARCHY); // ignored, no exception
            assertFalse(k.isPrecomputed(InferenceType.DATA_PROPERTY_HIERARCHY));
        }
    }

    @Test
    public void theDataPropertyHierarchyIsListedAndPrecomputedInsideTheFragment() throws Exception {
        OWLOntology o = IndividualsTest.parse(DATA);
        KMReasoner k = km(o);
        assertTrue(k.getPrecomputableInferenceTypes().contains(InferenceType.DATA_PROPERTY_HIERARCHY));
        assertFalse(k.isPrecomputed(InferenceType.DATA_PROPERTY_HIERARCHY));
        k.precomputeInferences(InferenceType.DATA_PROPERTY_HIERARCHY);
        assertTrue(k.isPrecomputed(InferenceType.DATA_PROPERTY_HIERARCHY));
        // Property assertions are not computed, so they are not offered.
        assertFalse(k.getPrecomputableInferenceTypes().contains(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
        assertFalse(k.getPrecomputableInferenceTypes().contains(InferenceType.DATA_PROPERTY_ASSERTIONS));
        assertFalse(k.isPrecomputed(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
        k.precomputeInferences(InferenceType.OBJECT_PROPERTY_ASSERTIONS); // ignored
        assertFalse(k.isPrecomputed(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
    }

    @Test
    public void aDataPropertyHierarchyFollowsAnEditOfTheOntology() throws Exception {
        OWLOntology o = IndividualsTest.parse(DATA);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        assertEquals(Collections.singleton("[q]"), nodes(k.getSuperDataProperties(dp(df, "p"), true)));
        o.getOWLOntologyManager().addAxiom(o, df.getOWLSubDataPropertyOfAxiom(dp(df, "p"), dp(df, "r")));
        k.flush();
        assertEquals(new TreeSet<>(Arrays.asList("[q]", "[r, s, t]")), nodes(k.getSuperDataProperties(dp(df, "p"), true)));
        // A class axiom with a data property leaves the fragment.
        o.getOWLOntologyManager().addAxiom(o, df.getOWLSubClassOfAxiom(cls(df, "C"),
                df.getOWLDataSomeValuesFrom(dp(df, "p"), df.getTopDatatype())));
        k.flush();
        try {
            k.getSuperDataProperties(dp(df, "p"), true);
            fail();
        } catch (UnsupportedOperationException expected) {
            // refused after the edit
        }
    }

    // ---- item 2: nothing answers empty ----------------------------------------

    private interface Query { void run(OWLReasoner r) throws Exception; }

    @Test
    public void queriesThePluginDoesNotAnswerThrowInsteadOfReturningEmptyAnswers() throws Exception {
        String source = IndividualsTest.SMALL.replace("Declaration(NamedIndividual(:loner))",
                "Declaration(NamedIndividual(:loner)) Declaration(DataProperty(:age))"
                + " DataPropertyAssertion(:age :rex \"3\"^^xsd:integer)").replace("Prefix(owl:",
                "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\nPrefix(owl:");
        OWLOntology o = IndividualsTest.parse(source);
        OWLDataFactory df = df(o);
        KMReasoner k = km(o);
        OWLClass dog = df.getOWLClass(IRI.create(IndividualsTest.NS + "Dog"));
        OWLClassExpression anonymous = df.getOWLObjectIntersectionOf(dog,
                df.getOWLClass(IRI.create(IndividualsTest.NS + "Pet")));
        OWLNamedIndividual rex = df.getOWLNamedIndividual(IRI.create(IndividualsTest.NS + "rex"));
        OWLObjectProperty owned = df.getOWLObjectProperty(IRI.create(IndividualsTest.NS + "ownedBy"));
        OWLDataProperty age = df.getOWLDataProperty(IRI.create(IndividualsTest.NS + "age"));
        Map<String, Query> refused = new LinkedHashMap<>();
        refused.put("getObjectPropertyValues", r -> r.getObjectPropertyValues(rex, owned));
        refused.put("getObjectPropertyValues(inverse)", r -> r.getObjectPropertyValues(rex, owned.getInverseProperty()));
        refused.put("getDataPropertyValues", r -> r.getDataPropertyValues(rex, age));
        refused.put("getDifferentIndividuals", r -> r.getDifferentIndividuals(rex));
        refused.put("getDisjointClasses(Dog)", r -> r.getDisjointClasses(dog));
        refused.put("getDisjointClasses(anon)", r -> r.getDisjointClasses(anonymous));
        refused.put("getSuperClasses(anon,true)", r -> r.getSuperClasses(anonymous, true));
        refused.put("getSuperClasses(anon,false)", r -> r.getSuperClasses(anonymous, false));
        refused.put("getSubClasses(anon,true)", r -> r.getSubClasses(anonymous, true));
        refused.put("getSubClasses(anon,false)", r -> r.getSubClasses(anonymous, false));
        refused.put("getEquivalentClasses(anon)", r -> r.getEquivalentClasses(anonymous));
        refused.put("getInstances(anon)", r -> r.getInstances(anonymous, false));
        refused.put("getDisjointObjectProperties(ownedBy)", r -> r.getDisjointObjectProperties(owned));
        refused.put("getDisjointDataProperties(age)", r -> r.getDisjointDataProperties(age));
        for (Map.Entry<String, Query> e : refused.entrySet()) {
            try {
                e.getValue().run(k);
                fail(e.getKey() + " must throw, not answer");
            } catch (UnsupportedOperationException expected) {
                assertNotNull(e.getKey(), expected.getMessage());
            }
        }
        // isSatisfiable of an expression keeps the OWL API exception the interface declares.
        try {
            k.isSatisfiable(anonymous);
            fail();
        } catch (ClassExpressionNotInProfileException expected) {
            // refused
        }
        // What the taxonomy answers is still answered.
        assertTrue(k.getSuperClasses(dog, false).containsEntity(
                df.getOWLClass(IRI.create(IndividualsTest.NS + "Animal"))));
        assertEquals("[Dog]", node(k.getEquivalentClasses(dog)));
    }

    @Test
    public void entailmentOfNonLogicalAxiomsIsTrueAndIsCheckedForTheSameTypes() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLDataFactory df = df(o);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<OWLAxiom> axioms = Arrays.asList(
                df.getOWLDeclarationAxiom(cls(df, "NeverSeen")),
                df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(), cls(df, "A").getIRI(), df.getOWLLiteral("vin", "fr")),
                df.getOWLSubAnnotationPropertyOfAxiom(df.getRDFSLabel(), df.getRDFSComment()));
        for (OWLAxiom a : axioms) {
            assertEquals(a.toString(), h.isEntailed(a), k.isEntailed(a));
            assertTrue(a.toString(), k.isEntailed(a));
            assertTrue(a.getAxiomType().toString(), k.isEntailmentCheckingSupported(a.getAxiomType()));
        }
        // A logical type the plugin cannot check says so, and isEntailed agrees.
        OWLAxiom disjoint = df.getOWLDisjointClassesAxiom(cls(df, "B"), cls(df, "C"));
        assertFalse(k.isEntailmentCheckingSupported(disjoint.getAxiomType()));
        try {
            k.isEntailed(disjoint);
            fail();
        } catch (UnsupportedEntailmentTypeException expected) {
            // matches isEntailmentCheckingSupported
        }
        for (AxiomType<?> type : AxiomType.AXIOM_TYPES) {
            if (k.isEntailmentCheckingSupported(type)) continue;
            assertTrue(type.toString(), type.isLogical());
        }
    }

    // ---- item 3: a failed classification is remembered -----------------------

    private static Path stubKm(String body) throws Exception {
        Path dir = Files.createTempDirectory(Paths.get("target"), "stub-km");
        Path script = dir.resolve("km");
        Files.write(script, body.getBytes("UTF-8"));
        assertTrue(script.toFile().setExecutable(true));
        return script.toAbsolutePath();
    }

    private static int lines(Path log) throws Exception {
        return Files.exists(log) ? Files.readAllLines(log).size() : 0;
    }

    @Test
    public void aFailedClassificationIsRethrownWithoutANewRunUntilTheOntologyChangesOrFlushRuns() throws Exception {
        Path log = Files.createTempFile(Paths.get("target"), "stub-runs", ".log");
        Path stub = stubKm("#!/bin/sh\necho run >> '" + log.toAbsolutePath() + "'\necho refused >&2\nexit 3\n");
        String saved = System.getProperty("km.bin");
        System.setProperty("km.bin", stub.toString());
        try {
            OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
            OWLDataFactory df = df(o);
            KMReasoner k = km(o);
            RuntimeException first = null;
            try {
                k.getSuperClasses(cls(df, "Dog"), false);
                fail("the stub refuses");
            } catch (ReasonerInternalException expected) {
                first = expected;
            }
            assertEquals(1, lines(log));
            for (Query q : Arrays.<Query>asList(r -> r.isConsistent(), r -> r.getSubClasses(cls(df, "Dog"), true),
                    r -> r.getTopClassNode(), r -> r.getTypes(df.getOWLNamedIndividual(IRI.create(IndividualsTest.NS + "rex")), true),
                    r -> r.precomputeInferences(InferenceType.CLASS_HIERARCHY))) {
                try {
                    q.run(k);
                    fail();
                } catch (ReasonerInternalException again) {
                    assertSame("the stored failure", first, again);
                }
            }
            assertEquals("no new km run for the repeated calls", 1, lines(log));
            // flush() asks the reasoner to look again.
            k.flush();
            try {
                k.isConsistent();
                fail();
            } catch (ReasonerInternalException expected) {
                // refused again
            }
            assertEquals(2, lines(log));
            // So does a change of the ontology (buffered, picked up by the next call).
            o.getOWLOntologyManager().addAxiom(o, df.getOWLSubClassOfAxiom(cls(df, "Puppy"), cls(df, "Dog")));
            try {
                k.isConsistent();
                fail();
            } catch (ReasonerInternalException expected) {
                // refused again
            }
            assertEquals(3, lines(log));
            try {
                k.isConsistent();
                fail();
            } catch (ReasonerInternalException expected) {
                // remembered
            }
            assertEquals(3, lines(log));
        } finally {
            if (saved == null) System.clearProperty("km.bin"); else System.setProperty("km.bin", saved);
        }
    }

    @Test
    public void aFailedPropertyRunIsRememberedToo() throws Exception {
        Path log = Files.createTempFile(Paths.get("target"), "stub-runs", ".log");
        String real = System.getProperty("km.bin");
        Path stub = stubKm("#!/bin/sh\ncase \"$*\" in\n*--properties*) echo run >> '" + log.toAbsolutePath()
                + "'; echo refused >&2; exit 3;;\n*) exec '" + real + "' \"$@\";;\nesac\n");
        System.setProperty("km.bin", stub.toString());
        try {
            OWLOntology o = IndividualsTest.parse(PROPERTIES);
            OWLDataFactory df = df(o);
            KMReasoner k = km(o);
            assertTrue(k.isConsistent());
            RuntimeException first = null;
            try {
                k.getSubObjectProperties(op(df, "p"), false);
                fail();
            } catch (RuntimeException expected) {
                first = expected;
            }
            assertEquals(1, lines(log));
            try {
                k.getSuperObjectProperties(op(df, "p"), false);
                fail();
            } catch (RuntimeException again) {
                assertSame(first, again);
            }
            try {
                k.getObjectPropertyDomains(op(df, "p"), false);
                fail();
            } catch (RuntimeException again) {
                assertSame(first, again);
            }
            assertEquals("one run, not one per query", 1, lines(log));
            // The class hierarchy still answers.
            assertFalse(k.getSubClasses(df.getOWLThing(), false).isEmpty());
            k.flush();
            try {
                k.getSubObjectProperties(op(df, "p"), false);
                fail();
            } catch (RuntimeException expected) {
                // refused again
            }
            assertEquals(2, lines(log));
        } finally {
            System.setProperty("km.bin", real);
        }
    }

    // ---- item 4: convention methods ---------------------------------------------

    @Test
    public void timeOutAndPolicyFollowTheConfigurationLikeHermit() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLReasonerConfiguration config = new SimpleConfiguration(5000);
        OWLReasoner k = new KMReasonerFactory().createReasoner(o, config);
        open.add(k);
        OWLReasoner h = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o, config);
        open.add(h);
        assertEquals(5000L, k.getTimeOut());
        assertEquals(h.getTimeOut(), k.getTimeOut());
        assertEquals(h.getIndividualNodeSetPolicy(), k.getIndividualNodeSetPolicy());
        assertEquals(h.getFreshEntityPolicy(), k.getFreshEntityPolicy());
        OWLReasoner unconfigured = km(o);
        assertEquals(Long.MAX_VALUE, unconfigured.getTimeOut());
    }

    @Test
    public void unsupportedPrecomputationIsNotListedAndNotPretended() throws Exception {
        OWLOntology o = IndividualsTest.parse(CLASSES);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        Set<InferenceType> hermit = h.getPrecomputableInferenceTypes();
        Set<InferenceType> km = k.getPrecomputableInferenceTypes();
        assertTrue("KM lists only types HermiT lists", hermit.containsAll(km));
        assertTrue(km.contains(InferenceType.CLASS_HIERARCHY));
        assertFalse(km.contains(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
        for (InferenceType t : InferenceType.values()) assertFalse("not yet computed: " + t, k.isPrecomputed(t));
        k.precomputeInferences(km.toArray(new InferenceType[0]));
        for (InferenceType t : km) assertTrue("computed: " + t, k.isPrecomputed(t));
    }
}
