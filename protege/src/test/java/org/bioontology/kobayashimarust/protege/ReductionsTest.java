package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.*;

import java.util.*;

import static org.junit.Assert.*;

/**
 * The queries answered by reduction to a km run on an extended ontology
 * (class expressions, disjoint classes and properties, property values,
 * different individuals, isEntailed for every supported axiom type), compared
 * with HermiT on small ontologies that make each answer non-trivial.
 */
public class ReductionsTest {

    static final String NS = "http://example.org/red#";

    /** Classes, properties and an ABox where every reduced query has a non-empty answer. */
    static final String ZOO = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
            + "Ontology(<http://example.org/red>\n"
            + "Declaration(Class(:Animal)) Declaration(Class(:Mammal)) Declaration(Class(:Dog)) Declaration(Class(:Cat))\n"
            + "Declaration(Class(:Person)) Declaration(Class(:Pet)) Declaration(Class(:Plant)) Declaration(Class(:Herbivore))\n"
            + "Declaration(Class(:Carnivore)) Declaration(Class(:Owner)) Declaration(Class(:Lonely))\n"
            + "Declaration(ObjectProperty(:eats)) Declaration(ObjectProperty(:ownedBy)) Declaration(ObjectProperty(:owns))\n"
            + "Declaration(ObjectProperty(:partOf)) Declaration(ObjectProperty(:friend)) Declaration(ObjectProperty(:likes))\n"
            + "Declaration(ObjectProperty(:dislikes)) Declaration(ObjectProperty(:hasParent)) Declaration(ObjectProperty(:hasGrandparent))\n"
            + "Declaration(ObjectProperty(:spouse)) Declaration(ObjectProperty(:knows)) Declaration(ObjectProperty(:loves))\n"
            + "Declaration(NamedIndividual(:rex)) Declaration(NamedIndividual(:tom)) Declaration(NamedIndividual(:alice))\n"
            + "Declaration(NamedIndividual(:bob)) Declaration(NamedIndividual(:robert)) Declaration(NamedIndividual(:carl))\n"
            + "Declaration(NamedIndividual(:dora)) Declaration(NamedIndividual(:wheel)) Declaration(NamedIndividual(:car))\n"
            + "Declaration(NamedIndividual(:fleet)) Declaration(NamedIndividual(:fern))\n"
            + "SubClassOf(:Dog :Mammal) SubClassOf(:Cat :Mammal) SubClassOf(:Mammal :Animal)\n"
            + "DisjointClasses(:Animal :Plant) DisjointClasses(:Dog :Cat) DisjointClasses(:Person :Animal)\n"
            + "EquivalentClasses(:Pet ObjectIntersectionOf(:Animal ObjectSomeValuesFrom(:ownedBy :Person)))\n"
            + "EquivalentClasses(:Herbivore ObjectIntersectionOf(:Animal ObjectAllValuesFrom(:eats :Plant)))\n"
            + "EquivalentClasses(:Owner ObjectSomeValuesFrom(:owns :Animal))\n"
            + "SubClassOf(:Carnivore ObjectSomeValuesFrom(:eats :Animal))\n"
            + "SubClassOf(:Lonely ObjectAllValuesFrom(:friend owl:Nothing))\n"
            + "InverseObjectProperties(:owns :ownedBy)\n"
            + "TransitiveObjectProperty(:partOf) SymmetricObjectProperty(:friend)\n"
            + "DisjointObjectProperties(:likes :dislikes) SubObjectPropertyOf(:loves :likes)\n"
            + "ObjectPropertyDomain(:eats :Animal) ObjectPropertyRange(:ownedBy :Person)\n"
            + "FunctionalObjectProperty(:spouse) AsymmetricObjectProperty(:hasParent) ReflexiveObjectProperty(:knows)\n"
            + "SubObjectPropertyOf(ObjectPropertyChain(:hasParent :hasParent) :hasGrandparent)\n"
            + "ClassAssertion(:Dog :rex) ClassAssertion(:Cat :tom) ClassAssertion(:Person :alice) ClassAssertion(:Person :bob)\n"
            + "ClassAssertion(:Plant :fern) ClassAssertion(ObjectIntersectionOf(:Animal ObjectAllValuesFrom(:eats :Plant)) :rex)\n"
            + "ObjectPropertyAssertion(:ownedBy :rex :alice) ObjectPropertyAssertion(:owns :bob :tom)\n"
            + "ObjectPropertyAssertion(:partOf :wheel :car) ObjectPropertyAssertion(:partOf :car :fleet)\n"
            + "ObjectPropertyAssertion(:friend :alice :bob) ObjectPropertyAssertion(:loves :carl :alice)\n"
            + "ObjectPropertyAssertion(:hasParent :carl :alice) ObjectPropertyAssertion(:hasParent :alice :dora)\n"
            + "ObjectPropertyAssertion(:spouse :alice :bob) ObjectPropertyAssertion(:spouse :alice :robert)\n"
            + "ObjectPropertyAssertion(:eats :tom :rex)\n"
            + "DifferentIndividuals(:alice :bob)\n"
            + ")\n";

    /** Data properties outside the told fragment: a data property in a class axiom. */
    static final String DATA = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
            + "Ontology(<http://example.org/red-data>\n"
            + "Declaration(Class(:Adult)) Declaration(Class(:Person)) Declaration(Class(:Named))\n"
            + "Declaration(DataProperty(:age)) Declaration(DataProperty(:name)) Declaration(DataProperty(:label))\n"
            + "Declaration(NamedIndividual(:ann)) Declaration(NamedIndividual(:ben)) Declaration(NamedIndividual(:cid))\n"
            + "FunctionalDataProperty(:age) DataPropertyRange(:age xsd:integer) DataPropertyDomain(:age :Person)\n"
            + "SubDataPropertyOf(:name :label)\n"
            + "EquivalentClasses(:Named DataSomeValuesFrom(:name xsd:string))\n"
            + "SubClassOf(:Adult DataHasValue(:age \"30\"^^xsd:integer))\n"
            + "ClassAssertion(:Adult :ann) DataPropertyAssertion(:name :ben \"Ben\")\n"
            + "DataPropertyAssertion(:age :cid \"7\"^^xsd:integer) DataPropertyAssertion(:label :cid \"C\")\n"
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

    private static OWLOntology load(String text) throws Exception {
        return OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new StringDocumentSource(text));
    }

    private KMReasoner km(OWLOntology o) {
        KMReasoner r = (KMReasoner) new KMReasonerFactory().createReasoner(o);
        open.add(r);
        return r;
    }

    private OWLReasoner hermit(OWLOntology o) {
        OWLReasoner r = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        open.add(r);
        return r;
    }

    private static String name(Object o) {
        if (o instanceof OWLObjectInverseOf) return "inv(" + name(((OWLObjectInverseOf) o).getInverse()) + ")";
        if (o instanceof OWLEntity) {
            String iri = ((OWLEntity) o).getIRI().toString();
            return iri.startsWith(NS) ? iri.substring(NS.length()) : iri;
        }
        return String.valueOf(o);
    }

    private static Set<String> nodes(NodeSet<?> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<?> n : ns.getNodes()) out.add(node(n));
        return out;
    }

    private static String node(Node<?> n) {
        List<String> one = new ArrayList<>();
        for (Object e : n.getEntities()) one.add(name(e));
        Collections.sort(one);
        return one.toString();
    }

    private static Set<String> flat(NodeSet<?> ns) {
        Set<String> out = new TreeSet<>();
        for (Object e : ns.getFlattened()) out.add(name(e));
        return out;
    }

    private static void same(List<String> diffs, String call, Object hermit, Object km) {
        if (!Objects.equals(hermit, km)) diffs.add(call + ": HermiT " + hermit + " KM " + km);
    }

    private OWLDataFactory df() { return OWLManager.getOWLDataFactory(); }

    private OWLClass c(String n) { return df().getOWLClass(IRI.create(NS + n)); }
    private OWLObjectProperty p(String n) { return df().getOWLObjectProperty(IRI.create(NS + n)); }
    private OWLDataProperty d(String n) { return df().getOWLDataProperty(IRI.create(NS + n)); }
    private OWLNamedIndividual i(String n) { return df().getOWLNamedIndividual(IRI.create(NS + n)); }

    private List<OWLClassExpression> zooExpressions() {
        OWLDataFactory f = df();
        return Arrays.asList(
                f.getOWLObjectComplementOf(c("Mammal")),
                f.getOWLObjectIntersectionOf(c("Animal"), f.getOWLObjectSomeValuesFrom(p("ownedBy"), c("Person"))),
                f.getOWLObjectIntersectionOf(c("Dog"), c("Cat")),
                f.getOWLObjectUnionOf(c("Dog"), c("Cat")),
                f.getOWLObjectUnionOf(c("Animal"), f.getOWLObjectComplementOf(c("Animal"))),
                f.getOWLObjectSomeValuesFrom(p("eats"), f.getOWLThing()),
                f.getOWLObjectAllValuesFrom(p("eats"), c("Plant")),
                f.getOWLObjectSomeValuesFrom(f.getOWLObjectInverseOf(p("ownedBy")), c("Animal")),
                f.getOWLObjectMinCardinality(2, p("spouse"), f.getOWLThing()),
                f.getOWLObjectHasValue(p("partOf"), i("fleet")),
                f.getOWLObjectOneOf(i("alice"), i("rex")),
                f.getOWLObjectSomeValuesFrom(p("friend"), c("Person")));
    }

    @Test
    public void classExpressionQueriesAgreeWithHermit() throws Exception {
        OWLOntology o = load(ZOO);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<String> diffs = new ArrayList<>();
        for (OWLClassExpression ce : zooExpressions()) {
            String a = ce.toString();
            same(diffs, "isSatisfiable " + a, h.isSatisfiable(ce), k.isSatisfiable(ce));
            same(diffs, "equivalents " + a, node(h.getEquivalentClasses(ce)), node(k.getEquivalentClasses(ce)));
            for (boolean direct : new boolean[]{true, false}) {
                Set<String> hermitInstances = flat(h.getInstances(ce, direct));
                if (direct && ce.equals(df().getOWLObjectAllValuesFrom(p("eats"), c("Plant")))) {
                    // Adjudicated HermiT error: rex is a Herbivore, which HermiT itself puts
                    // strictly below ∀eats.Plant, so rex is no direct instance (OWL API definition).
                    assertTrue(flat(h.getSubClasses(ce, false)).contains("Herbivore"));
                    assertTrue(flat(h.getTypes(i("rex"), false)).contains("Herbivore"));
                    hermitInstances.remove("rex");
                }
                same(diffs, "supers " + direct + " " + a, nodes(h.getSuperClasses(ce, direct)), nodes(k.getSuperClasses(ce, direct)));
                same(diffs, "subs " + direct + " " + a, nodes(h.getSubClasses(ce, direct)), nodes(k.getSubClasses(ce, direct)));
                same(diffs, "instances " + direct + " " + a, hermitInstances, flat(k.getInstances(ce, direct)));
            }
            same(diffs, "disjoint " + a, nodes(h.getDisjointClasses(ce)), nodes(k.getDisjointClasses(ce)));
        }
        for (OWLClass cls : o.getClassesInSignature()) {
            same(diffs, "disjoint " + name(cls), nodes(h.getDisjointClasses(cls)), nodes(k.getDisjointClasses(cls)));
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
    }

    @Test
    public void classExpressionAnswersAreCachedPerRevision() throws Exception {
        OWLOntology o = load(ZOO);
        KMReasoner k = km(o);
        OWLClassExpression ce = df().getOWLObjectSomeValuesFrom(p("eats"), df().getOWLThing());
        k.getSuperClasses(ce, false);
        int runs = k.reductionRunCount();
        k.getSubClasses(ce, true);
        k.getEquivalentClasses(ce);
        k.isSatisfiable(ce);
        assertEquals("one run serves every hierarchy query of one expression", runs, k.reductionRunCount());
        assertTrue(flat(k.getSubClasses(ce, false)).contains("Carnivore"));
        o.getOWLOntologyManager().addAxiom(o, df().getOWLSubClassOfAxiom(c("Dog"), ce));
        k.flush();
        assertTrue("a change drops the cached answer", flat(k.getSubClasses(ce, false)).contains("Dog"));
        assertTrue(k.reductionRunCount() > runs);
    }

    @Test
    public void individualQueriesAgreeWithHermit() throws Exception {
        OWLOntology o = load(ZOO);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<String> diffs = new ArrayList<>();
        List<OWLNamedIndividual> inds = new ArrayList<>(new TreeSet<>(o.getIndividualsInSignature()));
        List<OWLObjectPropertyExpression> props = new ArrayList<>();
        for (OWLObjectProperty r : new TreeSet<>(o.getObjectPropertiesInSignature())) {
            props.add(r);
            props.add(df().getOWLObjectInverseOf(r));
        }
        props.add(df().getOWLBottomObjectProperty());
        for (OWLNamedIndividual a : inds) {
            same(diffs, "different " + name(a), flat(h.getDifferentIndividuals(a)), flat(k.getDifferentIndividuals(a)));
            for (OWLObjectPropertyExpression r : props) {
                same(diffs, "values " + name(a) + " " + name(r),
                        flat(h.getObjectPropertyValues(a, r)), flat(k.getObjectPropertyValues(a, r)));
            }
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        assertEquals(new TreeSet<>(Arrays.asList("car", "fleet")), flat(k.getObjectPropertyValues(i("wheel"), p("partOf"))));
        assertEquals(new TreeSet<>(Arrays.asList("alice")), flat(k.getObjectPropertyValues(i("bob"), p("friend"))));
    }

    @Test
    public void objectPropertyValuesAreComputedOnDemandPerProperty() throws Exception {
        OWLOntology o = load(ZOO);
        KMReasoner k = km(o);
        assertFalse(k.getPrecomputableInferenceTypes().contains(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
        k.precomputeInferences(InferenceType.OBJECT_PROPERTY_ASSERTIONS); // ignored
        assertFalse(k.isPrecomputed(InferenceType.OBJECT_PROPERTY_ASSERTIONS));
        assertEquals(new TreeSet<>(Arrays.asList("dora")), flat(k.getObjectPropertyValues(i("carl"), p("hasGrandparent"))));
        int runs = k.reductionRunCount();
        assertTrue(flat(k.getObjectPropertyValues(i("dora"), df().getOWLObjectInverseOf(p("hasGrandparent")))).contains("carl"));
        assertEquals("one run serves every subject and the inverse", runs, k.reductionRunCount());
    }

    @Test
    public void disjointObjectPropertiesAgreeWithHermit() throws Exception {
        OWLOntology o = load(ZOO);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<String> diffs = new ArrayList<>();
        for (OWLObjectProperty r : new TreeSet<>(o.getObjectPropertiesInSignature())) {
            same(diffs, "disjoint " + name(r), flat(h.getDisjointObjectProperties(r)), flat(k.getDisjointObjectProperties(r)));
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        assertTrue(flat(k.getDisjointObjectProperties(p("loves"))).contains("dislikes"));
    }

    private List<OWLAxiom> zooAxioms() {
        OWLDataFactory f = df();
        OWLClassExpression someOwner = f.getOWLObjectSomeValuesFrom(p("ownedBy"), c("Person"));
        return Arrays.asList(
                f.getOWLSubClassOfAxiom(c("Dog"), c("Animal")),
                f.getOWLSubClassOfAxiom(c("Pet"), someOwner),
                f.getOWLSubClassOfAxiom(c("Carnivore"), f.getOWLObjectSomeValuesFrom(p("eats"), c("Mammal"))),
                f.getOWLSubClassOfAxiom(c("Carnivore"), c("Animal")),
                f.getOWLEquivalentClassesAxiom(c("Pet"), f.getOWLObjectIntersectionOf(c("Animal"), someOwner)),
                f.getOWLEquivalentClassesAxiom(c("Pet"), c("Animal")),
                f.getOWLDisjointClassesAxiom(c("Dog"), c("Plant")),
                f.getOWLDisjointClassesAxiom(c("Dog"), c("Pet")),
                f.getOWLDisjointUnionAxiom(c("Mammal"), new HashSet<>(Arrays.asList(c("Dog"), c("Cat")))),
                f.getOWLClassAssertionAxiom(c("Pet"), i("tom")),
                f.getOWLClassAssertionAxiom(someOwner, i("rex")),
                f.getOWLClassAssertionAxiom(f.getOWLObjectSomeValuesFrom(p("eats"), c("Mammal")), i("tom")),
                f.getOWLClassAssertionAxiom(c("Herbivore"), i("rex")),
                f.getOWLClassAssertionAxiom(c("Herbivore"), i("tom")),
                f.getOWLObjectPropertyAssertionAxiom(p("partOf"), i("wheel"), i("fleet")),
                f.getOWLObjectPropertyAssertionAxiom(p("friend"), i("bob"), i("alice")),
                f.getOWLObjectPropertyAssertionAxiom(p("friend"), i("bob"), i("carl")),
                f.getOWLObjectPropertyAssertionAxiom(f.getOWLObjectInverseOf(p("owns")), i("rex"), i("alice")),
                f.getOWLNegativeObjectPropertyAssertionAxiom(p("dislikes"), i("carl"), i("alice")),
                f.getOWLNegativeObjectPropertyAssertionAxiom(p("dislikes"), i("alice"), i("carl")),
                f.getOWLSameIndividualAxiom(i("bob"), i("robert")),
                f.getOWLDifferentIndividualsAxiom(i("alice"), i("bob")),
                f.getOWLDifferentIndividualsAxiom(i("rex"), i("alice")),
                f.getOWLDifferentIndividualsAxiom(i("rex"), i("tom")),
                f.getOWLDifferentIndividualsAxiom(i("wheel"), i("car")),
                f.getOWLSubObjectPropertyOfAxiom(p("loves"), p("likes")),
                f.getOWLSubPropertyChainOfAxiom(Arrays.<OWLObjectPropertyExpression>asList(p("hasParent"), p("hasParent")), p("hasGrandparent")),
                f.getOWLSubPropertyChainOfAxiom(Arrays.<OWLObjectPropertyExpression>asList(p("partOf"), p("partOf")), p("partOf")),
                f.getOWLSubPropertyChainOfAxiom(Arrays.<OWLObjectPropertyExpression>asList(p("owns"), p("ownedBy")), p("knows")),
                f.getOWLSubPropertyChainOfAxiom(Arrays.<OWLObjectPropertyExpression>asList(p("loves"), p("hasParent")), p("likes")),
                f.getOWLDisjointObjectPropertiesAxiom(p("loves"), p("dislikes")),
                f.getOWLDisjointObjectPropertiesAxiom(p("loves"), p("eats")),
                f.getOWLObjectPropertyDomainAxiom(p("eats"), f.getOWLObjectUnionOf(c("Mammal"), c("Animal"))),
                f.getOWLObjectPropertyDomainAxiom(p("owns"), f.getOWLObjectSomeValuesFrom(p("owns"), f.getOWLThing())),
                f.getOWLObjectPropertyDomainAxiom(p("eats"), f.getOWLObjectComplementOf(c("Plant"))),
                f.getOWLObjectPropertyRangeAxiom(p("owns"), f.getOWLObjectIntersectionOf(f.getOWLThing(), f.getOWLObjectSomeValuesFrom(p("ownedBy"), c("Person")))),
                f.getOWLObjectPropertyRangeAxiom(p("eats"), f.getOWLObjectComplementOf(c("Plant"))),
                f.getOWLFunctionalObjectPropertyAxiom(p("spouse")),
                f.getOWLFunctionalObjectPropertyAxiom(p("friend")),
                f.getOWLInverseFunctionalObjectPropertyAxiom(p("ownedBy")),
                f.getOWLInverseFunctionalObjectPropertyAxiom(f.getOWLObjectInverseOf(p("spouse"))),
                f.getOWLTransitiveObjectPropertyAxiom(p("partOf")),
                f.getOWLFunctionalObjectPropertyAxiom(p("partOf")),
                f.getOWLInverseFunctionalObjectPropertyAxiom(p("partOf")),
                f.getOWLTransitiveObjectPropertyAxiom(p("friend")),
                f.getOWLAsymmetricObjectPropertyAxiom(p("hasParent")),
                f.getOWLAsymmetricObjectPropertyAxiom(p("friend")),
                f.getOWLReflexiveObjectPropertyAxiom(p("knows")),
                f.getOWLReflexiveObjectPropertyAxiom(p("friend")),
                f.getOWLIrreflexiveObjectPropertyAxiom(p("hasParent")),
                f.getOWLIrreflexiveObjectPropertyAxiom(p("partOf")),
                f.getOWLObjectPropertyAssertionAxiom(df().getOWLTopObjectProperty(), i("rex"), i("fern")),
                f.getOWLNegativeObjectPropertyAssertionAxiom(df().getOWLBottomObjectProperty(), i("rex"), i("fern")),
                f.getOWLTransitiveObjectPropertyAxiom(df().getOWLTopObjectProperty()),
                f.getOWLFunctionalObjectPropertyAxiom(df().getOWLBottomObjectProperty()));
    }

    @Test
    public void isEntailedAgreesWithHermitOnEveryAxiomType() throws Exception {
        OWLOntology o = load(ZOO);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<String> diffs = new ArrayList<>();
        int trueCount = 0;
        OWLAxiom bottomFunctional = df().getOWLFunctionalObjectPropertyAxiom(df().getOWLBottomObjectProperty());
        for (OWLAxiom ax : zooAxioms()) {
            assertTrue(ax.getAxiomType().toString(), k.isEntailmentCheckingSupported(ax.getAxiomType()));
            // Adjudicated: HermiT answers false, but the empty property is functional.
            boolean expected = ax.equals(bottomFunctional) || h.isEntailed(ax);
            if (expected) trueCount++;
            same(diffs, "isEntailed " + ax, expected, k.isEntailed(ax));
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        assertTrue("the axioms mix entailed and non-entailed ones", trueCount > 10 && trueCount < zooAxioms().size() - 10);
        assertTrue(k.isEntailed(new HashSet<>(zooAxioms().subList(0, 2))));
    }

    @Test
    public void keysRulesAndDatatypeDefinitionsAreRefused() throws Exception {
        OWLOntology o = load(ZOO);
        KMReasoner k = km(o);
        OWLAxiom key = df().getOWLHasKeyAxiom(c("Person"), Collections.singleton(p("spouse")));
        assertFalse(k.isEntailmentCheckingSupported(AxiomType.HAS_KEY));
        assertFalse(k.isEntailmentCheckingSupported(AxiomType.SWRL_RULE));
        assertFalse(k.isEntailmentCheckingSupported(AxiomType.DATATYPE_DEFINITION));
        try {
            k.isEntailed(key);
            fail("a key is not answered");
        } catch (UnsupportedEntailmentTypeException expected) {
            // refused, as isEntailmentCheckingSupported says
        }
    }

    @Test
    public void dataQueriesOutsideTheToldFragment() throws Exception {
        OWLOntology o = load(DATA);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        OWLDataFactory f = df();
        // Values: asserted, through a sub-property, and through DataHasValue in a class axiom.
        assertEquals(Collections.singleton(f.getOWLLiteral("30", f.getIntegerOWLDatatype())),
                k.getDataPropertyValues(i("ann"), d("age")));
        assertEquals(new HashSet<>(Arrays.asList(f.getOWLLiteral("Ben"))), k.getDataPropertyValues(i("ben"), d("label")));
        assertEquals(new HashSet<>(Arrays.asList(f.getOWLLiteral("C"))), k.getDataPropertyValues(i("cid"), d("label")));
        for (OWLNamedIndividual a : o.getIndividualsInSignature()) {
            for (OWLDataProperty p : o.getDataPropertiesInSignature()) {
                Set<OWLLiteral> hv = h.getDataPropertyValues(a, p);
                Set<OWLLiteral> kv = k.getDataPropertyValues(a, p);
                // HermiT returns the asserted values only; KM's answer contains them.
                assertTrue(name(a) + " " + name(p) + ": HermiT " + hv + " KM " + kv, kv.containsAll(hv));
            }
        }
        // Domains: the named superclasses of ∃p.rdfs:Literal.
        List<String> diffs = new ArrayList<>();
        for (OWLDataProperty p : o.getDataPropertiesInSignature()) {
            for (boolean direct : new boolean[]{true, false}) {
                same(diffs, "domains " + name(p) + " " + direct,
                        nodes(h.getDataPropertyDomains(p, direct)), nodes(k.getDataPropertyDomains(p, direct)));
            }
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        // Entailment of data axioms that reduce to unsatisfiability or consistency.
        List<OWLAxiom> axioms = Arrays.asList(
                f.getOWLDataPropertyDomainAxiom(d("age"), c("Person")),
                f.getOWLDataPropertyDomainAxiom(d("name"), c("Named")),
                f.getOWLDataPropertyDomainAxiom(d("label"), c("Named")),
                f.getOWLDataPropertyRangeAxiom(d("age"), f.getIntegerOWLDatatype()),
                f.getOWLDataPropertyRangeAxiom(d("age"), f.getOWLDatatype(org.semanticweb.owlapi.vocab.OWL2Datatype.XSD_STRING.getIRI())),
                f.getOWLFunctionalDataPropertyAxiom(d("age")),
                f.getOWLFunctionalDataPropertyAxiom(d("name")),
                f.getOWLDataPropertyAssertionAxiom(d("age"), i("ann"), f.getOWLLiteral("30", f.getIntegerOWLDatatype())),
                f.getOWLDataPropertyAssertionAxiom(d("label"), i("ben"), f.getOWLLiteral("Ben")),
                f.getOWLDataPropertyAssertionAxiom(d("name"), i("cid"), f.getOWLLiteral("C")),
                f.getOWLNegativeDataPropertyAssertionAxiom(d("age"), i("ann"), f.getOWLLiteral("31", f.getIntegerOWLDatatype())),
                f.getOWLNegativeDataPropertyAssertionAxiom(d("age"), i("cid"), f.getOWLLiteral("31", f.getIntegerOWLDatatype())));
        for (OWLAxiom ax : axioms) same(diffs, "isEntailed " + ax, h.isEntailed(ax), k.isEntailed(ax));
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        // The data property hierarchy outside the syntactic fragment is answered via --data-properties.
        assertTrue(k.isEntailmentCheckingSupported(AxiomType.SUB_DATA_PROPERTY));
        assertTrue(k.isEntailed(f.getOWLSubDataPropertyOfAxiom(d("name"), d("label"))));
        assertFalse(k.isEntailed(f.getOWLSubDataPropertyOfAxiom(d("label"), d("name"))));
        for (OWLDataProperty p : o.getDataPropertiesInSignature()) {
            for (boolean direct : new boolean[]{true, false}) {
                same(diffs, "subData " + name(p) + " " + direct,
                        nodes(h.getSubDataProperties(p, direct)), nodes(k.getSubDataProperties(p, direct)));
                same(diffs, "superData " + name(p) + " " + direct,
                        nodes(h.getSuperDataProperties(p, direct)), nodes(k.getSuperDataProperties(p, direct)));
            }
            same(diffs, "eqData " + name(p),
                    node(h.getEquivalentDataProperties(p)), node(k.getEquivalentDataProperties(p)));
            same(diffs, "disjData " + name(p),
                    nodes(h.getDisjointDataProperties(p)), nodes(k.getDisjointDataProperties(p)));
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
    }

    @Test
    public void unwrittenValuesOfSmallDataRangesAreCandidatesAndFacetsThrow() throws Exception {
        String head = "Prefix(:=<" + NS + ">)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
                + "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n";
        // nonNegativeInteger ∩ nonPositiveInteger = {0}: 0 is entailed and no literal writes it.
        String zero = head + "Ontology(<http://example.org/red-zero>\n"
                + "Declaration(DataProperty(:n)) Declaration(NamedIndividual(:z))\n"
                + "DataPropertyRange(:n xsd:nonNegativeInteger) DataPropertyRange(:n xsd:nonPositiveInteger)\n"
                + "ClassAssertion(DataSomeValuesFrom(:n rdfs:Literal) :z)\n)\n";
        KMReasoner k = km(load(zero));
        assertEquals(Collections.singleton(df().getOWLLiteral("0", df().getIntegerOWLDatatype())),
                k.getDataPropertyValues(i("z"), d("n")));
        // A facet restriction can pin a value too; it is refused.
        String facet = head + "Ontology(<http://example.org/red-facet>\n"
                + "Declaration(DataProperty(:n)) Declaration(NamedIndividual(:z))\n"
                + "DataPropertyRange(:n DatatypeRestriction(xsd:integer xsd:minExclusive \"4\"^^xsd:integer xsd:maxExclusive \"6\"^^xsd:integer))\n"
                + "ClassAssertion(DataSomeValuesFrom(:n rdfs:Literal) :z)\n)\n";
        try {
            km(load(facet)).getDataPropertyValues(i("z"), d("n"));
            fail("the value 5 could be entailed and no literal of the ontology denotes it");
        } catch (UnsupportedOperationException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains("data range"));
        }
    }

    @Test
    public void refusedRunsAreRememberedUntilFlush() throws Exception {
        // Under unknown_datatypes=free, an undeclared custom datatype is accepted;
        // a pattern facet restriction is outside the decided datatype fragment
        // (dropped > 0), so km refuses the reduction and remembers the failure.
        OWLOntology o = load(DATA);
        KMReasoner k = km(o);
        OWLClassExpression freeCustom = df().getOWLDataSomeValuesFrom(
                d("age"), df().getOWLDatatype(IRI.create(NS + "Custom")));
        assertNotNull(k.getSuperClasses(freeCustom, false));
        OWLClassExpression ce = df().getOWLDataSomeValuesFrom(
                d("age"),
                df().getOWLDatatypeRestriction(
                        df().getOWLDatatype(org.semanticweb.owlapi.vocab.OWL2Datatype.XSD_STRING.getIRI()),
                        org.semanticweb.owlapi.vocab.OWLFacet.PATTERN,
                        df().getOWLLiteral("a*")));
        RuntimeException first = null;
        try {
            k.getSuperClasses(ce, false);
            fail("km refuses a pattern facet restriction outside the decided datatype fragment");
        } catch (RuntimeException e) {
            first = e;
        }
        int runs = k.reductionRunCount();
        try {
            k.getSubClasses(ce, false);
            fail("the refusal is remembered");
        } catch (RuntimeException e) {
            assertSame(first, e);
        }
        assertEquals(runs, k.reductionRunCount());
    }

    @Test
    public void disjointDataPropertiesInsideTheToldFragmentAgreeWithHermit() throws Exception {
        String text = "Prefix(:=<" + NS + ">)\nPrefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
                + "Ontology(<http://example.org/red-ddp>\n"
                + "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n"
                + "Declaration(DataProperty(:p)) Declaration(DataProperty(:q)) Declaration(DataProperty(:r))\n"
                + "Declaration(DataProperty(:s)) Declaration(DataProperty(:t))\n"
                + "DisjointClasses(:A :B) SubClassOf(:C :A)\n"
                + "DataPropertyDomain(:p :A) DataPropertyDomain(:q :B) DataPropertyDomain(:r :C)\n"
                + "SubDataPropertyOf(:s :q) DataPropertyRange(:t xsd:integer)\n"
                + "DataPropertyAssertion(:t :i \"1\"^^xsd:integer)\n)\n";
        OWLOntology o = load(text);
        OWLReasoner h = hermit(o);
        KMReasoner k = km(o);
        List<String> diffs = new ArrayList<>();
        for (OWLDataProperty dp : new TreeSet<>(o.getDataPropertiesInSignature())) {
            same(diffs, "disjoint " + name(dp), nodes(h.getDisjointDataProperties(dp)), nodes(k.getDisjointDataProperties(dp)));
        }
        assertTrue(String.join("\n", diffs), diffs.isEmpty());
        assertTrue(flat(k.getDisjointDataProperties(d("p"))).contains("s"));
        assertTrue(k.isEntailmentCheckingSupported(AxiomType.DISJOINT_DATA_PROPERTIES));
        assertTrue(k.isEntailed(df().getOWLDisjointDataPropertiesAxiom(d("p"), d("q"))));
        assertFalse(k.isEntailed(df().getOWLDisjointDataPropertiesAxiom(d("p"), d("t"))));
    }
}
