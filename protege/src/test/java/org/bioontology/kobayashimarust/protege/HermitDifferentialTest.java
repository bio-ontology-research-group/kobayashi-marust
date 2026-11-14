package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import java.io.File;
import java.util.*;

import static org.junit.Assert.*;

/**
 * Runs HermiT and the KM reasoner on the same ontologies through the OWL API
 * and compares the individual queries: {@code getTypes} (direct and all),
 * {@code getInstances} of every named class (direct and all), and
 * {@code getSameIndividuals} of every individual.
 */
public class HermitDifferentialTest {

    static void locateKm() {
        if (System.getProperty("km.bin") == null) {
            File release = new File("../.work/target/release/km");
            File debug = new File("../.work/target/debug/km");
            File local = release.isFile() ? release : debug;
            if (!local.isFile()) {
                throw new IllegalStateException(
                        "build km under the checkout-local .work/target or pass -Dkm.bin");
            }
            System.setProperty("km.bin", local.getAbsolutePath());
        }
    }

    @BeforeClass
    public static void setUp() {
        locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();

    @After
    public void closeReasoners() {
        for (OWLReasoner r : open) r.dispose();
    }

    private static final String NS = IndividualsTest.NS;

    private static Set<String> nodes(NodeSet<? extends OWLEntity> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<? extends OWLEntity> n : ns.getNodes()) out.add(node(n));
        return out;
    }

    /**
     * Adjudicated HermiT error. On wine, some runs of HermiT 1.4.3 return
     * getTypes(ind, true) with both Chardonnay and its superclass WhiteWine,
     * although its own taxonomy has Chardonnay below WhiteWine; other runs
     * return only Chardonnay. A direct answer cannot hold a node above
     * another node of the same answer, so drop such nodes from HermiT's side.
     */
    private static Set<String> mostSpecific(OWLReasoner hermit, NodeSet<OWLClass> types) {
        Set<String> out = new TreeSet<>();
        for (Node<OWLClass> n : types.getNodes()) {
            boolean aboveAnother = false;
            for (Node<OWLClass> other : types.getNodes()) {
                if (other != n && !other.equals(n)
                        && hermit.getSuperClasses(other.getRepresentativeElement(), false)
                                .containsEntity(n.getRepresentativeElement())) {
                    aboveAnother = true;
                    break;
                }
            }
            if (!aboveAnother) out.add(node(n));
        }
        return out;
    }

    private static Set<String> flat(NodeSet<? extends OWLEntity> ns) {
        Set<String> out = new TreeSet<>();
        for (OWLEntity e : ns.getFlattened()) out.add(e.getIRI().toString());
        return out;
    }

    private static String node(Node<? extends OWLEntity> n) {
        List<String> one = new ArrayList<>();
        for (OWLEntity e : n.getEntities()) one.add(e.getIRI().toString());
        Collections.sort(one);
        return one.toString();
    }

    /** All differences between HermiT and KM on the individual queries of {@code ontology}. */
    static List<String> differences(OWLOntology ontology, List<OWLReasoner> sink) {
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(ontology);
        OWLReasoner km = new KMReasonerFactory().createReasoner(ontology);
        sink.add(hermit);
        sink.add(km);
        List<String> diffs = new ArrayList<>();
        Set<OWLNamedIndividual> individuals = new TreeSet<>(ontology.getIndividualsInSignature(
                org.semanticweb.owlapi.model.parameters.Imports.INCLUDED));
        Set<OWLClass> classes = new TreeSet<>(ontology.getClassesInSignature(
                org.semanticweb.owlapi.model.parameters.Imports.INCLUDED));
        classes.add(ontology.getOWLOntologyManager().getOWLDataFactory().getOWLThing());
        classes.add(ontology.getOWLOntologyManager().getOWLDataFactory().getOWLNothing());
        for (OWLNamedIndividual i : individuals) {
            for (boolean direct : new boolean[]{true, false}) {
                NodeSet<OWLClass> hermitTypes = hermit.getTypes(i, direct);
                compare(diffs, "getTypes(" + i.getIRI() + "," + direct + ")",
                        direct ? mostSpecific(hermit, hermitTypes) : nodes(hermitTypes),
                        nodes(km.getTypes(i, direct)));
            }
            compare(diffs, "getSameIndividuals(" + i.getIRI() + ")",
                    Collections.singleton(node(hermit.getSameIndividuals(i))),
                    Collections.singleton(node(km.getSameIndividuals(i))));
        }
        for (OWLClass c : classes) {
            for (boolean direct : new boolean[]{true, false}) {
                // HermiT returns one node per individual, even for individuals it
                // reports as equal in getSameIndividuals. The OWL API contract (and
                // KM) group them, so compare the individuals, not the node shapes.
                compare(diffs, "getInstances(" + c.getIRI() + "," + direct + ")",
                        flat(hermit.getInstances(c, direct)), flat(km.getInstances(c, direct)));
            }
        }
        return diffs;
    }

    private static void compare(List<String> diffs, String what, Set<String> hermit, Set<String> km) {
        if (!hermit.equals(km)) {
            Set<String> onlyHermit = new TreeSet<>(hermit);
            onlyHermit.removeAll(km);
            Set<String> onlyKm = new TreeSet<>(km);
            onlyKm.removeAll(hermit);
            diffs.add(what + ": only HermiT " + onlyHermit + "; only KM " + onlyKm);
        }
    }

    private void assertNoDifferences(String label, OWLOntology ontology) {
        List<String> diffs = differences(ontology, open);
        if (!diffs.isEmpty()) {
            fail(label + ": " + diffs.size() + " difference(s) from HermiT, first:\n  "
                    + String.join("\n  ", diffs.subList(0, Math.min(15, diffs.size()))));
        }
    }

    @Test
    public void smallAbox() throws Exception {
        assertNoDifferences("small ABox", IndividualsTest.parse(IndividualsTest.SMALL));
    }

    @Test
    public void nominalsAndCardinality() throws Exception {
        String src = "Prefix(:=<" + NS + ">)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
                + "Ontology(<http://example.org/mixed>\n"
                + "SubClassOf(:Red ObjectOneOf(:apple :cherry))\n"
                + "ClassAssertion(:Red :x)\n"
                + "SubClassOf(:Owner ObjectMaxCardinality(1 :has :Thing))\n"
                + "ClassAssertion(:Owner :o)\nObjectPropertyAssertion(:has :o :p)\nObjectPropertyAssertion(:has :o :q)\n"
                + "ClassAssertion(:Item :p)\nClassAssertion(:Item :q)\n"
                + "SubClassOf(ObjectSomeValuesFrom(:has :Item) :Holder)\n"
                + "InverseObjectProperties(:has :heldBy)\n"
                + "ObjectPropertyDomain(:likes :Person)\nObjectPropertyRange(:likes :Food)\n"
                + "ObjectPropertyAssertion(:likes :ann :pizza)\n"
                + "DifferentIndividuals(:apple :cherry)\n"
                + "ClassAssertion(:Fruit :apple)\nSubClassOf(:Fruit :Food)\n"
                + "SubClassOf(:Unsat ObjectIntersectionOf(:Fruit ObjectComplementOf(:Food)))\n"
                + ")\n";
        assertNoDifferences("nominals", IndividualsTest.parse(src));
    }

    /**
     * A class declared equivalent to owl:Thing is a type of every individual.
     * KM's class hierarchy does not yet put it in the same node as owl:Thing
     * (the taxonomy has no owl:Thing row), so the node shape differs from
     * HermiT's; the set of types is the same.
     */
    @Test
    public void classEquivalentToThingIsATypeOfEveryIndividual() throws Exception {
        String src = "Prefix(:=<" + NS + ">)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
                + "Ontology(<http://example.org/everything>\n"
                + "Declaration(Class(:Everything)) Declaration(Class(:A))\n"
                + "EquivalentClasses(:Everything owl:Thing)\n"
                + "SubClassOf(:A :Everything)\nClassAssertion(:A :a)\nDeclaration(NamedIndividual(:b))\n"
                + ")\n";
        OWLOntology o = IndividualsTest.parse(src);
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(hermit);
        open.add(km);
        for (OWLNamedIndividual i : o.getIndividualsInSignature()) {
            assertEquals(flat(hermit.getTypes(i, false)), flat(km.getTypes(i, false)));
        }
    }

    @Test
    public void inconsistentOntologyThrowsAsHermitDoes() throws Exception {
        String src = IndividualsTest.SMALL.replace("Declaration(NamedIndividual(:loner))",
                "DisjointClasses(:Dog :Cat)\nClassAssertion(:Dog :tom)");
        OWLOntology o = IndividualsTest.parse(src);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLNamedIndividual rex = df.getOWLNamedIndividual(IRI.create(NS + "rex"));
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        open.add(hermit);
        assertFalse(hermit.isConsistent());
        try {
            hermit.getTypes(rex, false);
            fail("HermiT is expected to throw on an inconsistent ontology");
        } catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) {
            // HermiT throws, and so does KM.
        }
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(km);
        assertFalse(km.isConsistent());
        try {
            km.getTypes(rex, false);
            fail("KM is expected to throw like HermiT");
        } catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) {
            // same as HermiT
        }
    }

    @Test
    public void w3cWineAndFood() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        for (String name : new String[]{"wine", "food"}) {
            File file = new File(getClass().getResource("/w3c/" + name + ".rdf").toURI());
            manager.getIRIMappers().add(new SimpleIRIMapper(
                    IRI.create("http://www.w3.org/TR/2003/PR-owl-guide-20031209/" + name), IRI.create(file)));
        }
        OWLOntology wine = manager.loadOntology(
                IRI.create("http://www.w3.org/TR/2003/PR-owl-guide-20031209/wine"));
        assertTrue("wine has individuals",
                wine.getIndividualsInSignature(org.semanticweb.owlapi.model.parameters.Imports.INCLUDED).size() > 100);
        assertNoDifferences("wine and food", wine);
    }

    /** HermiT's default FreshEntityPolicy: a class outside the signature sits between Top and Bottom. */
    @Test
    public void freshNamedClassSitsBetweenTopAndBottom() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(hermit);
        open.add(km);
        OWLClass fresh = df.getOWLClass(IRI.create(NS + "NeverDeclared"));
        OWLClass dog = df.getOWLClass(IRI.create(NS + "Dog"));
        for (boolean direct : new boolean[]{true, false}) {
            assertEquals(nodes(hermit.getSuperClasses(fresh, direct)), nodes(km.getSuperClasses(fresh, direct)));
            assertEquals(nodes(hermit.getSubClasses(fresh, direct)), nodes(km.getSubClasses(fresh, direct)));
        }
        assertEquals(node(hermit.getEquivalentClasses(fresh)), node(km.getEquivalentClasses(fresh)));
        OWLClass animal = df.getOWLClass(IRI.create(NS + "Animal"));
        OWLClass other = df.getOWLClass(IRI.create(NS + "OtherFresh"));
        for (OWLClassExpression sub : new OWLClassExpression[]{fresh, dog, animal, df.getOWLThing(), df.getOWLNothing(), other}) {
            for (OWLClassExpression sup : new OWLClassExpression[]{fresh, dog, animal, df.getOWLThing(), df.getOWLNothing(), other}) {
                OWLAxiom axiom = df.getOWLSubClassOfAxiom(sub, sup);
                assertEquals(axiom.toString(), hermit.isEntailed(axiom), km.isEntailed(axiom));
            }
        }
        assertEquals(hermit.isSatisfiable(fresh), km.isSatisfiable(fresh));
    }

    /** isEntailed(Set) ignores annotation and declaration axioms like HermiT. */
    @Test
    public void entailedSetIgnoresNonLogicalAxioms() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(hermit);
        open.add(km);
        OWLClass dog = df.getOWLClass(IRI.create(NS + "Dog"));
        OWLClass animal = df.getOWLClass(IRI.create(NS + "Animal"));
        Set<OWLAxiom> set = new HashSet<>();
        set.add(df.getOWLDeclarationAxiom(df.getOWLClass(IRI.create(NS + "NeverSeen"))));
        set.add(df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(), dog.getIRI(), df.getOWLLiteral("label")));
        assertEquals(hermit.isEntailed(set), km.isEntailed(set));
        set.add(df.getOWLSubClassOfAxiom(dog, animal));
        assertEquals(hermit.isEntailed(set), km.isEntailed(set));
        set.add(df.getOWLSubClassOfAxiom(animal, dog));
        assertEquals(hermit.isEntailed(set), km.isEntailed(set));
    }
}
