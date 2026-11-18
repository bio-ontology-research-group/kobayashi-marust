package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.ReasonerInternalException;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * Tests the Protege plugin's lenient input mode and {@code unknown_datatypes=free}
 * against the minimal ontologies of {@code docs/V1.7.0-LENIENT-INPUT.md}.
 */
public class LenientInputTest {

    private static final String NS = "http://example.org/t#";

    @BeforeClass
    public static void setUp() {
        HermitDifferentialTest.locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();

    @After
    public void closeReasoners() {
        for (OWLReasoner r : open) r.dispose();
    }

    private static OWLOntology parse(String ofn) throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        return m.loadOntologyFromOntologyDocument(new StringDocumentSource(ofn));
    }

    private OWLReasoner km(OWLOntology o) {
        OWLReasoner r = new KMReasonerFactory().createReasoner(o);
        open.add(r);
        return r;
    }

    private OWLReasoner hermit(OWLOntology o) {
        OWLReasoner r = new ReasonerFactory().createReasoner(o);
        open.add(r);
        return r;
    }

    @Test
    public void anonymousIndividualInObjectHasValueSharesOntologyWideSkolemSemantics() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:A))\n"
                + "  Declaration(Class(:B))\n"
                + "  Declaration(ObjectProperty(:r))\n"
                + "  Declaration(NamedIndividual(:x))\n"
                + "  InverseFunctionalObjectProperty(:r)\n"
                + "  SubClassOf(:A ObjectHasValue(:r _:b1))\n"
                + "  ClassAssertion(ObjectHasValue(:r _:b1) :x)\n"
                + "  ClassAssertion(:B :x)\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLClass a = df.getOWLClass(IRI.create(NS + "A"));
        OWLClass b = df.getOWLClass(IRI.create(NS + "B"));
        OWLNamedIndividual x = df.getOWLNamedIndividual(IRI.create(NS + "x"));

        OWLReasoner h = hermit(o);
        OWLReasoner k = km(o);
        assertEquals(h.isConsistent(), k.isConsistent());
        assertTrue(k.isConsistent());
        assertTrue(h.getSuperClasses(a, true).containsEntity(b));
        assertTrue(k.getSuperClasses(a, true).containsEntity(b));
        assertEquals(h.getInstances(b, false).getFlattened(), k.getInstances(b, false).getFlattened());
        assertEquals(h.getInstances(df.getOWLThing(), false).getFlattened(),
                k.getInstances(df.getOWLThing(), false).getFlattened());
        assertEquals(h.getObjectPropertyValues(x, df.getOWLObjectProperty(IRI.create(NS + "r"))).getFlattened(),
                k.getObjectPropertyValues(x, df.getOWLObjectProperty(IRI.create(NS + "r"))).getFlattened());
        assertTrue(k.getInstances(b, false).containsEntity(x));
        assertEquals(1, k.getInstances(b, false).getFlattened().size());
        assertNotNull(Classifier.lastLoggedModeNote());
        assertTrue(Classifier.lastLoggedModeNote().contains("--lenient"));
        assertTrue(Classifier.lastLoggedModeNote().contains("--unknown-datatypes=free"));
    }

    @Test
    public void anonymousIndividualInObjectOneOfUnderQuantifierAndComplement() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:A))\n"
                + "  Declaration(ObjectProperty(:r))\n"
                + "  SubClassOf(:A ObjectSomeValuesFrom(:r ObjectOneOf(_:b1)))\n"
                + "  SubClassOf(:A ObjectAllValuesFrom(:r ObjectComplementOf(ObjectOneOf(_:b1))))\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLClass a = df.getOWLClass(IRI.create(NS + "A"));

        OWLReasoner h = hermit(o);
        OWLReasoner k = km(o);
        assertEquals(h.isConsistent(), k.isConsistent());
        assertEquals(h.isSatisfiable(a), k.isSatisfiable(a));
        assertFalse(k.isSatisfiable(a));
    }

    @Test
    public void anonymousIndividualForestViolationsAreAcceptedLikeHermiT() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:C))\n"
                + "  Declaration(ObjectProperty(:r))\n"
                + "  Declaration(NamedIndividual(:n1))\n"
                + "  Declaration(NamedIndividual(:n2))\n"
                + "  ClassAssertion(:C _:b1)\n"
                + "  ObjectPropertyAssertion(:r _:b1 _:b1)\n"
                + "  ObjectPropertyAssertion(:r :n1 _:b1)\n"
                + "  ObjectPropertyAssertion(:r :n2 _:b1)\n"
                + "  SubClassOf(ObjectHasSelf(:r) owl:Nothing)\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLReasoner h = hermit(o);
        OWLReasoner k = km(o);
        assertFalse(h.isConsistent());
        assertFalse(k.isConsistent());
    }

    @Test
    public void nonRfc3987ReplacementCharAndBracketIrisRoundTrip() throws Exception {
        String baden = NS + "Baden-W\uFFFDrttemberg";
        String bracket = NS + "[Event,]";
        String ofn = "Ontology(\n"
                + "  Declaration(Class(<" + baden + ">))\n"
                + "  Declaration(Class(<" + bracket + ">))\n"
                + "  SubClassOf(<" + baden + "> <" + bracket + ">)\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLClass sub = df.getOWLClass(IRI.create(baden));
        OWLClass sup = df.getOWLClass(IRI.create(bracket));

        OWLReasoner h = hermit(o);
        OWLReasoner k = km(o);
        assertTrue(h.isConsistent());
        assertTrue(k.isConsistent());
        assertTrue(h.getSuperClasses(sub, true).containsEntity(sup));
        assertTrue(k.getSuperClasses(sub, true).containsEntity(sup));
    }

    @Test
    public void rdfsLiteralTypedLiteralsAndUnknownDatatypesAreAccepted() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Prefix(rdfs:=<http://www.w3.org/2000/01/rdf-schema#>)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:A))\n"
                + "  Declaration(Class(:B))\n"
                + "  Declaration(DataProperty(:dp))\n"
                + "  Declaration(Datatype(:customDt))\n"
                + "  SubClassOf(:A DataHasValue(:dp \"NULL\"^^rdfs:Literal))\n"
                + "  SubClassOf(DataSomeValuesFrom(:dp DataOneOf(\"NULL\"^^rdfs:Literal)) :B)\n"
                + "  DataPropertyRange(:dp :customDt)\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLClass a = df.getOWLClass(IRI.create(NS + "A"));
        OWLClass b = df.getOWLClass(IRI.create(NS + "B"));

        OWLReasoner h = hermit(o);
        OWLReasoner k = km(o);
        assertTrue(h.isConsistent());
        assertTrue(k.isConsistent());
        assertTrue(h.getSuperClasses(a, true).containsEntity(b));
        assertTrue(k.getSuperClasses(a, true).containsEntity(b));
    }

    @Test
    public void undeclaredAnnotationPropertyIsAccepted() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:A))\n"
                + "  Declaration(Class(:B))\n"
                + "  AnnotationAssertion(:undeclaredProp :A \"note\")\n"
                + "  SubClassOf(:A :B)\n"
                + ")\n";
        try (Classifier.Session s = new Classifier.Session(ofn)) {
            assertTrue(s.consistent());
            assertEquals(0, s.dropped());
            assertFalse(s.lenient().isEmpty());
            assertTrue(s.lenient().get(0).contains("AnnotationProperty"));
        }
    }

    @Test
    public void nonXsdTildeEscapeInXsdPatternPassesValidation() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\n"
                + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
                + "Ontology(\n"
                + "  Declaration(Class(:A))\n"
                + "  Declaration(DataProperty(:dp))\n"
                + "  SubClassOf(:A DataSomeValuesFrom(:dp DatatypeRestriction(xsd:string xsd:pattern \"[\\\\~]abc\")))\n"
                + ")\n";
        OWLOntology o = parse(ofn);
        OWLReasoner k = km(o);
        try {
            k.isConsistent();
            fail("xsd:pattern is outside KM's decided datatype fragment and must report dropped > 0");
        } catch (ReasonerInternalException expected) {
            assertFalse(expected.getMessage().contains("invalid OWL 2 DL input"));
            assertTrue(expected.getMessage().contains("declined a complete classification"));
        }
    }
}
