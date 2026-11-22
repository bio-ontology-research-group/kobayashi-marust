package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Object property values between named individuals whose path runs through an
 * anonymous individual (Protégé parity run 3, {@code h_f9002_44_chain_anon}):
 * {@code getObjectPropertyValues} and {@code isEntailed(ObjectPropertyAssertion)}
 * must agree with HermiT. The plugin's shortcuts that read only named edges or
 * only "active" properties missed these rows.
 */
public class ChainAnonValuesTest {

    private static final String NS = "http://ex.org/";

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
        return OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new StringDocumentSource(ofn));
    }

    private OWLReasoner open(OWLReasoner r) {
        open.add(r);
        return r;
    }

    /** Checks values(a, p), values(a, inv p) and isEntailed(p(a, b)) on KM against HermiT. */
    private void assertSameValues(String ofn, String subject, String property, String expected) throws Exception {
        OWLOntology o = parse(ofn);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLNamedIndividual a = df.getOWLNamedIndividual(IRI.create(NS + subject));
        OWLNamedIndividual b = df.getOWLNamedIndividual(IRI.create(NS + expected));
        OWLObjectProperty p = df.getOWLObjectProperty(IRI.create(NS + property));
        OWLReasoner km = open(new KMReasonerFactory().createReasoner(o));
        OWLReasoner hermit = open(new ReasonerFactory().createReasoner(o));
        for (OWLObjectPropertyExpression pe : new OWLObjectPropertyExpression[]{p, p.getInverseProperty()}) {
            OWLNamedIndividual from = pe.isAnonymous() ? b : a;
            Set<OWLNamedIndividual> h = hermit.getObjectPropertyValues(from, pe).getFlattened();
            Set<OWLNamedIndividual> k = km.getObjectPropertyValues(from, pe).getFlattened();
            assertEquals("values(" + from + ", " + pe + ")", h, k);
        }
        assertTrue("HermiT entails " + property + "(" + subject + ", " + expected + ")",
                hermit.isEntailed(df.getOWLObjectPropertyAssertionAxiom(p, a, b)));
        assertTrue("KM entails " + property + "(" + subject + ", " + expected + ")",
                km.isEntailed(df.getOWLObjectPropertyAssertionAxiom(p, a, b)));
    }

    /** The parity reproducer verbatim: no property declarations. */
    @Test
    public void chainThroughAnonymousIndividualReturnsToItsStart() throws Exception {
        assertSameValues("Prefix(:=<" + NS + ">)\nOntology(<" + NS + "r1>\n"
                + "Declaration(NamedIndividual(:a4))\nDeclaration(Class(:B))\n"
                + "SubObjectPropertyOf(ObjectInverseOf(:s3) :s1)\nSymmetricObjectProperty(:s1)\n"
                + "SubClassOf(:B ObjectSomeValuesFrom(ObjectInverseOf(:s3) :B))\n"
                + "SubObjectPropertyOf(ObjectPropertyChain(:s1 :s3) :c1)\nClassAssertion(:B :a4)\n)\n",
                "a4", "c1", "a4");
    }

    /** Symmetric and transitive t with an anonymous successor: t(a, a). */
    @Test
    public void transitiveSymmetricLoopThroughAnonymousIndividual() throws Exception {
        assertSameValues("Prefix(:=<" + NS + ">)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\nOntology(<" + NS + "r2>\n"
                + "Declaration(NamedIndividual(:a))\nDeclaration(NamedIndividual(:b))\nDeclaration(Class(:B))\n"
                + "Declaration(ObjectProperty(:t))\nDeclaration(ObjectProperty(:k))\n"
                + "TransitiveObjectProperty(:t)\nSymmetricObjectProperty(:t)\n"
                + "SubClassOf(:B ObjectSomeValuesFrom(:t owl:Thing))\nClassAssertion(:B :a)\n"
                + "ObjectPropertyAssertion(:k :b :b)\n)\n",
                "a", "t", "a");
    }

    /** The existential's successor merges with the named b: s ⊑ f, f functional, f(x, b). */
    @Test
    public void functionalMergeOfAnonymousSuccessorWithNamedIndividual() throws Exception {
        assertSameValues("Prefix(:=<" + NS + ">)\nOntology(<" + NS + "r3>\n"
                + "Declaration(NamedIndividual(:x))\nDeclaration(NamedIndividual(:b))\nDeclaration(Class(:C))\n"
                + "Declaration(ObjectProperty(:s))\nDeclaration(ObjectProperty(:f))\n"
                + "SubObjectPropertyOf(:s :f)\nFunctionalObjectProperty(:f)\n"
                + "ObjectPropertyAssertion(:f :x :b)\nClassAssertion(ObjectSomeValuesFrom(:s :C) :x)\n)\n",
                "x", "s", "b");
    }
}
