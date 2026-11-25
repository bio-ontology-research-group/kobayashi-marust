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
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * The reflexive-property ABox rollup ({@code ForestABoxRollup.tryBuild}) asked
 * value probes only for individuals that occur in property assertions, so a
 * row through an anonymous individual to an individual without assertions was
 * lost. With a reflexive property the rollup is active; the values must still
 * match HermiT.
 */
public class RollupAnonValuesTest {

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

    @Test
    public void chainThroughAnonymousIndividualUnderReflexiveRollup() throws Exception {
        String ofn = "Prefix(:=<" + NS + ">)\nOntology(<" + NS + "roll>\n"
                + "Declaration(NamedIndividual(:a4))\nDeclaration(NamedIndividual(:b))\nDeclaration(Class(:B))\n"
                + "Declaration(ObjectProperty(:s1))\nDeclaration(ObjectProperty(:s3))\nDeclaration(ObjectProperty(:c1))\n"
                + "Declaration(ObjectProperty(:refl))\nDeclaration(DataProperty(:d))\n"
                + "ReflexiveObjectProperty(:refl)\n"
                + "SubObjectPropertyOf(ObjectInverseOf(:s3) :s1)\nSymmetricObjectProperty(:s1)\n"
                + "SubClassOf(:B ObjectSomeValuesFrom(ObjectInverseOf(:s3) :B))\n"
                + "SubObjectPropertyOf(ObjectPropertyChain(:s1 :s3) :c1)\nClassAssertion(:B :a4)\n"
                + "DataPropertyAssertion(:d :b \"1\")\n)\n";
        OWLOntology o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new StringDocumentSource(ofn));
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLNamedIndividual a4 = df.getOWLNamedIndividual(IRI.create(NS + "a4"));
        OWLObjectProperty c1 = df.getOWLObjectProperty(IRI.create(NS + "c1"));
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(km);
        OWLReasoner hermit = new ReasonerFactory().createReasoner(o);
        open.add(hermit);
        assertTrue(hermit.isEntailed(df.getOWLObjectPropertyAssertionAxiom(c1, a4, a4)));
        assertEquals(hermit.getObjectPropertyValues(a4, c1).getFlattened(), km.getObjectPropertyValues(a4, c1).getFlattened());
        assertTrue(km.isEntailed(df.getOWLObjectPropertyAssertionAxiom(c1, a4, a4)));
    }
}
