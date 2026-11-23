package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A negative data assertion entailed because the property is functional and
 * the individual already has another value (Protégé parity run 4,
 * {@code ore_ont_3205}). The plugin decides it as the inconsistency of the
 * ontology plus the positive assertion; KM's data ABox projection wrote the
 * clash as a one-operand {@code DifferentIndividuals} and answered false. It
 * takes a second assertion of the property on another individual.
 */
public class FunctionalDataValueTest {

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

    private static final String ONTOLOGY = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
            + "Ontology(<" + NS + "functional-data-value>\n"
            + "FunctionalDataProperty(:p)\n"
            + "InverseFunctionalObjectProperty(:t)\n"
            + "SubClassOf(:D :C)\n"
            + "DataPropertyAssertion(:p :a \"first value\"^^xsd:string)\n"
            + "DataPropertyAssertion(:p :b \"second value\"^^xsd:string)\n"
            + ")\n";

    @Test
    public void negativeAssertionOfAnotherValueOfAFunctionalPropertyIsEntailed() throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager()
                .loadOntologyFromOntologyDocument(new StringDocumentSource(ONTOLOGY));
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLDataProperty p = df.getOWLDataProperty(IRI.create(NS + "p"));
        OWLNamedIndividual b = df.getOWLNamedIndividual(IRI.create(NS + "b"));
        OWLAxiom other = df.getOWLNegativeDataPropertyAssertionAxiom(p, b, df.getOWLLiteral("x"));
        OWLAxiom own = df.getOWLNegativeDataPropertyAssertionAxiom(p, b,
                df.getOWLLiteral("second value"));
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(km);
        OWLReasoner hermit = new ReasonerFactory().createReasoner(o);
        open.add(hermit);
        assertTrue("HermiT entails " + other, hermit.isEntailed(other));
        assertTrue("KM entails " + other, km.isEntailed(other));
        assertEquals("own value", hermit.isEntailed(own), km.isEntailed(own));
    }
}
