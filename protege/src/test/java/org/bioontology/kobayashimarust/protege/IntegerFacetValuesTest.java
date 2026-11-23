package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLLiteral;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

/**
 * Data property values next to facet restrictions on integer datatypes
 * (Protégé parity run 4: {@code getDataPropertyValues} on {@code ore_ont_2548},
 * {@code 13700} and {@code 9662} declined with "the data range
 * DatatypeRestriction(xsd:int ...)" once the ABox rollup stepped aside for
 * values through anonymous individuals). Integer bounds now cut the integers
 * into intervals like the integer datatypes' own bounds, so the values a
 * small interval can force are candidates and the query answers.
 */
public class IntegerFacetValuesTest {

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

    /** Anonymous successors and a functional object property: the rollup steps aside. */
    private static final String ONTOLOGY = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n"
            + "Ontology(<" + NS + "integer-facets>\n"
            + "FunctionalObjectProperty(:r)\n"
            + "SubClassOf(:C ObjectSomeValuesFrom(:r :D))\n"
            + "FunctionalDataProperty(:p)\n"
            + "DataPropertyRange(:p DatatypeRestriction(xsd:int xsd:minInclusive \"0\"^^xsd:integer"
            + " xsd:maxInclusive \"9\"^^xsd:integer))\n"
            + "DataPropertyRange(:q DatatypeRestriction(xsd:int xsd:maxExclusive \"10\"^^xsd:int))\n"
            + "SubClassOf(:D DataSomeValuesFrom(:p DatatypeRestriction(xsd:int xsd:minInclusive \"9\"^^xsd:int)))\n"
            + "ClassAssertion(:C :a)\n"
            + "ClassAssertion(:D :b)\n"
            + "DataPropertyAssertion(:p :c \"3\"^^xsd:int)\n"
            + "DataPropertyAssertion(:q :c \"4\"^^xsd:int)\n"
            + "FunctionalDataProperty(:f)\n"
            + "DataPropertyRange(:f xsd:float)\n"
            + "DataPropertyAssertion(:f :c \"2.5\"^^xsd:float)\n"
            + ")\n";

    @Test
    public void integerBoundsDoNotPutTheOntologyOutsideTheFragment() throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager()
                .loadOntologyFromOntologyDocument(new StringDocumentSource(ONTOLOGY));
        DataValues.Candidates c = DataValues.collect(o, o.getOWLOntologyManager().getOWLDataFactory());
        assertNull(c.outside);
    }

    @Test
    public void valuesAgreeWithHermit() throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager()
                .loadOntologyFromOntologyDocument(new StringDocumentSource(ONTOLOGY));
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner km = new KMReasonerFactory().createReasoner(o);
        open.add(km);
        OWLReasoner hermit = new ReasonerFactory().createReasoner(o);
        open.add(hermit);
        for (String ind : new String[]{"a", "b", "c"}) {
            for (String prop : new String[]{"p", "q", "f"}) {
                OWLNamedIndividual i = df.getOWLNamedIndividual(IRI.create(NS + ind));
                OWLDataProperty p = df.getOWLDataProperty(IRI.create(NS + prop));
                // HermiT's getDataPropertyValues lists asserted values only, so
                // the oracle adds isEntailed(p(i, v)) for every integer the
                // ranges admit (b's p is forced to 9 by D and the range).
                Set<Object> h = keys(hermit.getDataPropertyValues(i, p));
                for (int v = -1; v <= 10; v++) {
                    OWLLiteral l = df.getOWLLiteral(Integer.toString(v),
                            df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#int")));
                    if (hermit.isEntailed(df.getOWLDataPropertyAssertionAxiom(p, i, l))) {
                        h.add(DataValues.valueKey(l));
                    }
                }
                Set<Object> k = keys(km.getDataPropertyValues(i, p));
                assertEquals(ind + " " + prop, h, k);
            }
        }
    }

    /** The integer candidates never become values of a property with a float range. */
    @Test
    public void integersAreOutsideTheFloats() {
        OWLDataFactory df = OWLManager.getOWLDataFactory();
        org.junit.Assert.assertTrue(DataValues.definitelyOutside(df.getOWLLiteral(3),
                df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#float"))));
        org.junit.Assert.assertTrue(DataValues.definitelyOutside(df.getOWLLiteral(2.5f),
                df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#integer"))));
        org.junit.Assert.assertFalse(DataValues.definitelyOutside(df.getOWLLiteral(2.5f),
                df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#float"))));
    }

    private static Set<Object> keys(Set<OWLLiteral> values) {
        Set<Object> out = new HashSet<>();
        for (OWLLiteral l : values) out.add(DataValues.valueKey(l));
        return out;
    }
}
