package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;

import java.util.*;

import static org.junit.Assert.*;

/**
 * Lifecycle and small-behaviour parity with HermiT: timeouts and progress
 * monitor, interrupt, inconsistent ontologies, fresh entities, lazy
 * classification. Where HermiT is the specification the comparison is in
 * {@link HermitDifferentialTest}.
 */
public class PluginBehaviourTest {

    static final String NS = IndividualsTest.NS;

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

    private KMReasoner km(OWLOntology ontology, OWLReasonerConfiguration config) {
        KMReasoner r = (KMReasoner) new KMReasonerFactory().createReasoner(ontology, config);
        open.add(r);
        return r;
    }

    static OWLClass cls(OWLDataFactory df, String f) { return df.getOWLClass(IRI.create(NS + f)); }
    static OWLNamedIndividual ind(OWLDataFactory df, String f) { return df.getOWLNamedIndividual(IRI.create(NS + f)); }

    static OWLDataFactory dataFactory(OWLOntology o) { return o.getOWLOntologyManager().getOWLDataFactory(); }

    static final String INCONSISTENT = IndividualsTest.SMALL.replace("Declaration(NamedIndividual(:loner))",
            "DisjointClasses(:Dog :Cat)\nClassAssertion(:Dog :tom)");

    // ---- item 6: isEntailed(Set) --------------------------------------

    @Test
    public void entailedSetSkipsAnnotationAndDeclarationAxioms() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = dataFactory(o);
        KMReasoner r = km(o);
        Set<OWLAxiom> set = new HashSet<>();
        set.add(df.getOWLDeclarationAxiom(cls(df, "NeverSeen")));
        set.add(df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(), cls(df, "Dog").getIRI(),
                df.getOWLLiteral("unasserted label")));
        assertTrue("annotations and declarations are not logical", r.isEntailed(set));
        set.add(df.getOWLSubClassOfAxiom(cls(df, "Dog"), cls(df, "Animal")));
        assertTrue(r.isEntailed(set));
        set.add(df.getOWLSubClassOfAxiom(cls(df, "Animal"), cls(df, "Dog")));
        assertFalse(r.isEntailed(set));
        assertTrue(r.isEntailed(Collections.<OWLAxiom>emptySet()));
    }
}
