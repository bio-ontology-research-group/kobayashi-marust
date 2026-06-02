package org.bioontology.kobayashimarust.protege;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.io.File;
import java.util.Set;

import static org.junit.Assert.*;

/**
 * Headless tests driving the Kobayashi-MaRust reasoner through the OWL API
 * (no Protege GUI). Requires python3 + moose + the built engine binary, located
 * via the {@code km.home} system property (set to the repository root below).
 */
public class ReasonerTest {

    private static final String NS = "http://example.org/km#";

    @BeforeClass
    public static void locateRepo() {
        // protege/ module CWD -> repo root is the parent directory.
        if (System.getProperty("km.home") == null) {
            System.setProperty("km.home", new File("..").getAbsolutePath());
        }
    }

    private static OWLClass cls(OWLDataFactory df, String f) {
        return df.getOWLClass(IRI.create(NS + f));
    }

    private static OWLClass byFrag(OWLOntology o, String frag) {
        for (OWLClass c : o.getClassesInSignature()) {
            String s = c.getIRI().toString();
            String tail = s.contains("#") ? s.substring(s.lastIndexOf('#') + 1)
                                          : s.substring(s.lastIndexOf('/') + 1);
            if (tail.equals(frag)) return c;
        }
        throw new AssertionError("class not found: " + frag);
    }

    private static boolean superContains(OWLReasoner r, OWLClass sub, OWLClass sup) {
        return r.getSuperClasses(sub, false).containsEntity(sup);
    }

    /** Disjunctive subsumption: A ⊑ ∃-free B⊔C, B⊑D, C⊑D  ⊢  A ⊑ D. */
    @Test
    public void disjunctiveSubsumption() {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = m.getOWLDataFactory();
        try {
            OWLOntology o = m.createOntology(IRI.create(NS + "disj"));
            OWLClass A = cls(df, "A"), B = cls(df, "B"), C = cls(df, "C"), D = cls(df, "D");
            m.addAxiom(o, df.getOWLDeclarationAxiom(A));
            m.addAxiom(o, df.getOWLDeclarationAxiom(D));
            m.addAxiom(o, df.getOWLSubClassOfAxiom(A, df.getOWLObjectUnionOf(B, C)));
            m.addAxiom(o, df.getOWLSubClassOfAxiom(B, D));
            m.addAxiom(o, df.getOWLSubClassOfAxiom(C, D));

            OWLReasoner r = new KMReasonerFactory().createReasoner(o);
            assertTrue("ontology should be consistent", r.isConsistent());
            assertTrue("A ⊑ D (disjunctive)", superContains(r, A, D));
            assertTrue("reasoner name", r.getReasonerName().contains("Kobayashi"));
            r.dispose();
        } catch (OWLOntologyCreationException e) {
            throw new RuntimeException(e);
        }
    }

    /** Load the real kinship.ofn and check named subsumptions (matches HermiT). */
    @Test
    public void kinshipOfn() throws Exception {
        File ofn = new File(System.getProperty("km.home"),
                "examples/ontologies/kinship.ofn");
        org.junit.Assume.assumeTrue("kinship.ofn present", ofn.exists());
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLOntology o = m.loadOntologyFromOntologyDocument(ofn);

        OWLReasoner r = new KMReasonerFactory().createReasoner(o);
        assertTrue(r.isConsistent());
        OWLClass father = byFrag(o, "Father");
        Set<OWLClass> sup = r.getSuperClasses(father, false).getFlattened();
        for (String expect : new String[]{"Person", "Parent", "Male", "Narcissist"}) {
            assertTrue("Father ⊑ " + expect, sup.contains(byFrag(o, expect)));
        }
        r.dispose();
    }
}
