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
 * (no Protege GUI). Requires the built pure-Rust {@code km} binary.
 */
public class ReasonerTest {

    private static final String NS = "http://example.org/km#";

    @BeforeClass
    public static void locateKm() {
        if (System.getProperty("km.bin") == null) {
            File cached = new File(
                    "/home/leechuck/km-frontend/kobayashi-marust/engine/target/release/km");
            File local = new File("../engine/target/release/km");
            System.setProperty("km.bin",
                    (cached.isFile() ? cached : local).getAbsolutePath());
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
        File ofn = new File("../examples/ontologies/kinship.ofn");
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

    /** The active ontology's imports closure is classified as one ontology. */
    @Test
    public void importedAxiomsAreIncluded() throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = m.getOWLDataFactory();
        IRI importedIri = IRI.create(NS + "imported");
        OWLOntology imported = m.createOntology(importedIri);
        OWLClass a = cls(df, "ImportedA");
        OWLClass b = cls(df, "ImportedB");
        m.addAxiom(imported, df.getOWLSubClassOfAxiom(a, b));

        OWLOntology root = m.createOntology(IRI.create(NS + "root"));
        m.applyChange(new AddImport(root, df.getOWLImportsDeclaration(importedIri)));

        OWLReasoner r = new KMReasonerFactory().createReasoner(root);
        assertTrue("imported subclass axiom", superContains(r, a, b));
        r.dispose();
    }

    /** Missing imports fail instead of producing a partial hierarchy. */
    @Test
    public void unresolvedImportIsRejected() throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLOntology root = m.createOntology();
        m.applyChange(new AddImport(root, m.getOWLDataFactory()
                .getOWLImportsDeclaration(IRI.create(NS + "missing"))));

        try {
            new KMReasonerFactory().createReasoner(root);
            fail("unresolved import should fail");
        } catch (org.semanticweb.owlapi.reasoner.ReasonerInternalException expected) {
            assertTrue(expected.getCause().getMessage().contains("has not loaded"));
        }
    }

    /** Complete IRIs distinguish entities with the same local fragment. */
    @Test
    public void duplicateFragmentsRemainDistinct() throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = m.getOWLDataFactory();
        OWLOntology o = m.createOntology();
        OWLClass left = df.getOWLClass(IRI.create("http://left.example/Shared"));
        OWLClass right = df.getOWLClass(IRI.create("http://right.example/Shared"));
        OWLClass target = cls(df, "Target");
        m.addAxiom(o, df.getOWLSubClassOfAxiom(left, target));
        m.addAxiom(o, df.getOWLDeclarationAxiom(right));

        OWLReasoner r = new KMReasonerFactory().createReasoner(o);
        assertTrue(superContains(r, left, target));
        assertFalse(superContains(r, right, target));
        r.dispose();
    }
}
