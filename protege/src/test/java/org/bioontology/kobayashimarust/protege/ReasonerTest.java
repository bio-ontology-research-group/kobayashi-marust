package org.bioontology.kobayashimarust.protege;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.UnsupportedEntailmentTypeException;

import java.io.File;
import java.util.Collections;
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

    @Test
    public void entailmentSurfaceHonoursOwlTautologiesUnsatisfiabilityAndInconsistency()
            throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "EntailA");
        OWLClass b = cls(dataFactory, "EntailB");
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLNothing()));
        OWLReasoner reasoner = new KMReasonerFactory().createReasoner(ontology);
        assertTrue(reasoner.isEntailed(dataFactory.getOWLSubClassOfAxiom(a, b)));
        assertTrue(reasoner.isEntailed(dataFactory.getOWLSubClassOfAxiom(a, a)));
        assertTrue(reasoner.isEntailed(dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLNothing(), b)));
        assertTrue(reasoner.isEntailed(dataFactory.getOWLSubClassOfAxiom(
                b, dataFactory.getOWLThing())));
        try {
            reasoner.isEntailed(dataFactory.getOWLSubClassOfAxiom(
                    dataFactory.getOWLObjectIntersectionOf(a, b), b));
            fail("anonymous subclass query should fail explicitly");
        } catch (UnsupportedEntailmentTypeException expected) {
            assertEquals(expected.getAxiom(), dataFactory.getOWLSubClassOfAxiom(
                    dataFactory.getOWLObjectIntersectionOf(a, b), b));
        }
        reasoner.dispose();

        OWLOntology inconsistent = manager.createOntology();
        manager.addAxiom(inconsistent, dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLThing(), dataFactory.getOWLNothing()));
        OWLReasoner inconsistentReasoner =
                new KMReasonerFactory().createReasoner(inconsistent);
        assertFalse(inconsistentReasoner.isConsistent());
        assertTrue(inconsistentReasoner.isEntailed(
                dataFactory.getOWLSubClassOfAxiom(a, b)));
        inconsistentReasoner.dispose();
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

    @Test
    public void successiveSnapshotsPreserveIdentityAndAnnotatedImportsClosure() throws Exception {
        for (boolean anonymous : new boolean[]{false, true}) {
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            OWLDataFactory df = manager.getOWLDataFactory();
            OWLOntology ontology = anonymous
                    ? manager.createOntology(new OWLOntologyID())
                    : manager.createOntology(IRI.create(NS.substring(0, NS.length() - 1)));
            assertEquals(anonymous, ontology.getOntologyID().isAnonymous());
            OWLOntology imported = manager.createOntology(IRI.create(NS + "snapshotImport"));
            manager.applyChange(new AddImport(ontology,
                    df.getOWLImportsDeclaration(imported.getOntologyID().getOntologyIRI().get())));
            OWLClass a = cls(df, "SnapshotA"), b = cls(df, "SnapshotB");
            OWLClass c = cls(df, "SnapshotC"), x = cls(df, "SnapshotX"), y = cls(df, "SnapshotY");
            for (OWLClass cls : new OWLClass[]{a, b, c}) {
                manager.addAxiom(ontology, df.getOWLDeclarationAxiom(cls));
            }
            for (OWLClass cls : new OWLClass[]{x, y}) {
                manager.addAxiom(imported, df.getOWLDeclarationAxiom(cls));
            }
            OWLAnnotation rootNote = df.getOWLAnnotation(df.getRDFSComment(), df.getOWLLiteral("root axiom"));
            OWLAnnotation importNote = df.getOWLAnnotation(df.getRDFSComment(), df.getOWLLiteral("import axiom"));
            OWLAxiom rootAxiom = df.getOWLSubClassOfAxiom(a, b, Collections.singleton(rootNote));
            OWLAxiom importedAxiom = df.getOWLSubClassOfAxiom(x, y, Collections.singleton(importNote));
            OWLAxiom label = df.getOWLAnnotationAssertionAxiom(
                    df.getRDFSLabel(), x.getIRI(), df.getOWLLiteral("imported label"));
            manager.addAxiom(ontology, rootAxiom);
            manager.addAxiom(imported, importedAxiom);
            manager.addAxiom(imported, label);

            OWLOntology first = FlattenedOntology.snapshot(ontology);
            String firstSource = FlattenedOntology.functionalSyntaxOfSnapshot(first);
            assertEquals(ontology.getOntologyID(), first.getOntologyID());
            assertEquals(ontology.getAxioms(Imports.INCLUDED), first.getAxioms());
            assertTrue(first.getImportsDeclarations().isEmpty());
            assertFalse("native answers must use full entity IRIs", firstSource.contains("Prefix("));
            assertTrue(firstSource.contains("Class(<" + a.getIRI() + ">)"));
            OWLOntology roundtrip = OWLManager.createOWLOntologyManager()
                    .loadOntologyFromOntologyDocument(
                            new org.semanticweb.owlapi.io.StringDocumentSource(firstSource));
            assertEquals("full-IRI serialization preserves annotated closure axioms",
                    first.getAxioms(), roundtrip.getAxioms());

            OWLAxiom addition = df.getOWLSubClassOfAxiom(b, c);
            manager.addAxiom(ontology, addition);
            OWLOntology second = FlattenedOntology.snapshot(ontology);
            String secondSource = FlattenedOntology.functionalSyntaxOfSnapshot(second);
            assertEquals(ontology.getOntologyID(), second.getOntologyID());
            assertEquals(ontology.getAxioms(Imports.INCLUDED), second.getAxioms());
            assertTrue(second.containsAxiom(rootAxiom));
            assertTrue(second.containsAxiom(importedAxiom));
            assertTrue(second.containsAxiom(label));
            assertFalse("snapshots must remain detached", first.containsAxiom(addition));
            int firstBody = firstSource.indexOf('\n', firstSource.indexOf("Ontology("));
            int secondBody = secondSource.indexOf('\n', secondSource.indexOf("Ontology("));
            assertTrue(firstBody > 0 && secondBody > 0);
            assertEquals("prefixes and ontology identity must stay stable",
                    firstSource.substring(0, firstBody), secondSource.substring(0, secondBody));
        }
    }

    @Test
    public void bufferingFlushUsesNativeIncrementalSession() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(df, "IncrementalA");
        OWLClass b = cls(df, "IncrementalB");
        OWLClass c = cls(df, "IncrementalC");
        OWLClass x = cls(df, "UnchangedX");
        OWLClass y = cls(df, "UnchangedY");
        manager.addAxiom(ontology, df.getOWLSubClassOfAxiom(a, b));
        manager.addAxiom(ontology, df.getOWLDeclarationAxiom(c));
        manager.addAxiom(ontology, df.getOWLSubClassOfAxiom(x, y));

        KMReasoner reasoner = (KMReasoner) new KMReasonerFactory().createReasoner(ontology);
        assertEquals(BufferingMode.BUFFERING, reasoner.getBufferingMode());
        assertFalse(superContains(reasoner, a, c));
        assertTrue(superContains(reasoner, x, y));
        assertEquals(1L, reasoner.getLastIncrementalReceipt().revision);

        OWLAxiom addition = df.getOWLSubClassOfAxiom(b, c);
        manager.addAxiom(ontology, addition);
        assertTrue(reasoner.getPendingAxiomAdditions().contains(addition));
        assertFalse(reasoner.getCommittedOntologySnapshot().containsAxiom(addition));
        assertFalse("buffered change must not leak before flush",
                superContains(reasoner, a, c));

        reasoner.flush();
        assertTrue(superContains(reasoner, a, c));
        assertTrue("the independent component remains exact", superContains(reasoner, x, y));
        assertTrue(reasoner.getCommittedOntologySnapshot().containsAxiom(addition));
        assertTrue(reasoner.getPendingChanges().isEmpty());
        Classifier.IncrementalReceipt receipt = reasoner.getLastIncrementalReceipt();
        assertNotNull(receipt);
        assertEquals("common_module_reuse", receipt.strategy);
        assertEquals(2L, receipt.revision);
        assertTrue(receipt.meaningful_incremental_update);
        assertTrue("the independent component's published row must actually be retained",
                receipt.reused_subjects > 0);
        assertTrue("the changed component must be reclassified", receipt.reclassified_subjects > 0);
        assertTrue("source delta counters must be verified", receipt.statement_delta_verified);
        assertEquals(1L, receipt.added_axioms);
        assertEquals(0L, receipt.removed_axioms);
        assertTrue(receipt.module_axioms > 0);
        assertTrue(receipt.rebuilt_index_axioms > 0);
        assertEquals("building a union index does not reuse old index work", 0L,
                receipt.reused_index_axioms);
        assertEquals("module classification does not resume a backend fixpoint", 0L,
                receipt.resumed_backend_states);
        assertEquals("legacy state counters must not invent retained backend work", 0,
                receipt.retained_states);
        assertFalse(receipt.reused_complete_answer);
        reasoner.dispose();
    }

    @Test
    public void incrementalReceiptPreservesCompilerCountersAndLegacyAbsence() {
        com.google.gson.Gson gson = new com.google.gson.Gson();
        Classifier.IncrementalReceipt current = gson.fromJson(
                "{\"strategy\":\"full_classify\",\"meaningful_incremental_update\":true,"
                + "\"index_build_calls\":2,\"index_build_failures\":0,"
                + "\"cross_revision_compiled_axioms\":4000000000,\"same_update_compiled_axioms\":3,"
                + "\"compiled_locality_axioms\":4,\"csr_axiom_records\":5,"
                + "\"csr_conjunctions\":6,\"csr_literal_records\":7}",
                Classifier.IncrementalReceipt.class);
        assertEquals("full_classify", current.strategy);
        assertTrue(current.meaningful_incremental_update);
        assertEquals(Long.valueOf(2), current.index_build_calls);
        assertEquals(Long.valueOf(0), current.index_build_failures);
        assertEquals(Long.valueOf(4000000000L), current.cross_revision_compiled_axioms);
        assertEquals(Long.valueOf(3), current.same_update_compiled_axioms);
        assertEquals(Long.valueOf(4), current.compiled_locality_axioms);
        assertEquals(Long.valueOf(5), current.csr_axiom_records);
        assertEquals(Long.valueOf(6), current.csr_conjunctions);
        assertEquals(Long.valueOf(7), current.csr_literal_records);
        assertEquals(0L, current.reused_subjects);
        assertEquals(0L, current.resumed_backend_states);

        Classifier.IncrementalReceipt legacy = gson.fromJson(
                "{\"revision\":5,\"strategy\":\"el_delta\",\"retained_states\":7}",
                Classifier.IncrementalReceipt.class);
        assertEquals(5L, legacy.revision);
        assertEquals("el_delta", legacy.strategy);
        assertEquals(7, legacy.retained_states);
        assertNull(legacy.index_build_calls);
        assertNull(legacy.index_build_failures);
        assertNull(legacy.cross_revision_compiled_axioms);
        assertNull(legacy.same_update_compiled_axioms);
        assertNull(legacy.compiled_locality_axioms);
        assertNull(legacy.csr_axiom_records);
        assertNull(legacy.csr_conjunctions);
        assertNull(legacy.csr_literal_records);
    }

    @Test
    public void nativeReceiptRevisionSurvivesRejectedReplacement() throws Exception {
        String declarations = "Declaration(Class(<urn:receipt:A>)) "
                + "Declaration(Class(<urn:receipt:B>)) Declaration(Class(<urn:receipt:C>)) ";
        String initial = "Ontology(" + declarations
                + "SubClassOf(<urn:receipt:A> <urn:receipt:B>))";
        String extended = "Ontology(" + declarations
                + "SubClassOf(<urn:receipt:A> <urn:receipt:B>) "
                + "SubClassOf(<urn:receipt:B> <urn:receipt:C>))";
        try (Classifier.Session session = new Classifier.Session(initial)) {
            assertEquals(1L, session.receipt().revision);
            Classifier.Result committed = session.replace(extended);
            Classifier.IncrementalReceipt receipt = session.receipt();
            assertEquals(2L, receipt.revision);
            try {
                session.replace("Ontology(Declaration(Class(<urn:receipt:A>)) "
                        + "SubClassOf(<urn:receipt:A> <urn:receipt:Missing>))");
                fail("an undeclared nonbuiltin class must be rejected");
            } catch (RuntimeException expected) {
                assertTrue(expected.getMessage().contains("no matching declaration"));
            }
            assertSame("rejection must preserve the last committed answer", committed, session.result());
            assertSame("rejection must preserve its receipt and revision", receipt, session.receipt());
            session.replace(extended);
            assertEquals("only successful transactions advance the native revision", 3L,
                    session.receipt().revision);
            assertEquals("exact_reuse", session.receipt().strategy);
            assertTrue(session.receipt().reused_complete_answer);
            assertEquals(0L, session.receipt().resumed_backend_states);
        }
    }

    @Test
    public void nonBufferingReasonerCommitsOntologyChangesImmediately() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(df, "ImmediateA");
        OWLClass b = cls(df, "ImmediateB");
        OWLClass c = cls(df, "ImmediateC");
        manager.addAxiom(ontology, df.getOWLSubClassOfAxiom(a, b));

        KMReasoner reasoner = (KMReasoner) new KMReasonerFactory()
                .createNonBufferingReasoner(ontology);
        assertEquals(BufferingMode.NON_BUFFERING, reasoner.getBufferingMode());
        manager.addAxiom(ontology, df.getOWLSubClassOfAxiom(b, c));
        assertTrue(superContains(reasoner, a, c));
        assertTrue(reasoner.getPendingChanges().isEmpty());
        assertNotNull(reasoner.getLastIncrementalReceipt());
        reasoner.dispose();
    }

    @Test
    public void failedBufferedTransactionRetainsAnswersAndLaterFlushRecovers()
            throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(df, "RollbackA");
        OWLClass b = cls(df, "RollbackB");
        OWLClass c = cls(df, "RollbackC");
        OWLAxiom initial = df.getOWLSubClassOfAxiom(a, b);
        manager.addAxiom(ontology, initial);

        KMReasoner reasoner = (KMReasoner) new KMReasonerFactory()
                .createReasoner(ontology);
        assertTrue(superContains(reasoner, a, b));
        OWLOntology committedBefore = reasoner.getCommittedOntologySnapshot();

        SWRLVariable variable = df.getSWRLVariable(IRI.create(NS + "rollbackVariable"));
        SWRLBuiltInAtom unsupported = df.getSWRLBuiltInAtom(
                IRI.create("http://example.org/unsupportedBuiltin"),
                Collections.singletonList(variable));
        SWRLClassAtom head = df.getSWRLClassAtom(b, variable);
        SWRLRule rule = df.getSWRLRule(
                Collections.singleton(unsupported), Collections.singleton(head));
        manager.addAxiom(ontology, rule);
        try {
            reasoner.flush();
            fail("unsupported incremental source should fail atomically");
        } catch (org.semanticweb.owlapi.reasoner.ReasonerInternalException expected) {
            assertNotNull(expected.getCause());
        }
        assertTrue("last committed hierarchy must remain queryable",
                superContains(reasoner, a, b));
        assertEquals(committedBefore.getAxioms(),
                reasoner.getCommittedOntologySnapshot().getAxioms());

        manager.removeAxiom(ontology, rule);
        OWLAxiom valid = df.getOWLSubClassOfAxiom(b, c);
        manager.addAxiom(ontology, valid);
        reasoner.flush();
        assertTrue("a clean session must recover after the failed transaction",
                superContains(reasoner, a, c));
        assertTrue(reasoner.getCommittedOntologySnapshot().containsAxiom(valid));
        Classifier.IncrementalReceipt restarted = reasoner.getLastIncrementalReceipt();
        assertNotNull(restarted);
        assertEquals("full_classify", restarted.strategy);
        assertEquals("a restarted native session starts its own revision sequence", 1L,
                restarted.revision);
        assertFalse("a restarted native session must not claim retained delta work",
                restarted.meaningful_incremental_update);
        assertEquals(0L, restarted.reused_subjects);
        assertEquals(0L, restarted.resumed_backend_states);
        assertFalse(restarted.reused_complete_answer);
        reasoner.dispose();
    }
}
