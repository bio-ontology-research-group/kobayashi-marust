package org.bioontology.kobayashimarust.protege;

import java.util.*;
import org.junit.Test;
import static org.junit.Assert.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.ReasonerInternalException;

public class SuppliedDeltaTest {
    private final OWLDataFactory df = OWLManager.getOWLDataFactory();
    private OWLClass c(String name) { return df.getOWLClass(IRI.create("urn:delta:" + name)); }
    private OWLAxiom sc(String a, String b) { return df.getOWLSubClassOfAxiom(c(a), c(b)); }
    private OWLOntology ontology() throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager().createOntology(IRI.create("urn:delta:ontology"));
        for (String name : List.of("A", "B", "C", "D"))
            o.getOWLOntologyManager().addAxiom(o, df.getOWLDeclarationAxiom(c(name)));
        o.getOWLOntologyManager().addAxiom(o, sc("A", "B"));
        return o;
    }
    private void snapshot(KMReasoner r, OWLOntology o) {
        assertEquals(o.getAxioms(Imports.INCLUDED), r.getCommittedOntologySnapshot().getAxioms());
    }
    private void sameRendering(OWLOntology o, String prepared) throws Exception {
        OWLOntology a = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new StringDocumentSource(prepared));
        OWLOntology b = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new StringDocumentSource(FlattenedOntology.functionalSyntax(o)));
        assertEquals(b.getAxioms(), a.getAxioms());
        assertEquals(b.getOntologyID(), a.getOntologyID());
    }
    private OWLAxiom refusedRule() {
        SWRLVariable x = df.getSWRLVariable(IRI.create("urn:delta:x"));
        return df.getSWRLRule(Set.of(df.getSWRLBuiltInAtom(IRI.create("urn:delta:unsupportedBuiltin"), List.of(x))),
                Set.of(df.getSWRLClassAtom(c("B"), x)));
    }
    private void refuses(KMReasoner r) {
        try { r.flush(); fail("unsupported native revision accepted"); }
        catch (ReasonerInternalException expected) { assertNotNull(expected.getCause()); }
    }

    @Test public void exactDeltaAvoidsFullCollectionAndMatchesOrdinaryRenderer() throws Exception {
        OWLOntology o = ontology(); RetainedFunctionalSyntax cache = new RetainedFunctionalSyntax();
        cache.commit(cache.prepare(o)); OWLAxiom added = sc("B", "C");
        o.getOWLOntologyManager().addAxiom(o, added);
        RetainedFunctionalSyntax.Prepared p = cache.prepare(o, Set.of(added), Set.of());
        assertTrue(p.usedSuppliedDelta); assertTrue(p.reused); sameRendering(o, p.source); cache.commit(p);
        o.getOWLOntologyManager().removeAxiom(o, added);
        p = cache.prepare(o, Set.of(), Set.of(added));
        assertTrue(p.usedSuppliedDelta); sameRendering(o, p.source);
    }
    @Test public void incorrectEffectiveMembershipFallsBack() throws Exception {
        OWLOntology o = ontology(); RetainedFunctionalSyntax cache = new RetainedFunctionalSyntax(); cache.commit(cache.prepare(o));
        OWLAxiom added = sc("B", "C"); o.getOWLOntologyManager().addAxiom(o, added);
        RetainedFunctionalSyntax.Prepared p = cache.prepare(o, Set.of(added), Set.of(sc("C", "D")));
        assertFalse(p.usedSuppliedDelta); sameRendering(o, p.source);
    }
    @Test public void bufferedDeltaAndEarlierRevisionRestorationReuse() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.addAxiom(o, sc("B", "C")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o);
            assertTrue(r.isEntailed(sc("A", "C")));
            m.removeAxiom(o, sc("B", "C")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o);
            assertFalse(r.isEntailed(sc("A", "C"))); assertEquals("exact_reuse", r.getLastIncrementalReceipt().strategy);
        } finally { r.dispose(); }
    }
    @Test public void refusedThenNoCallbackRetryAndRevertResynchronize() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o); OWLOntology accepted = r.getCommittedOntologySnapshot();
        try {
            OWLAxiom bad = refusedRule(); m.addAxiom(o, bad); refuses(r); refuses(r);
            // Base bookkeeping already equals the refused source; these cancel,
            // making its effective diff empty. Full retry must still occur.
            m.addAxiom(o, sc("B", "C")); m.removeAxiom(o, sc("B", "C")); refuses(r);
            assertEquals(accepted.getAxioms(), r.getCommittedOntologySnapshot().getAxioms());
            m.removeAxiom(o, bad); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o);
            m.addAxiom(o, sc("B", "C")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o);
            assertTrue(r.isEntailed(sc("A", "C")));
        } finally { r.dispose(); }
    }
    @Test public void nonBufferedChangesUseSameSynchronizedDeltaPath() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createNonBufferingReasoner(o);
        try {
            m.addAxiom(o, sc("B", "C")); assertTrue(r.lastPreparationUsedDelta()); assertTrue(r.isEntailed(sc("A", "C"))); snapshot(r, o);
            m.removeAxiom(o, sc("B", "C")); assertTrue(r.lastPreparationUsedDelta()); assertFalse(r.isEntailed(sc("A", "C"))); snapshot(r, o);
        } finally { r.dispose(); }
    }
    @Test public void importedDuplicateOwnershipUsesEffectiveNotRawDelta() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        OWLOntology imported = m.createOntology(IRI.create("urn:delta:import")); m.addAxiom(imported, sc("A", "B"));
        m.applyChange(new AddImport(o, df.getOWLImportsDeclaration(imported.getOntologyID().getOntologyIRI().get())));
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.removeAxiom(imported, sc("A", "B")); r.flush(); snapshot(r, o); assertTrue(r.isEntailed(sc("A", "B")));
            m.addAxiom(imported, sc("B", "C")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o);
            m.removeAxiom(o, sc("A", "B")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o); assertFalse(r.isEntailed(sc("A", "C")));
            m.addAxiom(imported, sc("A", "B")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o); assertTrue(r.isEntailed(sc("A", "C")));
        } finally { r.dispose(); }
    }
    @Test public void annotationOnlyBaseSkipForcesFullThenSafeDeltaResumes() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        OWLAnnotationProperty note = df.getOWLAnnotationProperty(IRI.create("urn:delta:note")); m.addAxiom(o, df.getOWLDeclarationAxiom(note));
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            OWLAxiom annotation = df.getOWLAnnotationAssertionAxiom(note, c("A").getIRI(), df.getOWLLiteral("note"));
            m.addAxiom(o, annotation); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o);
            m.addAxiom(o, sc("B", "C")); r.flush(); assertTrue(r.lastPreparationUsedDelta()); snapshot(r, o);
            m.removeAxiom(o, annotation); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o);
        } finally { r.dispose(); }
    }
    @Test public void annotatedInitialBaseNormalizationForcesSafeFallback() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager();
        OWLAnnotationProperty note = df.getOWLAnnotationProperty(IRI.create("urn:delta:note"));m.addAxiom(o, df.getOWLDeclarationAxiom(note));
        m.removeAxiom(o, sc("A", "B"));m.addAxiom(o, sc("A", "B").getAnnotatedAxiom(Set.of(df.getOWLAnnotation(note, df.getOWLLiteral("note")))));
        KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try { m.addAxiom(o, sc("B", "C")); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o); assertTrue(r.isEntailed(sc("A", "C"))); }
        finally { r.dispose(); }
    }
    @Test public void ontologyIdEmptyImportAndUnresolvedImportForceFull() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager(); KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.applyChange(new SetOntologyID(o, new OWLOntologyID(IRI.create("urn:delta:newid")))); r.flush(); assertFalse(r.lastPreparationUsedDelta()); assertEquals(o.getOntologyID(), r.getCommittedOntologySnapshot().getOntologyID());
            OWLOntology empty = m.createOntology(IRI.create("urn:delta:empty"));OWLImportsDeclaration imp = df.getOWLImportsDeclaration(IRI.create("urn:delta:empty"));m.applyChange(new AddImport(o, imp)); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o);
            OWLImportsDeclaration missing = df.getOWLImportsDeclaration(IRI.create("urn:delta:missing"));m.applyChange(new AddImport(o, missing)); refuses(r); assertFalse(r.getCommittedOntologySnapshot().getImportsDeclarations().contains(missing));
            m.applyChange(new RemoveImport(o, missing)); r.flush(); assertFalse(r.lastPreparationUsedDelta());snapshot(r, o);
        } finally { r.dispose(); }
    }
    @Test public void signatureAndDeclarationChangesStayOnFullFallback() throws Exception {
        OWLOntology o = ontology(); OWLOntologyManager m = o.getOWLOntologyManager(); KMReasoner r = (KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.addAxiom(o, sc("B", "NewClass")); r.flush(); assertFalse(r.lastPreparationUsedDelta()); snapshot(r, o);
            m.removeAxiom(o, df.getOWLDeclarationAxiom(c("D")));r.flush();assertFalse(r.lastPreparationUsedDelta());snapshot(r, o);
        } finally { r.dispose(); }
    }
}
