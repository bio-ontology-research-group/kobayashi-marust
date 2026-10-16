package org.bioontology.kobayashimarust.protege;

import org.junit.Test;
import static org.junit.Assert.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.ReasonerInternalException;
import org.semanticweb.owl.explanation.api.Explanation;
import java.util.*;

/** Private adapter integration tests against the immutable c6 native binary. */
public class RetainedFunctionalSyntaxNativeTest {
    private final OWLDataFactory df=OWLManager.getOWLDataFactory();
    private OWLClass c(String name) {return df.getOWLClass(IRI.create("http://example.org/span-native#"+name));}
    private OWLSubClassOfAxiom sc(String a,String b){return df.getOWLSubClassOfAxiom(c(a),c(b));}
    private OWLOntology ontology() throws Exception {
        OWLOntology o=OWLManager.createOWLOntologyManager().createOntology(
                IRI.create("http://example.org/span-native"));
        for(String name:List.of("A","B","C","D"))
            o.getOWLOntologyManager().addAxiom(o,df.getOWLDeclarationAxiom(c(name)));
        return o;
    }
    private void expectSnapshot(KMReasoner r,OWLOntology o) {
        assertEquals(o.getAxioms(org.semanticweb.owlapi.model.parameters.Imports.INCLUDED),
                r.getCommittedOntologySnapshot().getAxioms());
    }

    @Test public void fastUpdatesRestoreEarlierNativeRevisionAndDetachedExplanationSnapshot() throws Exception {
        OWLOntology o=ontology();OWLOntologyManager m=o.getOWLOntologyManager();
        OWLAxiom disjoint=df.getOWLDisjointClassesAxiom(c("A"),c("D"));
        m.addAxiom(o,sc("A","B"));m.addAxiom(o,disjoint);
        KMReasoner r=(KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            OWLOntology old=r.getCommittedOntologySnapshot();
            m.addAxiom(o,sc("B","C"));m.removeAxiom(o,disjoint);r.flush();
            assertTrue(r.isEntailed(sc("A","C")));expectSnapshot(r,o);
            Set<Explanation<OWLAxiom>> explanations=r.createExplanationGenerator().getExplanations(sc("A","C"),1);
            assertEquals(1,explanations.size());
            assertEquals(Set.of(sc("A","B"),sc("B","C")),explanations.iterator().next().getAxioms());
            assertFalse(old.containsAxiom(sc("B","C")));assertTrue(old.containsAxiom(disjoint));
            m.removeAxiom(o,sc("B","C"));m.addAxiom(o,disjoint);r.flush();
            assertEquals("exact_reuse",r.getLastIncrementalReceipt().strategy);
            assertFalse(r.isEntailed(sc("A","C")));expectSnapshot(r,o);
            assertTrue(r.createExplanationGenerator().getExplanations(sc("A","C"),1).isEmpty());
            OWLOntology external=r.getCommittedOntologySnapshot();
            external.getOWLOntologyManager().addAxiom(external,sc("B","C"));
            assertFalse(r.getCommittedOntologySnapshot().containsAxiom(sc("B","C")));
        } finally {r.dispose();}
    }

    @Test public void actualNativeRefusalLeavesSourceCacheAndCommittedSnapshotThenRecovers() throws Exception {
        OWLOntology o=ontology();OWLOntologyManager m=o.getOWLOntologyManager();
        m.addAxiom(o,sc("A","B"));
        KMReasoner r=(KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.addAxiom(o,sc("B","C"));r.flush();expectSnapshot(r,o);
            OWLOntology committed=r.getCommittedOntologySnapshot();
            SWRLVariable x=df.getSWRLVariable(IRI.create("http://example.org/span-native#x"));
            SWRLRule unsupported=df.getSWRLRule(Collections.singleton(df.getSWRLBuiltInAtom(
                    IRI.create("http://example.org/unsupportedBuiltin"),Collections.singletonList(x))),
                    Collections.singleton(df.getSWRLClassAtom(c("B"),x)));
            m.addAxiom(o,unsupported);
            try{r.flush();fail("native accepted unsupported rule");}
            catch(ReasonerInternalException expected){assertNotNull(expected.getCause());}
            assertTrue(r.isEntailed(sc("A","C")));
            assertEquals(committed.getAxioms(),r.getCommittedOntologySnapshot().getAxioms());
            assertEquals(1,r.createExplanationGenerator().getExplanations(sc("A","C"),1).size());
            m.removeAxiom(o,unsupported);m.addAxiom(o,sc("C","D"));r.flush();
            assertTrue(r.isEntailed(sc("A","D")));expectSnapshot(r,o);
            assertEquals("full_classify",r.getLastIncrementalReceipt().strategy);
            assertEquals(1L,r.getLastIncrementalReceipt().revision);
            assertEquals(Set.of(sc("A","B"),sc("B","C"),sc("C","D")),
                    r.createExplanationGenerator().getExplanations(sc("A","D"),1).iterator().next().getAxioms());
        } finally {r.dispose();}
    }

    @Test public void importedSupportedDeltaAndSignatureFallbackKeepSnapshotExact() throws Exception {
        OWLOntology o=ontology();OWLOntologyManager m=o.getOWLOntologyManager();
        OWLOntology imported=m.createOntology(IRI.create("http://example.org/span-import"));
        m.addAxiom(imported,sc("A","B"));
        m.applyChange(new AddImport(o,df.getOWLImportsDeclaration(IRI.create("http://example.org/span-import"))));
        KMReasoner r=(KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            m.addAxiom(imported,sc("B","C"));r.flush();
            assertTrue(r.isEntailed(sc("A","C")));expectSnapshot(r,o);
            m.addAxiom(imported,sc("C","NewClass"));r.flush();
            assertTrue(r.isEntailed(sc("A","NewClass")));expectSnapshot(r,o);
            m.removeAxiom(imported,sc("C","NewClass"));r.flush();
            assertFalse(r.getCommittedOntologySnapshot().getClassesInSignature().contains(c("NewClass")));
            expectSnapshot(r,o);
        } finally {r.dispose();}
    }

    @Test public void capturedAssertionsComplexRolesAndDataDeleteRestoreMatchFreshNativeAnswers() throws Exception {
        OWLOntology o=ontology();OWLOntologyManager m=o.getOWLOntologyManager();
        OWLObjectProperty p=df.getOWLObjectProperty(IRI.create("http://example.org/span-native#p"));
        OWLDataProperty d=df.getOWLDataProperty(IRI.create("http://example.org/span-native#d"));
        OWLNamedIndividual a=df.getOWLNamedIndividual(IRI.create("http://example.org/span-native#a"));
        for(OWLEntity e:Arrays.asList(p,d,a,df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#string"))))
            m.addAxiom(o,df.getOWLDeclarationAxiom(e));
        Set<OWLAxiom> captured=Set.of(df.getOWLClassAssertionAxiom(c("A"),a),
                df.getOWLSubClassOfAxiom(c("C"),df.getOWLObjectSomeValuesFrom(p,c("D"))),
                df.getOWLObjectPropertyAssertionAxiom(p,a,a),df.getOWLDataPropertyAssertionAxiom(d,a,"v"));
        m.addAxiom(o,sc("A","B"));m.addAxioms(o,captured);
        KMReasoner r=(KMReasoner)new KMReasonerFactory().createReasoner(o);
        try {
            OWLOntology original=r.getCommittedOntologySnapshot();
            m.removeAxioms(o,captured);m.addAxiom(o,sc("B","C"));r.flush();
            assertTrue(r.isEntailed(sc("A","C")));expectSnapshot(r,o);sameFresh(r,o);
            assertEquals(captured.size()+1,original.getLogicalAxioms().size());
            m.removeAxiom(o,sc("B","C"));m.addAxioms(o,captured);r.flush();
            assertFalse(r.isEntailed(sc("A","C")));expectSnapshot(r,o);sameFresh(r,o);
            assertEquals(original.getAxioms(),r.getCommittedOntologySnapshot().getAxioms());
        } finally {r.dispose();}
    }

    private void sameFresh(KMReasoner retained,OWLOntology ontology) {
        KMReasoner fresh=(KMReasoner)new KMReasonerFactory().createReasoner(ontology);
        try {
            assertEquals(fresh.isConsistent(),retained.isConsistent());
            assertEquals(0,retained.getDroppedClauseCount());
            assertEquals(fresh.getUnsatisfiableClasses(),retained.getUnsatisfiableClasses());
            for(String name:List.of("A","B","C","D")) {
                assertEquals(fresh.getSuperClasses(c(name),false),retained.getSuperClasses(c(name),false));
                assertEquals(fresh.getEquivalentClasses(c(name)),retained.getEquivalentClasses(c(name)));
            }
        } finally {fresh.dispose();}
    }
}
