package org.bioontology.kobayashimarust.protege;

import org.junit.Test;
import static org.junit.Assert.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import java.util.*;

/** Reasoner-free parser/renderer equivalence and transactional cache tests. */
public class RetainedFunctionalSyntaxTest {
    private static final String NS = "http://example.org/span#";
    private final OWLDataFactory df = OWLManager.getOWLDataFactory();
    private OWLClass c(String name) { return df.getOWLClass(IRI.create(NS + name)); }
    private OWLSubClassOfAxiom sc(String a, String b) {
        return df.getOWLSubClassOfAxiom(c(a), c(b));
    }
    private OWLOntology ontology() throws Exception {
        return OWLManager.createOWLOntologyManager().createOntology(IRI.create(NS+"ontology"));
    }
    private void add(OWLOntology o, OWLAxiom... axioms) {
        o.getOWLOntologyManager().addAxioms(o, new HashSet<>(Arrays.asList(axioms)));
    }
    private void remove(OWLOntology o, OWLAxiom... axioms) {
        o.getOWLOntologyManager().removeAxioms(o, new HashSet<>(Arrays.asList(axioms)));
    }
    private void declared(OWLOntology o, String... names) {
        for (String name : names) add(o, df.getOWLDeclarationAxiom(c(name)));
    }
    private OWLOntology parse(String text) throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        // Match the public worker's stable anonymous-ID parser setting, so
        // equality checks also verify shared versus distinct blank nodes.
        try {
            Object configurator = OWLOntologyManager.class.getMethod("getOntologyConfigurator").invoke(manager);
            configurator.getClass().getMethod("withRemapAllAnonymousIndividualsIds", boolean.class)
                    .invoke(configurator, false);
        } catch (NoSuchMethodException legacy) {
            Class.forName("org.semanticweb.owlapi.io.AnonymousIndividualProperties")
                    .getMethod("setRemapAllAnonymousIndividualsIds", boolean.class).invoke(null, false);
        }
        return manager.loadOntologyFromOntologyDocument(new StringDocumentSource(text));
    }
    private void parity(OWLOntology root, RetainedFunctionalSyntax.Prepared prepared) throws Exception {
        // Compare to the actual normal renderer's parsed output, including all
        // generated declarations, not just the original source axiom set.
        String ordinary = FlattenedOntology.functionalSyntax(root);
        OWLOntology expected = parse(ordinary);
        OWLOntology actual = parse(prepared.source);
        assertEquals(expected.getOntologyID(), actual.getOntologyID());
        assertEquals(expected.getAxioms(), actual.getAxioms());
        assertEquals(expected.getSignature(), actual.getSignature());
    }

    @Test public void initialCaptureIsTransparentIncludingNestedAnnotationsAndUnicode() throws Exception {
        OWLOntology o = ontology();
        OWLAnnotation inner = df.getOWLAnnotation(df.getRDFSComment(), df.getOWLLiteral("π ) #\n\"x\""));
        OWLAnnotation nested = df.getOWLAnnotation(df.getRDFSLabel(), df.getOWLLiteral("outer"),
                Collections.singleton(inner));
        add(o, sc("A", "B").getAnnotatedAxiom(Collections.singleton(nested)),
                df.getOWLDisjointClassesAxiom(c("A"),c("B"),c("C")),
                df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(), c("A").getIRI(),
                        df.getOWLLiteral("A ) # entity")));
        RetainedFunctionalSyntax cache = new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared p = cache.prepare(o);
        assertFalse(p.reused);
        assertNotNull(p.fallbackSnapshot);
        assertEquals(FlattenedOntology.functionalSyntax(o), p.source);
        parity(o,p);
    }

    @Test public void additionsDeletionAndOriginRestorationMatchNormalReparse() throws Exception {
        OWLOntology o = ontology();
        declared(o,"A","B","C","D");
        OWLAxiom disjoint = df.getOWLDisjointClassesAxiom(c("A"),c("C"),c("D"));
        add(o,sc("A","B"),disjoint);
        RetainedFunctionalSyntax cache = new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared initial = cache.prepare(o);
        cache.commit(initial);
        remove(o,disjoint,sc("A","B")); add(o,sc("B","C"));
        RetainedFunctionalSyntax.Prepared p = cache.prepare(o);
        assertTrue(p.reused); assertNull(p.fallbackSnapshot);
        assertEquals(1,p.added.size()); assertEquals(2,p.removed.size());
        parity(o,p); cache.commit(p);
        remove(o,sc("B","C")); add(o,disjoint,sc("A","B"));
        RetainedFunctionalSyntax.Prepared restored = cache.prepare(o);
        assertTrue(restored.reused);
        assertEquals("origin text restored exactly",initial.source,restored.source);
        parity(o,restored); cache.commit(restored);
        for(int i=0;i<80;i++) {
            OWLSubClassOfAxiom edge = sc(i%2==0?"B":"C","D");
            OWLSubClassOfAxiom other = sc(i%2==0?"C":"B","D");
            remove(o,other); add(o,edge);
            p=cache.prepare(o); assertTrue(p.reused); parity(o,p); cache.commit(p);
        }
    }

    @Test public void generatedDeclarationsFollowLastEntityRemoval() throws Exception {
        OWLOntology o=ontology(); add(o,sc("A","B"),sc("B","C"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();
        cache.commit(cache.prepare(o));
        add(o,sc("A","C"));
        RetainedFunctionalSyntax.Prepared p=cache.prepare(o);
        assertTrue(p.reused); parity(o,p); cache.commit(p);
        remove(o,sc("A","B"),sc("A","C"));
        p=cache.prepare(o); assertTrue(p.reused); parity(o,p);
        assertFalse(parse(p.source).getSignature().contains(c("A")));
    }

    @Test public void unsupportedAnnotationsNewDisjointAndIdChangesFallBack() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B","C"); add(o,sc("A","B"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(o));
        OWLAxiom annotated=sc("B","C").getAnnotatedAxiom(Collections.singleton(
                df.getOWLAnnotation(df.getRDFSComment(),df.getOWLLiteral("x"))));
        add(o,annotated); RetainedFunctionalSyntax.Prepared p=cache.prepare(o);
        assertFalse(p.reused); parity(o,p); cache.commit(p);
        OWLAxiom novel=df.getOWLDisjointClassesAxiom(c("B"),c("C")); add(o,novel);
        p=cache.prepare(o); assertFalse(p.reused); parity(o,p);cache.commit(p);
        o.getOWLOntologyManager().applyChange(new SetOntologyID(o,new OWLOntologyID(IRI.create(NS+"new"))));
        p=cache.prepare(o);assertFalse(p.reused);parity(o,p);
    }

    @Test public void typedPunningAndFullIrisArePreserved() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B");
        OWLClass other=df.getOWLClass(IRI.create("http://other.example/#A"));
        add(o,df.getOWLDeclarationAxiom(other),df.getOWLSubClassOfAxiom(c("A"),other));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(o));
        add(o,df.getOWLSubClassOfAxiom(other,c("B")));
        RetainedFunctionalSyntax.Prepared p=cache.prepare(o);assertTrue(p.reused);parity(o,p);cache.commit(p);
        add(o,df.getOWLDeclarationAxiom(df.getOWLObjectProperty(c("A").getIRI())));
        p=cache.prepare(o);assertFalse(p.reused);parity(o,p);
    }

    @Test public void importsValidatedBeforeReuseAndFlattenedInputRemainsExact() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B","C");
        OWLOntology imported=o.getOWLOntologyManager().createOntology(IRI.create(NS+"import"));
        add(imported,sc("A","B"));
        OWLImportsDeclaration declaration=df.getOWLImportsDeclaration(IRI.create(NS+"import"));
        o.getOWLOntologyManager().applyChange(new AddImport(o,declaration));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(o));
        add(imported,sc("B","C"));
        RetainedFunctionalSyntax.Prepared p=cache.prepare(o);assertTrue(p.reused);parity(o,p);cache.commit(p);
        o.getOWLOntologyManager().applyChange(new AddImport(o,
                df.getOWLImportsDeclaration(IRI.create(NS+"unresolved"))));
        try {cache.prepare(o);fail("unresolved import accepted");}
        catch(IllegalStateException expected){assertTrue(expected.getMessage().contains("has not loaded"));}
        o.getOWLOntologyManager().applyChange(new RemoveImport(o,
                df.getOWLImportsDeclaration(IRI.create(NS+"unresolved"))));
        p=cache.prepare(o);assertTrue(p.reused);assertTrue(p.added.isEmpty());parity(o,p);
    }

    @Test public void discardedCandidateModelsNativeRefusalAndCommitIsAtomic() throws Exception {
        OWLOntology o=ontology();declared(o,"A","B","C");add(o,sc("A","B"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o);cache.commit(initial);
        add(o,sc("B","C"));
        RetainedFunctionalSyntax.Prepared refused=cache.prepare(o);
        // Native refusal/exception: caller deliberately does not commit.
        remove(o,sc("B","C"));
        RetainedFunctionalSyntax.Prepared after=cache.prepare(o);
        assertEquals(initial.source,after.source);assertTrue(after.added.isEmpty());parity(o,after);
        try{after.added.add(sc("B","C"));fail("mutable delta");}
        catch(UnsupportedOperationException expected){}
        cache.commit(after);
        try{cache.commit(refused);fail("stale commit accepted");}
        catch(IllegalStateException expected){}
        try{new RetainedFunctionalSyntax().commit(after);fail("foreign commit accepted");}
        catch(IllegalStateException expected){}
        try{parse("Ontology( SubClassOf(");fail("malformed source accepted");}
        catch(OWLOntologyCreationException expected){}
        after=cache.prepare(o);assertEquals(initial.source,after.source);
    }

    @Test public void captureIneligibilityUsesOrdinaryRendererWithoutRejectingOntology() throws Exception {
        OWLOntology o=ontology();add(o,sc("A","B"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax() {
            @Override Capture createCapture(OWLOntology ignored) {
                throw new CaptureIneligible("forced capture limitation");
            }
        };
        RetainedFunctionalSyntax.Prepared p=cache.prepare(o);
        assertFalse(p.reused);assertEquals(FlattenedOntology.functionalSyntax(o),p.source);
        parity(o,p);cache.commit(p);
        add(o,sc("B","A"));p=cache.prepare(o);
        assertFalse(p.reused);assertEquals(FlattenedOntology.functionalSyntax(o),p.source);parity(o,p);
    }

    @Test public void unchangedRulesComplexAxiomsAndAnnotationsSurviveSplicing() throws Exception {
        OWLOntology o=ontology();declared(o,"A","B","C");
        SWRLVariable x=df.getSWRLVariable(IRI.create(NS+"x"));
        add(o,df.getSWRLRule(Collections.singleton(df.getSWRLClassAtom(c("A"),x)),
                Collections.singleton(df.getSWRLClassAtom(c("B"),x))),
                df.getOWLSubClassOfAxiom(c("A"),df.getOWLObjectUnionOf(c("B"),c("C"))),
                df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(),c("B").getIRI(),
                        df.getOWLLiteral("β ) #\ncomment")));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o);
        assertEquals(FlattenedOntology.functionalSyntax(o),initial.source);cache.commit(initial);
        add(o,sc("B","C"));RetainedFunctionalSyntax.Prepared p=cache.prepare(o);
        assertTrue(p.reused);parity(o,p);cache.commit(p);
        remove(o,sc("B","C"));p=cache.prepare(o);assertTrue(p.reused);
        assertEquals(initial.source,p.source);parity(o,p);
    }

    @Test public void preparedDomainAndDeltasAreFrozenAgainstSubsequentRootMutation() throws Exception {
        OWLOntology o=ontology();declared(o,"A","B","C");add(o,sc("A","B"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(o));
        add(o,sc("B","C"));RetainedFunctionalSyntax.Prepared p=cache.prepare(o);
        assertTrue(p.reused);assertNull(p.fallbackSnapshot);
        add(o,sc("C","Later"));remove(o,sc("B","C"));
        assertFalse(p.classes.contains(c("Later")));
        assertEquals(Collections.singleton(sc("B","C")),p.added);
        assertTrue(parse(p.source).containsAxiom(sc("B","C")));
        try{p.classes.add(c("Later"));fail("mutable domain");}
        catch(UnsupportedOperationException expected){}
        // This test deliberately never commits a preparation after a caller
        // races root changes; adapter synchronization owns that contract.
    }

    @Test public void inputAliasesAndFullIriVariantsUseSameResolvedAxioms() throws Exception {
        OWLOntology original=parse("Prefix(x:=<http://example.org/span#>) "
                +"Ontology(<http://example.org/span#ontology> "
                +"Declaration(Class(x:A)) Declaration(Class(x:B)) Declaration(Class(x:C)) "
                +"SubClassOf(x:A x:B) SubClassOf(x:B x:C))");
        OWLOntology updated=parse("Ontology(<http://example.org/span#ontology> "
                +"Declaration(Class(<http://example.org/span#A>)) "
                +"Declaration(Class(<http://example.org/span#B>)) "
                +"Declaration(Class(<http://example.org/span#C>)) "
                +"SubClassOf(<http://example.org/span#A> <http://example.org/span#B>) "
                +"SubClassOf(<http://example.org/span#B> <http://example.org/span#C>) "
                +"SubClassOf(<http://example.org/span#A> <http://example.org/span#C>))");
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(original));
        RetainedFunctionalSyntax.Prepared p=cache.prepare(updated);
        assertTrue(p.reused);assertEquals(Collections.singleton(sc("A","C")),p.added);
        assertTrue(p.source.contains("<http://example.org/span#A>"));parity(updated,p);
    }

    @Test public void capturedAnnotatedComplexAssertionRoleDataAndRuleAxiomsRestoreExactly() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B","C","D");
        OWLObjectProperty p=df.getOWLObjectProperty(IRI.create(NS+"p"));
        OWLObjectProperty q=df.getOWLObjectProperty(IRI.create(NS+"q"));
        OWLDataProperty d=df.getOWLDataProperty(IRI.create(NS+"d"));
        OWLNamedIndividual a=df.getOWLNamedIndividual(IRI.create(NS+"a"));
        OWLDatatype string=df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#string"));
        for(OWLEntity e:Arrays.asList(p,q,d,a,string,df.getRDFSLabel())) add(o,df.getOWLDeclarationAxiom(e));
        SWRLVariable x=df.getSWRLVariable(IRI.create(NS+"x"));
        Set<OWLAxiom> captured=new HashSet<>(Arrays.asList(
                sc("A","B").getAnnotatedAxiom(Collections.singleton(df.getOWLAnnotation(df.getRDFSLabel(),df.getOWLLiteral("origin")))),
                df.getOWLSubClassOfAxiom(c("C"),df.getOWLObjectSomeValuesFrom(p,c("D"))),
                df.getOWLClassAssertionAxiom(c("A"),a), df.getOWLObjectPropertyAssertionAxiom(p,a,a),
                df.getOWLSubObjectPropertyOfAxiom(p,q), df.getOWLDataPropertyAssertionAxiom(d,a,"v"),
                df.getSWRLRule(Collections.singleton(df.getSWRLClassAtom(c("A"),x)),Collections.singleton(df.getSWRLClassAtom(c("B"),x))),
                df.getOWLAnnotationAssertionAxiom(df.getRDFSLabel(),c("A").getIRI(),df.getOWLLiteral("fixed span"))));
        o.getOWLOntologyManager().addAxioms(o,captured);
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o); parity(o,initial);cache.commit(initial);
        o.getOWLOntologyManager().removeAxioms(o,captured);add(o,sc("B","C"));
        RetainedFunctionalSyntax.Prepared changed=cache.prepare(o);assertTrue(changed.reused);parity(o,changed);cache.commit(changed);
        remove(o,sc("B","C"));o.getOWLOntologyManager().addAxioms(o,captured);
        RetainedFunctionalSyntax.Prepared restored=cache.prepare(o);assertTrue(restored.reused);
        assertEquals(initial.source,restored.source);parity(o,restored);
    }

    @Test public void capturedSharedAndDistinctAnonymousIndividualsKeepTheirIdentity() throws Exception {
        OWLOntology o=ontology();declared(o,"A","B");
        OWLObjectProperty p=df.getOWLObjectProperty(IRI.create(NS+"anonymousRole"));add(o,df.getOWLDeclarationAxiom(p));
        OWLAnonymousIndividual shared=df.getOWLAnonymousIndividual("shared"),distinct=df.getOWLAnonymousIndividual("distinct");
        Set<OWLAxiom> captured=new HashSet<>(Arrays.asList(df.getOWLClassAssertionAxiom(c("A"),shared),
                df.getOWLClassAssertionAxiom(c("B"),distinct),df.getOWLObjectPropertyAssertionAxiom(p,shared,distinct),
                df.getOWLObjectPropertyAssertionAxiom(p,distinct,shared)));
        o.getOWLOntologyManager().addAxioms(o,captured);
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();RetainedFunctionalSyntax.Prepared initial=cache.prepare(o);
        parity(o,initial);assertEquals(2,parse(initial.source).getAnonymousIndividuals().size());cache.commit(initial);
        remove(o,df.getOWLClassAssertionAxiom(c("A"),shared));
        RetainedFunctionalSyntax.Prepared partial=cache.prepare(o);assertTrue(partial.reused);parity(o,partial);cache.commit(partial);
        o.getOWLOntologyManager().removeAxioms(o,captured);
        RetainedFunctionalSyntax.Prepared empty=cache.prepare(o);assertTrue(empty.reused);parity(o,empty);cache.commit(empty);
        o.getOWLOntologyManager().addAxioms(o,captured);
        RetainedFunctionalSyntax.Prepared restored=cache.prepare(o);assertTrue(restored.reused);
        assertEquals(initial.source,restored.source);parity(o,restored);
        assertEquals(2,parse(restored.source).getAnonymousIndividuals().size());
    }

    @Test public void declarationRemovalAndNovelAnonymousComplexDataAxiomsUseNormalRendering() throws Exception {
        OWLOntology o=ontology();declared(o,"A","B","C");add(o,sc("A","B"));
        OWLDataProperty d=df.getOWLDataProperty(IRI.create(NS+"d"));
        OWLNamedIndividual a=df.getOWLNamedIndividual(IRI.create(NS+"a"));
        add(o,df.getOWLDeclarationAxiom(d),df.getOWLDeclarationAxiom(a),
                df.getOWLDeclarationAxiom(df.getOWLDatatype(IRI.create("http://www.w3.org/2001/XMLSchema#string"))));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();cache.commit(cache.prepare(o));
        OWLAxiom declaration=df.getOWLDeclarationAxiom(c("A"));remove(o,declaration);
        RetainedFunctionalSyntax.Prepared undeclared=cache.prepare(o);assertFalse(undeclared.reused);parity(o,undeclared);
        assertTrue("ordinary renderer supplies a synthetic declaration",parse(undeclared.source).containsAxiom(declaration));
        add(o,declaration);
        for(OWLAxiom novel:Arrays.asList(df.getOWLClassAssertionAxiom(c("A"),df.getOWLAnonymousIndividual("novel")),
                df.getOWLSubClassOfAxiom(c("A"),df.getOWLObjectComplementOf(c("B"))),
                df.getOWLDataPropertyAssertionAxiom(d,a,"new"))) {
            add(o,novel);RetainedFunctionalSyntax.Prepared prepared=cache.prepare(o);
            assertFalse(prepared.reused);parity(o,prepared);remove(o,novel);
        }
        RetainedFunctionalSyntax.Prepared unchanged=cache.prepare(o);assertTrue(unchanged.reused);parity(o,unchanged);
    }

    private static final class CountingSerializer extends RetainedFunctionalSyntax {
        int captures;
        @Override Capture createCapture(OWLOntology ontology) {
            captures++;
            return super.createCapture(ontology);
        }
    }

    @Test public void undeclaredIndividualsShrinkRestoreAndRepeatWithoutRecapture() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B"); add(o,sc("A","B"));
        Set<OWLAxiom> assertions=new HashSet<>();
        Set<OWLNamedIndividual> individuals=new HashSet<>();
        for(int i=0;i<22;i++) {
            OWLNamedIndividual individual=df.getOWLNamedIndividual(IRI.create(NS+"individual"+i));
            individuals.add(individual); assertions.add(df.getOWLClassAssertionAxiom(c("A"),individual));
            assertFalse(o.containsAxiom(df.getOWLDeclarationAxiom(individual)));
        }
        OWLNamedIndividual last=df.getOWLNamedIndividual(IRI.create(NS+"last"));
        OWLAxiom lastAssertion=df.getOWLClassAssertionAxiom(c("A"),last);
        o.getOWLOntologyManager().addAxioms(o,assertions); add(o,lastAssertion);
        CountingSerializer cache=new CountingSerializer();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o);
        assertEquals(FlattenedOntology.functionalSyntax(o),initial.source); cache.commit(initial);
        for(int cycle=0;cycle<2;cycle++) {
            o.getOWLOntologyManager().removeAxioms(o,assertions);
            RetainedFunctionalSyntax.Prepared shrunk=cache.prepare(o,Collections.emptySet(),assertions);
            assertTrue(shrunk.reused); assertTrue(shrunk.usedSuppliedDelta); parity(o,shrunk);
            OWLOntology parsed=parse(shrunk.source);
            for(OWLNamedIndividual individual:individuals) assertFalse(parsed.getSignature().contains(individual));
            assertTrue(parsed.getSignature().contains(last)); cache.commit(shrunk);
            remove(o,lastAssertion);
            RetainedFunctionalSyntax.Prepared empty=cache.prepare(o,Collections.emptySet(),Collections.singleton(lastAssertion));
            assertTrue(empty.reused); assertTrue(empty.usedSuppliedDelta); parity(o,empty);
            assertFalse(parse(empty.source).getSignature().contains(last)); cache.commit(empty);
            Set<OWLAxiom> restoredAxioms=new HashSet<>(assertions); restoredAxioms.add(lastAssertion);
            o.getOWLOntologyManager().addAxioms(o,restoredAxioms);
            RetainedFunctionalSyntax.Prepared restored=cache.prepare(o,restoredAxioms,Collections.emptySet());
            assertTrue(restored.reused); assertTrue(restored.usedSuppliedDelta); parity(o,restored);
            assertEquals(initial.source,restored.source); cache.commit(restored);
        }
        assertEquals("signature edits must keep the same immutable origin",1,cache.captures);
    }

    @Test public void syntheticDeclarationsFollowFullTypedSignatureIncludingPunning() throws Exception {
        OWLOntology o=ontology();
        OWLObjectProperty role=df.getOWLObjectProperty(c("Shared").getIRI());
        OWLDataProperty data=df.getOWLDataProperty(c("DataShared").getIRI());
        OWLDatatype datatype=df.getOWLDatatype(IRI.create(NS+"customDatatype"));
        OWLNamedIndividual individual=df.getOWLNamedIndividual(IRI.create(NS+"undeclared"));
        OWLAnnotationProperty annotation=df.getOWLAnnotationProperty(IRI.create(NS+"annotation"));
        OWLAxiom classEdge=sc("Shared","B");
        Set<OWLAxiom> removable=new HashSet<>(Arrays.asList(
                df.getOWLObjectPropertyDomainAxiom(role,c("A")),
                df.getOWLDataPropertyRangeAxiom(data,datatype),
                df.getOWLClassAssertionAxiom(c("A"),individual),
                df.getOWLAnnotationAssertionAxiom(annotation,c("Shared").getIRI(),df.getOWLLiteral("value"))));
        add(o,classEdge,sc("DataShared","B"),sc("A","B"));
        o.getOWLOntologyManager().addAxioms(o,removable);
        CountingSerializer cache=new CountingSerializer();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o); cache.commit(initial);
        o.getOWLOntologyManager().removeAxioms(o,removable);
        RetainedFunctionalSyntax.Prepared shrunk=cache.prepare(o);
        assertTrue(shrunk.reused); assertFalse(shrunk.usedSuppliedDelta); parity(o,shrunk);
        Set<OWLEntity> signature=parse(shrunk.source).getSignature();
        assertTrue(signature.contains(c("Shared"))); assertTrue(signature.contains(c("DataShared")));
        for(OWLEntity absent:Arrays.asList(role,data,datatype,individual,annotation)) assertFalse(signature.contains(absent));
        cache.commit(shrunk);
        o.getOWLOntologyManager().addAxioms(o,removable);
        RetainedFunctionalSyntax.Prepared restored=cache.prepare(o);
        assertTrue(restored.reused); assertEquals(initial.source,restored.source); parity(o,restored); cache.commit(restored);
        remove(o,classEdge);
        RetainedFunctionalSyntax.Prepared propertyOnly=cache.prepare(o,Collections.emptySet(),Collections.singleton(classEdge));
        assertTrue(propertyOnly.reused); parity(o,propertyOnly);
        signature=parse(propertyOnly.source).getSignature();
        assertFalse(signature.contains(c("Shared"))); assertTrue(signature.contains(role));
        assertFalse(propertyOnly.classes.contains(c("Shared"))); cache.commit(propertyOnly);
        add(o,classEdge); restored=cache.prepare(o);
        assertTrue(restored.reused); assertEquals(initial.source,restored.source); parity(o,restored);
        assertEquals(1,cache.captures);
    }

    @Test public void discardedSignatureShrinkDoesNotMutateTheCommittedOrigin() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B");
        OWLNamedIndividual individual=df.getOWLNamedIndividual(IRI.create(NS+"uncommitted"));
        OWLAxiom assertion=df.getOWLClassAssertionAxiom(c("A"),individual); add(o,assertion,sc("A","B"));
        CountingSerializer cache=new CountingSerializer();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o); cache.commit(initial);
        remove(o,assertion);
        RetainedFunctionalSyntax.Prepared refused=cache.prepare(o,Collections.emptySet(),Collections.singleton(assertion));
        assertTrue(refused.reused); assertFalse(parse(refused.source).getSignature().contains(individual)); parity(o,refused);
        // Model native refusal: do not commit the detached preparation.
        add(o,assertion);
        RetainedFunctionalSyntax.Prepared unchanged=cache.prepare(o,Collections.emptySet(),Collections.emptySet());
        assertTrue(unchanged.reused); assertEquals(initial.source,unchanged.source); parity(o,unchanged); cache.commit(unchanged);
        try {cache.commit(refused);fail("stale shrink committed");} catch(IllegalStateException expected) {}
        remove(o,assertion);
        RetainedFunctionalSyntax.Prepared accepted=cache.prepare(o);
        assertTrue(accepted.reused); parity(o,accepted); cache.commit(accepted);
        add(o,assertion); RetainedFunctionalSyntax.Prepared restored=cache.prepare(o);
        assertTrue(restored.reused); assertEquals(initial.source,restored.source); parity(o,restored);
        assertEquals(1,cache.captures);
    }

    @Test public void signatureExtensionAndExplicitDeclarationEditsStillUseNormalRendering() throws Exception {
        OWLOntology o=ontology(); declared(o,"A","B"); add(o,sc("A","B"));
        RetainedFunctionalSyntax cache=new RetainedFunctionalSyntax();
        RetainedFunctionalSyntax.Prepared initial=cache.prepare(o); cache.commit(initial);
        OWLAxiom novel=sc("B","NewEntity"); add(o,novel);
        RetainedFunctionalSyntax.Prepared extension=cache.prepare(o,Collections.singleton(novel),Collections.emptySet());
        assertFalse(extension.reused); assertEquals(FlattenedOntology.functionalSyntax(o),extension.source); parity(o,extension);
        remove(o,novel); assertEquals(initial.source,cache.prepare(o).source);
        OWLAxiom declaration=df.getOWLDeclarationAxiom(c("A")); remove(o,declaration);
        RetainedFunctionalSyntax.Prepared undeclared=cache.prepare(o,Collections.emptySet(),Collections.singleton(declaration));
        assertFalse(undeclared.reused); parity(o,undeclared);
        assertTrue(parse(undeclared.source).containsAxiom(declaration));
    }
}
