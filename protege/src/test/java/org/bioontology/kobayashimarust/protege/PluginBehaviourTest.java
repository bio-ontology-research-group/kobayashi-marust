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

    // ---- item 2: no wrong answers ------------------------------------

    @Test
    public void satisfiabilityOfAnAnonymousExpressionIsNotGuessed() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = dataFactory(o);
        KMReasoner r = km(o);
        OWLClassExpression anonymous = df.getOWLObjectIntersectionOf(cls(df, "Dog"), cls(df, "Cat"));
        try {
            r.isSatisfiable(anonymous);
            fail("an anonymous expression must not get a guessed answer");
        } catch (ClassExpressionNotInProfileException expected) {
            assertEquals(anonymous, expected.getClassExpression());
        }
        assertTrue(r.isSatisfiable(cls(df, "Dog")));
        assertTrue(r.isSatisfiable(df.getOWLThing()));
        assertFalse(r.isSatisfiable(df.getOWLNothing()));
    }

    @Test
    public void inverseOfAPropertyIsNeverItself() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = dataFactory(o);
        KMReasoner r = km(o);
        OWLObjectProperty owned = df.getOWLObjectProperty(IRI.create(NS + "ownedBy"));
        Set<OWLObjectPropertyExpression> inverse = r.getInverseObjectProperties(owned).getEntities();
        assertEquals(Collections.singleton(owned.getInverseProperty()), inverse);
        assertEquals(Collections.singleton(owned),
                r.getInverseObjectProperties(owned.getInverseProperty()).getEntities());
        assertEquals(Collections.singleton(df.getOWLTopObjectProperty()),
                r.getInverseObjectProperties(df.getOWLTopObjectProperty()).getEntities());
    }

    // ---- item 3: inconsistent ontology --------------------------------

    private interface Query { void run(OWLReasoner r) throws Exception; }

    /** Every query HermiT guards with checkPreConditions, as (name, call). */
    private static Map<String, Query> guardedQueries(OWLOntology o) {
        OWLDataFactory df = dataFactory(o);
        OWLClass dog = cls(df, "Dog");
        OWLNamedIndividual rex = ind(df, "rex");
        OWLObjectProperty owned = df.getOWLObjectProperty(IRI.create(NS + "ownedBy"));
        OWLDataProperty data = df.getOWLDataProperty(IRI.create(NS + "age"));
        Map<String, Query> q = new LinkedHashMap<>();
        q.put("isSatisfiable", r -> r.isSatisfiable(dog));
        q.put("getEquivalentClasses", r -> r.getEquivalentClasses(dog));
        q.put("getSuperClasses", r -> r.getSuperClasses(dog, false));
        q.put("getSubClasses", r -> r.getSubClasses(dog, true));
        q.put("getDisjointClasses", r -> r.getDisjointClasses(dog));
        q.put("getTypes", r -> r.getTypes(rex, false));
        q.put("getInstances", r -> r.getInstances(dog, false));
        q.put("getSameIndividuals", r -> r.getSameIndividuals(rex));
        q.put("getDifferentIndividuals", r -> r.getDifferentIndividuals(rex));
        q.put("getObjectPropertyValues", r -> r.getObjectPropertyValues(rex, owned));
        q.put("getDataPropertyValues", r -> r.getDataPropertyValues(rex, data));
        q.put("getSubObjectProperties", r -> r.getSubObjectProperties(owned, false));
        q.put("getSuperObjectProperties", r -> r.getSuperObjectProperties(owned, false));
        q.put("getEquivalentObjectProperties", r -> r.getEquivalentObjectProperties(owned));
        q.put("getInverseObjectProperties", r -> r.getInverseObjectProperties(owned));
        q.put("getDisjointObjectProperties", r -> r.getDisjointObjectProperties(owned));
        q.put("getObjectPropertyDomains", r -> r.getObjectPropertyDomains(owned, false));
        q.put("getObjectPropertyRanges", r -> r.getObjectPropertyRanges(owned, false));
        q.put("getSubDataProperties", r -> r.getSubDataProperties(data, false));
        q.put("getSuperDataProperties", r -> r.getSuperDataProperties(data, false));
        q.put("getEquivalentDataProperties", r -> r.getEquivalentDataProperties(data));
        q.put("getDisjointDataProperties", r -> r.getDisjointDataProperties(data));
        q.put("getDataPropertyDomains", r -> r.getDataPropertyDomains(data, false));
        q.put("isEntailed", r -> r.isEntailed(df.getOWLSubClassOfAxiom(dog, cls(df, "Animal"))));
        q.put("isEntailedSet", r -> r.isEntailed(Collections.singleton(
                df.getOWLSubClassOfAxiom(dog, cls(df, "Animal")))));
        q.put("precomputeInferences", r -> r.precomputeInferences(InferenceType.CLASS_HIERARCHY));
        return q;
    }

    private static boolean throwsInconsistent(Query query, OWLReasoner r) throws Exception {
        try {
            query.run(r);
            return false;
        } catch (InconsistentOntologyException e) {
            return true;
        }
    }

    @Test
    public void everyGuardedQueryThrowsOnAnInconsistentOntologyLikeHermit() throws Exception {
        OWLOntology o = IndividualsTest.parse(INCONSISTENT);
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        open.add(hermit);
        KMReasoner km = km(o);
        assertFalse(km.isConsistent());
        assertFalse(hermit.isConsistent());
        for (Map.Entry<String, Query> e : guardedQueries(o).entrySet()) {
            assertTrue("HermiT throws for " + e.getKey(), throwsInconsistent(e.getValue(), hermit));
            assertTrue("KM throws for " + e.getKey(), throwsInconsistent(e.getValue(), km));
        }
    }

    @Test
    public void aConsistentOntologyThrowsNothingFromTheGuardedQueries() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        KMReasoner km = km(o);
        for (Map.Entry<String, Query> e : guardedQueries(o).entrySet()) {
            assertFalse(e.getKey(), throwsInconsistent(e.getValue(), km));
        }
    }

    @Test
    public void consistencyAndTheUnsatisfiableNodeDoNotThrowOnAnInconsistentOntology() throws Exception {
        OWLOntology o = IndividualsTest.parse(INCONSISTENT);
        KMReasoner km = km(o);
        assertFalse(km.isConsistent());
        assertNotNull(km.getUnsatisfiableClasses());
        assertNotNull(km.getTopClassNode());
        assertNotNull(km.getBottomClassNode());
        // The explanation code reads the committed snapshot, not the reasoner's answers.
        assertNotNull(km.getCommittedOntologySnapshot());
    }

    // ---- item 5: classification outside the constructor ---------------

    @Test
    public void theConstructorDoesNoNativeWork() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        KMReasoner r = km(o);
        assertNull("no native session before the first use", r.getLastIncrementalReceipt());
        assertFalse(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        r.flush();
        assertNull("flush on an unclassified reasoner starts nothing", r.getLastIncrementalReceipt());
        assertFalse(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        r.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        assertTrue(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        assertEquals(1L, r.getLastIncrementalReceipt().revision);
    }

    @Test
    public void theFirstQueryClassifiesAndAnswersCorrectly() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLDataFactory df = dataFactory(o);
        KMReasoner r = km(o);
        assertTrue(r.getSuperClasses(cls(df, "Dog"), false).containsEntity(cls(df, "Animal")));
        assertTrue(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        assertFalse("only computed types are precomputed", r.isPrecomputed(InferenceType.OBJECT_PROPERTY_HIERARCHY));
        assertFalse(r.isPrecomputed(InferenceType.DATA_PROPERTY_HIERARCHY));
        assertFalse(r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
    }

    @Test
    public void changesBufferedBeforeTheFirstUseAreFoldedIntoTheFirstClassification() throws Exception {
        OWLOntology o = IndividualsTest.parse(IndividualsTest.SMALL);
        OWLOntologyManager m = o.getOWLOntologyManager();
        OWLDataFactory df = dataFactory(o);
        KMReasoner r = km(o);
        OWLClass puppy = cls(df, "Puppy");
        m.addAxiom(o, df.getOWLSubClassOfAxiom(puppy, cls(df, "Dog")));
        assertFalse(r.getPendingChanges().isEmpty());
        assertTrue(r.getSuperClasses(puppy, false).containsEntity(cls(df, "Animal")));
        assertTrue("the first run read the changed ontology", r.getPendingChanges().isEmpty());
        assertEquals(1L, r.getLastIncrementalReceipt().revision);
        // Afterwards buffering works as before: invisible until flush, then a delta.
        OWLClass pup = cls(df, "Pup");
        m.addAxiom(o, df.getOWLSubClassOfAxiom(pup, puppy));
        assertFalse(r.getSuperClasses(pup, false).containsEntity(puppy));
        r.flush();
        assertTrue(r.getSuperClasses(pup, false).containsEntity(puppy));
        assertEquals(2L, r.getLastIncrementalReceipt().revision);
    }

    @Test
    public void aFailedFirstClassificationIsRetriedOnTheNextUse() throws Exception {
        OWLOntologyManager m = org.semanticweb.owlapi.apibinding.OWLManager.createOWLOntologyManager();
        OWLDataFactory df = m.getOWLDataFactory();
        OWLOntology root = m.createOntology(IRI.create(NS + "retry"));
        OWLClass a = cls(df, "RetryA"), b = cls(df, "RetryB");
        m.addAxiom(root, df.getOWLSubClassOfAxiom(a, b));
        IRI missing = IRI.create(NS + "missingImport");
        m.applyChange(new AddImport(root, df.getOWLImportsDeclaration(missing)));
        KMReasoner r = km(root);
        try {
            r.isConsistent();
            fail("the unresolved import must fail the first classification");
        } catch (ReasonerInternalException expected) {
            // as before, now at first use instead of in the constructor
        }
        assertFalse(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        m.applyChange(new RemoveImport(root, df.getOWLImportsDeclaration(missing)));
        r.flush();
        assertTrue(r.getSuperClasses(a, false).containsEntity(b));
        assertTrue(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
    }
}
