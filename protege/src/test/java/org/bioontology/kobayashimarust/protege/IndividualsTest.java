package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.UnsupportedEntailmentTypeException;

import java.io.File;
import java.util.*;

import static org.junit.Assert.*;

/**
 * Individual queries (types, instances, same individuals) answered from
 * {@code km classify --realize}. Hand-written expectations on a small ABox;
 * the comparison with HermiT is in {@link HermitDifferentialTest}.
 */
public class IndividualsTest {

    static final String NS = "http://example.org/ind#";

    static final String SMALL = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
            + "Ontology(<http://example.org/ind>\n"
            + "Declaration(Class(:Animal)) Declaration(Class(:Mammal)) Declaration(Class(:Dog))\n"
            + "Declaration(Class(:Cat)) Declaration(Class(:Person)) Declaration(Class(:Pet))\n"
            + "Declaration(ObjectProperty(:ownedBy)) Declaration(ObjectProperty(:spouse))\n"
            + "SubClassOf(:Dog :Mammal)\nSubClassOf(:Cat :Mammal)\nSubClassOf(:Mammal :Animal)\n"
            + "EquivalentClasses(:Pet ObjectIntersectionOf(:Animal ObjectSomeValuesFrom(:ownedBy :Person)))\n"
            + "FunctionalObjectProperty(:spouse)\n"
            + "ClassAssertion(:Dog :rex)\nClassAssertion(:Cat :tom)\nClassAssertion(:Person :alice)\n"
            + "ObjectPropertyAssertion(:ownedBy :rex :alice)\n"
            + "SameIndividual(:rex :rexy)\n"
            + "ObjectPropertyAssertion(:spouse :alice :bob)\nObjectPropertyAssertion(:spouse :alice :robert)\n"
            + "ClassAssertion(:Person :bob)\n"
            + "Declaration(NamedIndividual(:loner))\n"
            + ")\n";

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();

    @After
    public void closeReasoners() {
        for (OWLReasoner r : open) r.dispose();
    }

    private OWLReasoner km(OWLOntology ontology) {
        OWLReasoner r = new KMReasonerFactory().createReasoner(ontology);
        open.add(r);
        return r;
    }

    static OWLOntology parse(String functionalSyntax) throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        return m.loadOntologyFromOntologyDocument(new StringDocumentSource(functionalSyntax));
    }

    private static OWLClass cls(OWLDataFactory df, String f) { return df.getOWLClass(IRI.create(NS + f)); }
    private static OWLNamedIndividual ind(OWLDataFactory df, String f) { return df.getOWLNamedIndividual(IRI.create(NS + f)); }

    private static Set<String> names(NodeSet<? extends OWLEntity> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<? extends OWLEntity> n : ns.getNodes()) {
            List<String> one = new ArrayList<>();
            for (OWLEntity e : n.getEntities()) one.add(e.getIRI().getShortForm());
            Collections.sort(one);
            out.add(one.toString());
        }
        return out;
    }

    private static Set<String> names(Node<? extends OWLEntity> n) {
        Set<String> out = new TreeSet<>();
        for (OWLEntity e : n.getEntities()) out.add(e.getIRI().getShortForm());
        return out;
    }

    @Test
    public void typesOfAnAssertedAndInferredIndividual() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertEquals(new TreeSet<>(Arrays.asList("[Animal]", "[Dog]", "[Mammal]", "[Pet]", "[Thing]")),
                names(r.getTypes(ind(df, "rex"), false)));
        assertEquals(new TreeSet<>(Arrays.asList("[Dog]", "[Pet]")),
                names(r.getTypes(ind(df, "rex"), true)));
        // The same individual has the same types.
        assertEquals(names(r.getTypes(ind(df, "rex"), false)), names(r.getTypes(ind(df, "rexy"), false)));
        assertEquals(new TreeSet<>(Arrays.asList("[Animal]", "[Cat]", "[Mammal]", "[Thing]")),
                names(r.getTypes(ind(df, "tom"), false)));
    }

    @Test
    public void anIndividualWithoutNamedTypesHasOnlyThing() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertEquals(Collections.singleton("[Thing]"), names(r.getTypes(ind(df, "loner"), true)));
        assertEquals(Collections.singleton("[Thing]"), names(r.getTypes(ind(df, "loner"), false)));
    }

    @Test
    public void instancesAreSingletonNodesUnderByName() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        // The default policy is BY_NAME: one node per individual, as in HermiT.
        assertEquals(org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy.BY_NAME, r.getIndividualNodeSetPolicy());
        assertEquals(new TreeSet<>(Arrays.asList("[rex]", "[rexy]", "[tom]")),
                names(r.getInstances(cls(df, "Mammal"), false)));
        assertEquals(new TreeSet<>(Arrays.asList("[rex]", "[rexy]")), names(r.getInstances(cls(df, "Dog"), true)));
        assertEquals(new TreeSet<>(Arrays.asList("[alice]", "[bob]", "[loner]", "[rex]", "[rexy]", "[robert]", "[tom]")),
                names(r.getInstances(df.getOWLThing(), false)));
        // getSameIndividuals still reports the whole group.
        assertEquals(new TreeSet<>(Arrays.asList("rex", "rexy")), names(r.getSameIndividuals(ind(df, "rex"))));
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
        open.add(hermit);
        assertEquals(names(hermit.getInstances(cls(df, "Dog"), true)), names(r.getInstances(cls(df, "Dog"), true)));
        assertEquals(names(hermit.getInstances(df.getOWLThing(), false)),
                names(r.getInstances(df.getOWLThing(), false)));
    }

    @Test
    public void instancesAreGroupedIntoSameIndividualNodes() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = new KMReasonerFactory().createReasoner(o, new org.semanticweb.owlapi.reasoner.SimpleConfiguration(
                new org.semanticweb.owlapi.reasoner.NullReasonerProgressMonitor(),
                org.semanticweb.owlapi.reasoner.FreshEntityPolicy.ALLOW, Long.MAX_VALUE,
                org.semanticweb.owlapi.reasoner.IndividualNodeSetPolicy.BY_SAME_AS));
        open.add(r);
        assertEquals(new TreeSet<>(Arrays.asList("[rex, rexy]", "[tom]")),
                names(r.getInstances(cls(df, "Mammal"), false)));
        assertEquals(Collections.singleton("[rex, rexy]"), names(r.getInstances(cls(df, "Dog"), true)));
        // Mammal has no direct instance: every mammal is a Dog or a Cat.
        assertTrue(r.getInstances(cls(df, "Mammal"), true).isEmpty());
        assertEquals(Collections.singleton("[rex, rexy]"), names(r.getInstances(cls(df, "Pet"), false)));
        assertTrue(r.getInstances(df.getOWLNothing(), false).isEmpty());
        // owl:Thing has every individual, in same-individual nodes.
        assertEquals(new TreeSet<>(Arrays.asList("[alice]", "[bob, robert]", "[loner]", "[rex, rexy]", "[tom]")),
                names(r.getInstances(df.getOWLThing(), false)));
        // Only the individuals with no other named type are direct instances of Thing.
        assertEquals(Collections.singleton("[loner]"), names(r.getInstances(df.getOWLThing(), true)));
    }

    @Test
    public void sameIndividualsFollowFunctionalRoles() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertEquals(new TreeSet<>(Arrays.asList("bob", "robert")), names(r.getSameIndividuals(ind(df, "bob"))));
        assertEquals(new TreeSet<>(Arrays.asList("rex", "rexy")), names(r.getSameIndividuals(ind(df, "rexy"))));
        assertEquals(Collections.singleton("alice"), names(r.getSameIndividuals(ind(df, "alice"))));
        // An individual that the ontology does not mention is its own node.
        assertEquals(Collections.singleton("nobody"), names(r.getSameIndividuals(ind(df, "nobody"))));
    }

    @Test
    public void entailmentOfClassAssertionsAndSameIndividual() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertTrue(r.isEntailmentCheckingSupported(AxiomType.CLASS_ASSERTION));
        assertTrue(r.isEntailmentCheckingSupported(AxiomType.SAME_INDIVIDUAL));
        assertTrue(r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Animal"), ind(df, "rex"))));
        assertTrue(r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Pet"), ind(df, "rexy"))));
        assertFalse(r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Cat"), ind(df, "rex"))));
        assertTrue(r.isEntailed(df.getOWLClassAssertionAxiom(df.getOWLThing(), ind(df, "loner"))));
        assertFalse(r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Animal"), ind(df, "loner"))));
        assertTrue(r.isEntailed(df.getOWLSameIndividualAxiom(ind(df, "bob"), ind(df, "robert"))));
        assertFalse(r.isEntailed(df.getOWLSameIndividualAxiom(ind(df, "bob"), ind(df, "alice"))));
        assertTrue(r.isEntailed(df.getOWLSameIndividualAxiom(ind(df, "alice"), ind(df, "alice"))));
        // An anonymous class assertion C(a) is refuted by O ∪ {¬C(a)}.
        assertTrue(r.isEntailed(df.getOWLClassAssertionAxiom(
                df.getOWLObjectSomeValuesFrom(df.getOWLObjectProperty(IRI.create(NS + "ownedBy")), cls(df, "Person")),
                ind(df, "rex"))));
        assertFalse(r.isEntailed(df.getOWLClassAssertionAxiom(
                df.getOWLObjectSomeValuesFrom(df.getOWLObjectProperty(IRI.create(NS + "ownedBy")), cls(df, "Person")),
                ind(df, "tom"))));
    }

    @Test
    public void precomputeAndInferenceTypes() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLReasoner r = km(o);
        Set<InferenceType> types = r.getPrecomputableInferenceTypes();
        assertTrue(types.contains(InferenceType.CLASS_HIERARCHY));
        assertTrue(types.contains(InferenceType.CLASS_ASSERTIONS));
        assertTrue(types.contains(InferenceType.SAME_INDIVIDUAL));
        assertFalse("the constructor does not classify", r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        r.precomputeInferences(InferenceType.CLASS_HIERARCHY);
        assertTrue(r.isPrecomputed(InferenceType.CLASS_HIERARCHY));
        assertFalse("realization is lazy", r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
        assertFalse(r.isPrecomputed(InferenceType.SAME_INDIVIDUAL));
        r.precomputeInferences(InferenceType.CLASS_ASSERTIONS);
        assertTrue(r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
        assertTrue(r.isPrecomputed(InferenceType.SAME_INDIVIDUAL));
    }

    @Test
    public void plainClassificationDoesNotRealize() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        KMReasoner r = (KMReasoner) km(o);
        r.getSuperClasses(cls(df, "Dog"), false);
        r.getSubClasses(cls(df, "Animal"), false);
        r.isConsistent();
        assertFalse(r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
    }

    @Test
    public void realizationIsDroppedWhenTheOntologyChanges() throws Exception {
        OWLOntology o = parse(SMALL);
        OWLOntologyManager m = o.getOWLOntologyManager();
        OWLDataFactory df = m.getOWLDataFactory();
        OWLReasoner r = km(o);
        assertFalse(r.getInstances(cls(df, "Animal"), false).containsEntity(ind(df, "loner")));
        assertTrue(r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));

        // Buffered: nothing changes until flush.
        m.addAxiom(o, df.getOWLClassAssertionAxiom(cls(df, "Dog"), ind(df, "loner")));
        assertFalse(r.getInstances(cls(df, "Animal"), false).containsEntity(ind(df, "loner")));
        r.flush();
        assertFalse("a new revision must be realized again", r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
        assertTrue(r.getInstances(cls(df, "Animal"), false).containsEntity(ind(df, "loner")));
        assertEquals(new TreeSet<>(Arrays.asList("[Animal]", "[Dog]", "[Mammal]", "[Thing]")),
                names(r.getTypes(ind(df, "loner"), false)));

        // An equality added after the first realization.
        m.addAxiom(o, df.getOWLSameIndividualAxiom(ind(df, "loner"), ind(df, "tom")));
        r.flush();
        assertEquals(new TreeSet<>(Arrays.asList("loner", "tom")), names(r.getSameIndividuals(ind(df, "tom"))));
        assertTrue(r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Cat"), ind(df, "loner"))));

        // And a removal.
        m.removeAxiom(o, df.getOWLSameIndividualAxiom(ind(df, "loner"), ind(df, "tom")));
        r.flush();
        assertEquals(Collections.singleton("tom"), names(r.getSameIndividuals(ind(df, "tom"))));
    }

    @Test
    public void anInconsistentOntologyThrowsLikeHermit() throws Exception {
        String inconsistent = SMALL.replace("Declaration(NamedIndividual(:loner))",
                "DisjointClasses(:Dog :Cat)\nClassAssertion(:Dog :tom)");
        OWLOntology o = parse(inconsistent);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertFalse(r.isConsistent());
        try { r.getTypes(ind(df, "rex"), false); fail(); }
        catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) { }
        try { r.getInstances(cls(df, "Dog"), false); fail(); }
        catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) { }
        try { r.getSameIndividuals(ind(df, "rex")); fail(); }
        catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) { }
        try { r.isEntailed(df.getOWLClassAssertionAxiom(cls(df, "Cat"), ind(df, "rex"))); fail(); }
        catch (org.semanticweb.owlapi.reasoner.InconsistentOntologyException expected) { }
    }

    @Test
    public void anOntologyWithoutIndividualsNeedsNoNativeRealization() throws Exception {
        OWLOntology o = parse("Prefix(:=<" + NS + ">)\nOntology(<http://example.org/tbox>\n"
                + "SubClassOf(:A :B)\n)\n");
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner r = km(o);
        assertTrue(r.getInstances(cls(df, "B"), false).isEmpty());
        assertTrue(r.isPrecomputed(InferenceType.CLASS_ASSERTIONS));
    }

    @Test
    public void reasonerVersionComesFromTheBuild() {
        org.semanticweb.owlapi.util.Version v = KMReasoner.versionOf("1.7.0-rc1");
        assertEquals(1, v.getMajor());
        assertEquals(7, v.getMinor());
        assertEquals(0, v.getPatch());
        assertEquals(0, KMReasoner.versionOf("dev").getMajor());
        String built = KMExecutable.pluginVersion();
        assertNotEquals("the build writes the version into km-plugin.properties", "dev", built);
        assertEquals(KMReasoner.versionOf(built).getMinor(),
                ((KMReasoner) km(parse0())).getReasonerVersion().getMinor());
    }

    private static OWLOntology parse0() {
        try { return parse("Ontology(<http://example.org/v>)"); } catch (Exception e) { throw new RuntimeException(e); }
    }
}
