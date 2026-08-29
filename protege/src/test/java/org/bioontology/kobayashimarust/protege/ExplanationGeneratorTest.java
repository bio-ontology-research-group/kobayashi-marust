package org.bioontology.kobayashimarust.protege;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owl.explanation.api.ExplanationException;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorFactory;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorInterruptedException;
import org.semanticweb.owl.explanation.api.ExplanationProgressMonitor;
import org.semanticweb.owl.explanation.api.UnsupportedEntailmentException;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLObjectProperty;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ServiceLoader;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** End-to-end OWL Explanation API tests against the native {@code km} binary. */
public class ExplanationGeneratorTest {

    private static final String NS = "http://example.org/km-explain#";

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

    private static OWLClass cls(OWLDataFactory dataFactory, String localName) {
        return dataFactory.getOWLClass(IRI.create(NS + localName));
    }

    @Test
    public void returnsTwoMinimalElJustificationsAsSourceOwlAxioms() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "A");
        OWLClass b = cls(dataFactory, "B");
        OWLClass c = cls(dataFactory, "C");
        OWLClass d = cls(dataFactory, "D");
        OWLClass noise = cls(dataFactory, "Noise");
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, b));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(b, d));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, c));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(c, d));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(noise, d));

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, d);
        ExplanationGenerator<OWLAxiom> generator =
                new KMExplanationGeneratorFactory().createExplanationGenerator(ontology);
        Set<Explanation<OWLAxiom>> explanations = generator.getExplanations(entailment);

        assertEquals(2, explanations.size());
        for (Explanation<OWLAxiom> explanation : explanations) {
            assertEquals(entailment, explanation.getEntailment());
            assertEquals(2, explanation.getSize());
            assertFalse(explanation.getAxioms().stream()
                    .anyMatch(axiom -> axiom.getSignature().contains(noise)));
            assertTrue(ontology.getAxioms().containsAll(explanation.getAxioms()));
        }
        assertEquals(1, generator.getExplanations(entailment, 1).size());
    }

    @Test
    public void routeMigrationDuringMinimisationKeepsTheExactSourceSupport() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "MigrationA");
        OWLClass b = cls(dataFactory, "MigrationB");
        OWLClass c = cls(dataFactory, "MigrationC");
        OWLClass noise = cls(dataFactory, "MigrationNoise");
        OWLClass left = cls(dataFactory, "MigrationLeft");
        OWLClass right = cls(dataFactory, "MigrationRight");
        OWLAxiom first = dataFactory.getOWLSubClassOfAxiom(a, b);
        OWLAxiom second = dataFactory.getOWLSubClassOfAxiom(b, c);
        OWLAxiom disjunctiveNoise = dataFactory.getOWLSubClassOfAxiom(
                noise, dataFactory.getOWLObjectUnionOf(left, right));
        manager.addAxiom(ontology, first);
        manager.addAxiom(ontology, second);
        manager.addAxiom(ontology, disjunctiveNoise);

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, c);
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment, 1);

        assertEquals(1, explanations.size());
        assertEquals(Set.of(first, second), explanations.iterator().next().getAxioms());
    }

    @Test
    public void nonEntailedQueryHasACompleteEmptyExplanationSet() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "AbsentA");
        OWLClass b = cls(dataFactory, "AbsentB");
        manager.addAxiom(ontology, dataFactory.getOWLDeclarationAxiom(a));
        manager.addAxiom(ontology, dataFactory.getOWLDeclarationAxiom(b));

        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(dataFactory.getOWLSubClassOfAxiom(a, b));
        assertTrue(explanations.isEmpty());
    }

    @Test
    public void importedAndAnnotatedSourceAxiomsRemainInTheJustification() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        IRI importedIri = IRI.create(NS + "explanation-import");
        OWLOntology imported = manager.createOntology(importedIri);
        OWLClass a = cls(dataFactory, "ImportA");
        OWLClass b = cls(dataFactory, "ImportB");
        OWLClass c = cls(dataFactory, "ImportC");
        OWLAxiom annotated = dataFactory.getOWLSubClassOfAxiom(a, b).getAnnotatedAxiom(
                Set.of(dataFactory.getOWLAnnotation(
                        dataFactory.getRDFSLabel(), dataFactory.getOWLLiteral("source"))));
        manager.addAxiom(imported, annotated);

        OWLOntology root = manager.createOntology(IRI.create(NS + "explanation-root"));
        manager.applyChange(new org.semanticweb.owlapi.model.AddImport(
                root, dataFactory.getOWLImportsDeclaration(importedIri)));
        OWLAxiom local = dataFactory.getOWLSubClassOfAxiom(b, c);
        manager.addAxiom(root, local);

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, c);
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(root)
                .getExplanations(entailment);
        assertEquals(1, explanations.size());
        Set<OWLAxiom> support = explanations.iterator().next().getAxioms();
        assertEquals(2, support.size());
        assertTrue(support.contains(annotated));
        assertTrue(support.contains(local));
    }

    @Test
    public void duplicateLocalAndImportedAxiomIsOneSourceSupport() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        IRI importedIri = IRI.create(NS + "duplicate-import");
        OWLOntology imported = manager.createOntology(importedIri);
        OWLClass a = cls(dataFactory, "DuplicateA");
        OWLClass b = cls(dataFactory, "DuplicateB");
        OWLAxiom shared = dataFactory.getOWLSubClassOfAxiom(a, b);
        manager.addAxiom(imported, shared);

        OWLOntology root = manager.createOntology(IRI.create(NS + "duplicate-root"));
        manager.applyChange(new org.semanticweb.owlapi.model.AddImport(
                root, dataFactory.getOWLImportsDeclaration(importedIri)));
        manager.addAxiom(root, shared);

        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(root)
                .getExplanations(shared);
        assertEquals(1, explanations.size());
        assertEquals(Set.of(shared), explanations.iterator().next().getAxioms());
    }

    @Test
    public void tautologyHasOneVerifiedEmptySourceJustification() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "TautologyA");
        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, a);

        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment);
        assertEquals(1, explanations.size());
        assertTrue(explanations.iterator().next().getAxioms().isEmpty());
    }

    @Test
    public void generatorRemainsBoundToItsCreationRevision() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "RevisionA");
        OWLClass b = cls(dataFactory, "RevisionB");
        OWLClass c = cls(dataFactory, "RevisionC");
        OWLAxiom first = dataFactory.getOWLSubClassOfAxiom(a, b);
        OWLAxiom second = dataFactory.getOWLSubClassOfAxiom(b, c);
        manager.addAxiom(ontology, first);
        manager.addAxiom(ontology, second);
        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, c);

        ExplanationGenerator<OWLAxiom> committed = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology);
        manager.removeAxiom(ontology, second);

        Set<Explanation<OWLAxiom>> prior = committed.getExplanations(entailment, 1);
        assertEquals(1, prior.size());
        assertTrue(prior.iterator().next().getAxioms().contains(second));
        assertTrue(new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment, 1).isEmpty());
    }

    @Test
    public void reasonerFactoryUsesOnlyTheCommittedBufferedRevision() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "CommittedA");
        OWLClass b = cls(dataFactory, "CommittedB");
        OWLClass c = cls(dataFactory, "CommittedC");
        OWLAxiom first = dataFactory.getOWLSubClassOfAxiom(a, b);
        OWLAxiom pending = dataFactory.getOWLSubClassOfAxiom(b, c);
        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, c);
        manager.addAxiom(ontology, first);

        KMReasoner reasoner = (KMReasoner) new KMReasonerFactory().createReasoner(ontology);
        manager.addAxiom(ontology, pending);
        assertTrue(reasoner.getPendingAxiomAdditions().contains(pending));
        assertTrue(reasoner.createExplanationGenerator()
                .getExplanations(entailment, 1)
                .isEmpty());

        reasoner.flush();
        Set<Explanation<OWLAxiom>> explanations = reasoner.createExplanationGenerator()
                .getExplanations(entailment, 1);
        assertEquals(1, explanations.size());
        assertEquals(Set.of(first, pending), explanations.iterator().next().getAxioms());
        reasoner.dispose();
    }

    @Test
    public void factoryIsDiscoverableThroughTheStandardJavaServiceLoader() {
        boolean found = false;
        for (ExplanationGeneratorFactory<?> factory
                : ServiceLoader.load(ExplanationGeneratorFactory.class)) {
            if (factory instanceof KMExplanationGeneratorFactory) {
                found = true;
            }
        }
        assertTrue("KM explanation factory service metadata missing", found);
    }

    @Test
    public void explainsNamedClassUnsatisfiability() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "UnsatA");
        OWLClass b = cls(dataFactory, "UnsatB");
        OWLClass c = cls(dataFactory, "UnsatC");
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, b));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, c));
        manager.addAxiom(ontology, dataFactory.getOWLDisjointClassesAxiom(b, c));

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLNothing());
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment, 1);

        assertEquals(1, explanations.size());
        Explanation<OWLAxiom> explanation = explanations.iterator().next();
        assertEquals(3, explanation.getSize());
        assertTrue(ontology.getAxioms().containsAll(explanation.getAxioms()));
    }

    @Test
    public void explainsAQualifiedCardinalityPigeonholeClash() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "CardinalityA");
        OWLClass b = cls(dataFactory, "CardinalityB");
        org.semanticweb.owlapi.model.OWLObjectProperty r =
                dataFactory.getOWLObjectProperty(IRI.create(NS + "cardinalityR"));
        OWLAxiom minimum = dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLObjectMinCardinality(2, r, b));
        OWLAxiom maximum = dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLObjectMaxCardinality(1, r, b));
        manager.addAxiom(ontology, minimum);
        manager.addAxiom(ontology, maximum);

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLNothing());
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment, 1);

        assertEquals(1, explanations.size());
        assertEquals(Set.of(minimum, maximum), explanations.iterator().next().getAxioms());
    }

    @Test
    public void explainsNativeAboxSingletonIdentityInconsistency() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass aClass = cls(dataFactory, "NativeAboxClass");
        org.semanticweb.owlapi.model.OWLNamedIndividual a =
                dataFactory.getOWLNamedIndividual(IRI.create(NS + "nativeA"));
        org.semanticweb.owlapi.model.OWLNamedIndividual b =
                dataFactory.getOWLNamedIndividual(IRI.create(NS + "nativeB"));
        OWLAxiom singleton = dataFactory.getOWLEquivalentClassesAxiom(
                aClass, dataFactory.getOWLObjectOneOf(a));
        OWLAxiom assertion = dataFactory.getOWLClassAssertionAxiom(aClass, b);
        OWLAxiom inequality = dataFactory.getOWLDifferentIndividualsAxiom(a, b);
        manager.addAxiom(ontology, singleton);
        manager.addAxiom(ontology, assertion);
        manager.addAxiom(ontology, inequality);

        OWLAxiom inconsistency = dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLThing(), dataFactory.getOWLNothing());
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(inconsistency, 1);

        assertEquals(1, explanations.size());
        assertEquals(Set.of(singleton, assertion, inequality),
                explanations.iterator().next().getAxioms());
    }

    @Test
    public void explainsAnInverseRoleCbEntailment() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "InverseA");
        OWLClass b = cls(dataFactory, "InverseB");
        OWLClass c = cls(dataFactory, "InverseC");
        org.semanticweb.owlapi.model.OWLObjectProperty r =
                dataFactory.getOWLObjectProperty(IRI.create(NS + "r"));
        org.semanticweb.owlapi.model.OWLObjectProperty s =
                dataFactory.getOWLObjectProperty(IRI.create(NS + "s"));
        manager.addAxiom(ontology, dataFactory.getOWLInverseObjectPropertiesAxiom(r, s));
        manager.addAxiom(ontology, dataFactory.getOWLObjectPropertyRangeAxiom(s, b));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(
                a, dataFactory.getOWLObjectSomeValuesFrom(r, c)));

        OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, b);
        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(entailment, 1);
        assertEquals(1, explanations.size());
        assertEquals(3, explanations.iterator().next().getSize());
    }

    @Test
    public void explainsRuleInconsistencyThroughTheValidatedHtGate() throws Exception {
        File fixture = new File("../engine/tests/fixtures/explain_rule_unsat.ofn");
        org.junit.Assume.assumeTrue("rule fixture present", fixture.isFile());
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(fixture);
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLAxiom inconsistency = dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLThing(), dataFactory.getOWLNothing());

        Set<Explanation<OWLAxiom>> explanations = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology)
                .getExplanations(inconsistency, 1);
        assertEquals(1, explanations.size());
        assertTrue(explanations.iterator().next().getAxioms().stream()
                .anyMatch(axiom -> axiom.getAxiomType().equals(AxiomType.SWRL_RULE)));
    }

    @Test
    public void rejectsAnonymousEntailmentQueries() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "AnonymousA");
        OWLClass b = cls(dataFactory, "AnonymousB");
        OWLAxiom anonymous = dataFactory.getOWLSubClassOfAxiom(
                dataFactory.getOWLObjectIntersectionOf(a, b), a);
        assertFalse(new KMNativeExplanationService().hasExplanation(anonymous));
        try {
            new KMExplanationGeneratorFactory()
                    .createExplanationGenerator(ontology)
                    .getExplanations(anonymous, 1);
            fail("anonymous entailment should be rejected");
        } catch (UnsupportedEntailmentException expected) {
            assertTrue(expected.getMessage().contains("named"));
        }
    }

    @Test
    public void rejectsPropertyAndIndividualEntailmentsEvenAtZeroLimit() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLObjectProperty r = dataFactory.getOWLObjectProperty(IRI.create(NS + "r"));
        OWLObjectProperty s = dataFactory.getOWLObjectProperty(IRI.create(NS + "s"));
        OWLAxiom propertyEntailment = dataFactory.getOWLSubObjectPropertyOfAxiom(r, s);
        OWLAxiom individualEntailment = dataFactory.getOWLClassAssertionAxiom(
                cls(dataFactory, "Person"),
                dataFactory.getOWLNamedIndividual(IRI.create(NS + "alice")));
        ExplanationGenerator<OWLAxiom> generator = new KMExplanationGeneratorFactory()
                .createExplanationGenerator(ontology);

        assertUnsupported(generator, propertyEntailment, 1);
        assertUnsupported(generator, propertyEntailment, 0);
        assertUnsupported(generator, individualEntailment, 1);
        assertUnsupported(generator, individualEntailment, 0);

        KMNativeExplanationService service = new KMNativeExplanationService();
        assertFalse(service.hasExplanation(propertyEntailment));
        assertFalse(service.hasExplanation(individualEntailment));
        assertTrue(service.hasExplanation(dataFactory.getOWLSubClassOfAxiom(
                cls(dataFactory, "A"), cls(dataFactory, "B"))));
        try {
            service.explain(propertyEntailment);
            fail("Protégé service should reject an unsupported entailment");
        } catch (UnsupportedEntailmentException expected) {
            assertTrue(expected.getMessage().contains("SubClassOf"));
        }
    }

    private static void assertUnsupported(
            ExplanationGenerator<OWLAxiom> generator,
            OWLAxiom entailment,
            int limit) {
        try {
            generator.getExplanations(entailment, limit);
            fail("unsupported entailment should be rejected explicitly");
        } catch (UnsupportedEntailmentException expected) {
            assertTrue(expected.getMessage().contains("SubClassOf"));
        }
    }

    @Test
    public void failsClosedWhenConfiguredSourceBoundIsTooSmall() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "BoundA");
        OWLClass b = cls(dataFactory, "BoundB");
        OWLClass c = cls(dataFactory, "BoundC");
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, b));
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(b, c));
        KMExplanationConfiguration configuration = new KMExplanationConfiguration(
                System.getProperty("km.bin"), 60, 1, 16, 1024 * 1024, 1);
        try {
            new KMExplanationGeneratorFactory(configuration)
                    .createExplanationGenerator(ontology)
                    .getExplanations(dataFactory.getOWLSubClassOfAxiom(a, c), 1);
            fail("native source bound should fail closed");
        } catch (ExplanationException expected) {
            assertTrue(expected.getMessage().contains("declined or failed"));
        }
    }

    @Test
    public void cancellationTerminatesTheRunningNativeExplanationProcess() throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.createOntology();
        OWLClass a = cls(dataFactory, "CancelA");
        OWLClass b = cls(dataFactory, "CancelB");
        manager.addAxiom(ontology, dataFactory.getOWLSubClassOfAxiom(a, b));

        Path marker = Files.createTempFile("km-explain-started-", ".marker");
        Files.delete(marker);
        Path worker = Files.createTempFile("km-explain-worker-", ".sh");
        String script = "#!/bin/sh\n"
                + "printf started > '" + marker.toString().replace("'", "'\\''") + "'\n"
                + "exec sleep 60\n";
        Files.write(worker, script.getBytes(StandardCharsets.UTF_8));
        assertTrue(worker.toFile().setExecutable(true));

        AtomicBoolean cancelled = new AtomicBoolean(false);
        ExplanationProgressMonitor<OWLAxiom> monitor =
                new ExplanationProgressMonitor<OWLAxiom>() {
                    @Override
                    public void foundExplanation(
                            ExplanationGenerator<OWLAxiom> generator,
                            Explanation<OWLAxiom> explanation,
                            Set<Explanation<OWLAxiom>> explanations) {
                        // The fake worker never returns an explanation.
                    }

                    @Override
                    public boolean isCancelled() {
                        return cancelled.get();
                    }
                };
        KMExplanationConfiguration configuration = new KMExplanationConfiguration(
                worker.toString(), 60, 128, 128, 1024 * 1024, 4);
        ExplanationGenerator<OWLAxiom> generator = new KMExplanationGeneratorFactory(configuration)
                .createExplanationGenerator(ontology, monitor);
        AtomicReference<Throwable> outcome = new AtomicReference<>();
        Thread request = new Thread(() -> {
            try {
                generator.getExplanations(dataFactory.getOWLSubClassOfAxiom(a, b), 1);
                outcome.set(new AssertionError("cancelled explanation unexpectedly completed"));
            } catch (Throwable error) {
                outcome.set(error);
            }
        }, "km-native-explanation-cancellation-test");

        try {
            request.start();
            long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
            while (!Files.exists(marker) && System.nanoTime() < deadline) {
                Thread.sleep(10);
            }
            assertTrue("fake native explanation worker did not start", Files.exists(marker));
            cancelled.set(true);
            request.join(TimeUnit.SECONDS.toMillis(5));
            assertFalse("native explanation request survived cancellation", request.isAlive());
            assertTrue(outcome.get() instanceof ExplanationGeneratorInterruptedException);
        } finally {
            cancelled.set(true);
            request.interrupt();
            request.join(TimeUnit.SECONDS.toMillis(1));
            Files.deleteIfExists(worker);
            Files.deleteIfExists(marker);
        }
    }
}
