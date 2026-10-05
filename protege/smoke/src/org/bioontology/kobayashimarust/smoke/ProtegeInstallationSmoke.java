package org.bioontology.kobayashimarust.smoke;

import org.bioontology.kobayashimarust.protege.KMReasonerFactory;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.lang.reflect.Method;
import java.util.Set;

/**
 * One-shot OSGi consumer used by {@code run-installation-smoke.sh}.
 *
 * <p>This class is deliberately a separate test bundle.  It proves that the
 * packaged KM bundle resolves through Protégé's real OSGi package wiring and
 * that its OWLReasoner and OWL Explanation API exports can invoke the native
 * binary.  It is never included in the released plugin.</p>
 */
public final class ProtegeInstallationSmoke implements BundleActivator {

    private static final String KM_BUNDLE = "org.bioontology.kobayashi-marust";
    private static final String NS = "http://example.org/km-install-smoke#";

    @Override
    public void start(BundleContext context) {
        Thread smoke = new Thread(() -> execute(context), "km-protege-installation-smoke");
        smoke.setDaemon(false);
        smoke.start();
    }

    private static void execute(BundleContext context) {
        OWLReasoner reasoner = null;
        try {
            // Let Protégé finish the current start level before exercising a
            // provider from another plugin bundle.
            Thread.sleep(1_000L);
            Bundle kmBundle = findBundle(context, KM_BUNDLE);
            require(kmBundle.getState() == Bundle.ACTIVE,
                    "KM bundle is not ACTIVE (state=" + kmBundle.getState() + ")");

            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            OWLDataFactory dataFactory = manager.getOWLDataFactory();
            OWLOntology ontology = manager.createOntology();
            OWLClass a = cls(dataFactory, "A");
            OWLClass b = cls(dataFactory, "B");
            OWLClass c = cls(dataFactory, "C");
            OWLAxiom ab = dataFactory.getOWLSubClassOfAxiom(a, b);
            OWLAxiom bc = dataFactory.getOWLSubClassOfAxiom(b, c);
            manager.addAxiom(ontology, ab);

            reasoner = new KMReasonerFactory().createNonBufferingReasoner(ontology);
            require(reasoner.getSuperClasses(a, false).containsEntity(b),
                    "packaged reasoner did not classify A subclass B");

            // This must travel through the native source-level session rather
            // than constructing a second batch reasoner.
            manager.addAxiom(ontology, bc);
            require(reasoner.getSuperClasses(a, false).containsEntity(c),
                    "packaged non-buffering update did not derive A subclass C");

            OWLAxiom entailment = dataFactory.getOWLSubClassOfAxiom(a, c);
            // Load the API through the KM bundle wire.  The explanation API is
            // nested in the packaged bundle, so deliberately do not leak a
            // test-classpath copy into this consumer.
            Class<?> factoryType = kmBundle.loadClass(
                    "org.bioontology.kobayashimarust.protege.KMExplanationGeneratorFactory");
            Object factory = factoryType.getConstructor().newInstance();
            Method createGenerator = factoryType.getMethod(
                    "createExplanationGenerator", OWLOntology.class);
            Object generator = createGenerator.invoke(factory, ontology);
            Method getExplanations = generator.getClass().getMethod(
                    "getExplanations", OWLAxiom.class, int.class);
            Set<?> explanations = (Set<?>) getExplanations.invoke(generator, entailment, 1);
            require(explanations.size() == 1,
                    "packaged explanation API did not return one support");
            Object explanation = explanations.iterator().next();
            Set<?> support = (Set<?>) explanation.getClass().getMethod("getAxioms")
                    .invoke(explanation);
            require(support.equals(Set.of(ab, bc)),
                    "packaged explanation support differs from the two source axioms");

            System.out.println("KM_PROTEGE_INSTALLATION_SMOKE_OK");
            reasoner.dispose();
            reasoner = null;
            context.getBundle(0).stop();
        } catch (Throwable error) {
            if (reasoner != null) {
                reasoner.dispose();
            }
            System.err.println("KM_PROTEGE_INSTALLATION_SMOKE_FAILED: " + error);
            error.printStackTrace(System.err);
            System.exit(2);
        }
    }

    private static Bundle findBundle(BundleContext context, String symbolicName) {
        for (Bundle bundle : context.getBundles()) {
            if (symbolicName.equals(bundle.getSymbolicName())) {
                return bundle;
            }
        }
        throw new IllegalStateException("KM plugin bundle is not installed");
    }

    private static OWLClass cls(OWLDataFactory dataFactory, String localName) {
        return dataFactory.getOWLClass(IRI.create(NS + localName));
    }

    private static void require(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }

    @Override
    public void stop(BundleContext context) {
        // The test stops the framework after printing its durable success marker.
    }
}
