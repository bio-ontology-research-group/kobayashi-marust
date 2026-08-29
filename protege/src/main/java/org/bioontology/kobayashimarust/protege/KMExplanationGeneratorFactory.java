package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owl.explanation.api.ExplanationException;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;
import org.semanticweb.owl.explanation.api.ExplanationGeneratorFactory;
import org.semanticweb.owl.explanation.api.ExplanationProgressMonitor;
import org.semanticweb.owl.explanation.api.NullExplanationProgressMonitor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

import java.util.LinkedHashSet;
import java.util.Set;

/** Factory for native KM generators using the OWL Explanation API 2.0.1. */
public final class KMExplanationGeneratorFactory
        implements ExplanationGeneratorFactory<OWLAxiom> {

    private final KMExplanationConfiguration configuration;

    public KMExplanationGeneratorFactory() {
        this(KMExplanationConfiguration.fromSystemProperties());
    }

    public KMExplanationGeneratorFactory(KMExplanationConfiguration configuration) {
        if (configuration == null) {
            throw new NullPointerException("configuration");
        }
        this.configuration = configuration;
    }

    @Override
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(OWLOntology ontology) {
        return createExplanationGenerator(
                ontology, new NullExplanationProgressMonitor<OWLAxiom>());
    }

    /**
     * Create a generator over the exact ontology revision currently published
     * by a KM reasoner. In buffering mode this intentionally excludes pending
     * OWLAPI changes until {@link KMReasoner#flush()} commits them.
     */
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(KMReasoner reasoner) {
        if (reasoner == null) {
            throw new NullPointerException("reasoner");
        }
        return createExplanationGenerator(reasoner.getCommittedOntologySnapshot());
    }

    /** Create a committed-revision generator with a caller progress monitor. */
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(
            KMReasoner reasoner,
            ExplanationProgressMonitor<OWLAxiom> progressMonitor) {
        if (reasoner == null) {
            throw new NullPointerException("reasoner");
        }
        return createExplanationGenerator(
                reasoner.getCommittedOntologySnapshot(), progressMonitor);
    }

    @Override
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(
            OWLOntology ontology,
            ExplanationProgressMonitor<OWLAxiom> progressMonitor) {
        if (ontology == null) {
            throw new NullPointerException("ontology");
        }
        if (progressMonitor == null) {
            throw new NullPointerException("progressMonitor");
        }
        return new KMExplanationGenerator(ontology, progressMonitor, configuration);
    }

    @Override
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(
            Set<? extends OWLAxiom> axioms) {
        return createExplanationGenerator(
                axioms, new NullExplanationProgressMonitor<OWLAxiom>());
    }

    @Override
    public ExplanationGenerator<OWLAxiom> createExplanationGenerator(
            Set<? extends OWLAxiom> axioms,
            ExplanationProgressMonitor<OWLAxiom> progressMonitor) {
        if (axioms == null) {
            throw new NullPointerException("axioms");
        }
        try {
            Set<OWLAxiom> copied = new LinkedHashSet<>();
            copied.addAll(axioms);
            OWLOntology ontology = OWLManager.createOWLOntologyManager()
                    .createOntology(copied);
            return createExplanationGenerator(ontology, progressMonitor);
        } catch (Exception error) {
            throw new ExplanationException(
                    "Could not create an ontology for KM explanation axioms", error);
        }
    }
}
