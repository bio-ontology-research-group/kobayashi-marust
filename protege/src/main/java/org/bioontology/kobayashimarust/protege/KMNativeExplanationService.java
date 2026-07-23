package org.bioontology.kobayashimarust.protege;

import org.protege.editor.owl.ui.explanation.ExplanationResult;
import org.protege.editor.owl.ui.explanation.ExplanationService;
import org.semanticweb.owl.explanation.api.UnsupportedEntailmentException;
import org.semanticweb.owlapi.model.OWLAxiom;

/**
 * Native KM provider for Protégé's standard Explain action. The core
 * ExplanationManager displays this service only for the exact supported
 * named-class entailment surface.
 */
public final class KMNativeExplanationService extends ExplanationService {

    @Override
    public void initialise() {
        // Configuration is read when the explanation panel is opened.
    }

    @Override
    public boolean hasExplanation(OWLAxiom axiom) {
        return KMExplanationGenerator.supportsEntailment(axiom);
    }

    @Override
    public ExplanationResult explain(OWLAxiom entailment) {
        if (!hasExplanation(entailment)) {
            throw new UnsupportedEntailmentException(
                    "KM native explanations require a named SubClassOf entailment");
        }
        return new KMNativeExplanationResult(
                getOWLModelManager().getActiveOntology(),
                entailment,
                KMExplanationConfiguration.fromSystemProperties());
    }

    @Override
    public void dispose() {
        // Individual ExplanationResult panels own and stop their controllers.
    }
}
