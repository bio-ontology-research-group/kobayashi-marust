package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owlapi.model.OWLAxiom;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/** Immutable result metadata shared by the native adapter and Protégé UI. */
final class KMExplanationRun {

    private final boolean entailed;
    private final Set<Explanation<OWLAxiom>> explanations;
    private final boolean enumerationComplete;
    private final boolean justificationLimitReached;
    private final int classificationChecks;
    private final int classificationCheckLimit;
    private final int justificationLimit;

    KMExplanationRun(
            boolean entailed,
            Set<Explanation<OWLAxiom>> explanations,
            boolean enumerationComplete,
            boolean justificationLimitReached,
            int classificationChecks,
            int classificationCheckLimit,
            int justificationLimit) {
        this.entailed = entailed;
        this.explanations = Collections.unmodifiableSet(
                new LinkedHashSet<>(explanations));
        this.enumerationComplete = enumerationComplete;
        this.justificationLimitReached = justificationLimitReached;
        this.classificationChecks = classificationChecks;
        this.classificationCheckLimit = classificationCheckLimit;
        this.justificationLimit = justificationLimit;
    }

    boolean isEntailed() {
        return entailed;
    }

    Set<Explanation<OWLAxiom>> getExplanations() {
        return explanations;
    }

    boolean isEnumerationComplete() {
        return enumerationComplete;
    }

    boolean isJustificationLimitReached() {
        return justificationLimitReached;
    }

    int getClassificationChecks() {
        return classificationChecks;
    }

    int getClassificationCheckLimit() {
        return classificationCheckLimit;
    }

    int getJustificationLimit() {
        return justificationLimit;
    }

    String statusText() {
        if (!entailed) {
            return "Not entailed by KM; no justification exists for this source.";
        }
        int count = explanations.size();
        String prefix = count + " verified, subset-minimal source justification"
                + (count == 1 ? "" : "s") + ". ";
        String coverage;
        if (enumerationComplete) {
            coverage = "Enumeration complete: all source-occurrence-minimal "
                    + "justifications were found.";
        } else if (justificationLimitReached) {
            coverage = "Bounded result: the requested limit of "
                    + justificationLimit + " was reached; more may exist.";
        } else {
            coverage = "Enumeration incomplete.";
        }
        return prefix + coverage + " Classification checks: "
                + classificationChecks + "/" + classificationCheckLimit + ".";
    }
}
