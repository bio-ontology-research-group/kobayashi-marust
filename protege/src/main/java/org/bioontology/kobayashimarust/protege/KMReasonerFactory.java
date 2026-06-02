package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.*;

/** {@link OWLReasonerFactory} for the Kobayashi-MaRust reasoner. */
public class KMReasonerFactory implements OWLReasonerFactory {

    @Override
    public String getReasonerName() { return "Kobayashi-MaRust"; }

    @Override
    public OWLReasoner createReasoner(OWLOntology ontology) {
        return new KMReasoner(ontology, new SimpleConfiguration(), BufferingMode.BUFFERING);
    }

    @Override
    public OWLReasoner createReasoner(OWLOntology ontology, OWLReasonerConfiguration config) {
        return new KMReasoner(ontology, config, BufferingMode.BUFFERING);
    }

    @Override
    public OWLReasoner createNonBufferingReasoner(OWLOntology ontology) {
        return new KMReasoner(ontology, new SimpleConfiguration(), BufferingMode.NON_BUFFERING);
    }

    @Override
    public OWLReasoner createNonBufferingReasoner(OWLOntology ontology, OWLReasonerConfiguration config) {
        return new KMReasoner(ontology, config, BufferingMode.NON_BUFFERING);
    }
}
