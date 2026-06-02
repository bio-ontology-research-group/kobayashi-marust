package org.bioontology.kobayashimarust.protege;

import org.protege.editor.owl.model.inference.AbstractProtegeOWLReasonerInfo;
import org.semanticweb.owlapi.reasoner.BufferingMode;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Protege glue: registers the Kobayashi-MaRust reasoner with the Protege
 * "Reasoner" menu via the {@code inference_reasonerfactory} extension point
 * (see {@code plugin.xml}).
 */
public class KMReasonerInfo extends AbstractProtegeOWLReasonerInfo {

    private final KMReasonerFactory factory = new KMReasonerFactory();

    @Override
    public OWLReasonerFactory getReasonerFactory() {
        return factory;
    }

    @Override
    public BufferingMode getRecommendedBuffering() {
        return BufferingMode.BUFFERING;
    }

    @Override
    public void initialise() throws Exception { }

    @Override
    public void dispose() throws Exception { }
}
