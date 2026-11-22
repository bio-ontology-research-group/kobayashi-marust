package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.TreeSet;

/**
 * Plugin timing and value rows (not a JUnit test; run by hand):
 * {@code java -Dkm.bin=KM ... PluginValues ONT OUT}. Precomputes the class
 * hierarchy, class assertions and object property assertions, then asks
 * {@code getObjectPropertyValues(a, p)} for every named individual and
 * property. Writes the sorted rows {@code p a b} to OUT and the wall times
 * (precompute, values) to standard output.
 */
public class PluginValues {
    public static void main(String[] args) throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(args[0]));
        long t0 = System.nanoTime();
        OWLReasoner k = new KMReasonerFactory().createReasoner(o);
        k.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.CLASS_ASSERTIONS,
                InferenceType.OBJECT_PROPERTY_ASSERTIONS);
        long t1 = System.nanoTime();
        List<OWLNamedIndividual> inds = new ArrayList<>(o.getIndividualsInSignature());
        inds.sort(Comparator.comparing(x -> x.getIRI().toString()));
        List<OWLObjectProperty> props = new ArrayList<>(o.getObjectPropertiesInSignature());
        props.removeIf(p -> p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty());
        TreeSet<String> rows = new TreeSet<>();
        for (OWLObjectProperty p : props)
            for (OWLNamedIndividual a : inds)
                for (OWLNamedIndividual b : k.getObjectPropertyValues(a, p).getFlattened())
                    rows.add(p.getIRI() + "\t" + a.getIRI() + "\t" + b.getIRI());
        long t2 = System.nanoTime();
        try (PrintWriter w = new PrintWriter(args[1])) {
            for (String r : rows) w.println(r);
        }
        System.out.printf("precompute_s %.2f values_s %.2f rows %d individuals %d properties %d%n",
                (t1 - t0) / 1e9, (t2 - t1) / 1e9, rows.size(), inds.size(), props.size());
        k.dispose();
        Runtime.getRuntime().halt(0);
    }
}
