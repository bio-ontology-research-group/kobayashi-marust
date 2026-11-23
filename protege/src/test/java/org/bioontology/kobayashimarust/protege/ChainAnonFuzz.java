package org.bioontology.kobayashimarust.protege;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import java.io.File;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

/**
 * Plugin-level differential check for property values (not a JUnit test; run
 * by hand): {@code java -Dkm.bin=KM ... ChainAnonFuzz OUT F1 F2 ...}. For every
 * named individual {@code a}, named property {@code p} and individual {@code b}
 * it compares HermiT's {@code isEntailed(p(a, b))} (the oracle) with the
 * plugin's {@code getObjectPropertyValues(a, p)}, its inverse form
 * {@code getObjectPropertyValues(b, inv p)} and its {@code isEntailed(p(a, b))}.
 * Writes one line per case to OUT: {@code OK}, {@code DIFF} with the differing
 * calls, {@code INCONSISTENT}, or {@code KM_ERROR}/{@code HERMIT_ERROR}.
 */
public class ChainAnonFuzz {
    public static void main(String[] args) throws Exception {
        try (PrintWriter out = new PrintWriter(args[0])) {
            for (int i = 1; i < args.length; i++) {
                String name = new File(args[i]).getName();
                String line;
                try {
                    line = check(new File(args[i]));
                } catch (Throwable t) {
                    line = "KM_ERROR " + String.valueOf(t).replace('\n', ' ');
                }
                out.println(name + "\t" + line);
                out.flush();
            }
        }
        Runtime.getRuntime().halt(0);
    }

    static String check(File f) throws Exception {
        OWLOntology o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(f);
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        OWLReasoner h;
        try {
            h = new ReasonerFactory().createReasoner(o);
            if (!h.isConsistent()) return "INCONSISTENT";
        } catch (Throwable t) {
            return "HERMIT_ERROR " + String.valueOf(t).replace('\n', ' ');
        }
        OWLReasoner k = new KMReasonerFactory().createReasoner(o);
        List<OWLNamedIndividual> inds = new ArrayList<>(o.getIndividualsInSignature());
        inds.sort(Comparator.comparing(x -> x.getIRI().toString()));
        List<OWLObjectProperty> props = new ArrayList<>(o.getObjectPropertiesInSignature());
        props.removeIf(p -> p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty());
        props.sort(Comparator.comparing(x -> x.getIRI().toString()));
        StringBuilder diffs = new StringBuilder();
        int checked = 0;
        try {
            for (OWLObjectProperty p : props) {
                for (OWLNamedIndividual a : inds) {
                    Set<OWLNamedIndividual> kv = k.getObjectPropertyValues(a, p).getFlattened();
                    for (OWLNamedIndividual b : inds) {
                        boolean truth = h.isEntailed(df.getOWLObjectPropertyAssertionAxiom(p, a, b));
                        boolean viaValues = kv.contains(b);
                        boolean viaInverse = k.getObjectPropertyValues(b, p.getInverseProperty()).getFlattened().contains(a);
                        boolean viaEntailed = k.isEntailed(df.getOWLObjectPropertyAssertionAxiom(p, a, b));
                        checked++;
                        if (viaValues != truth || viaInverse != truth || viaEntailed != truth) {
                            diffs.append(' ').append(sh(p.getIRI())).append('(').append(sh(a.getIRI())).append(',')
                                    .append(sh(b.getIRI())).append(")hermit=").append(truth).append(",values=")
                                    .append(viaValues).append(",inverse=").append(viaInverse).append(",entailed=")
                                    .append(viaEntailed);
                        }
                    }
                }
            }
        } finally {
            k.dispose();
            h.dispose();
        }
        return diffs.length() == 0 ? "OK " + checked : "DIFF" + diffs;
    }

    static String sh(IRI i) {
        String s = i.toString();
        return s.startsWith("http://ex.org/") ? s.substring(14) : s;
    }
}
