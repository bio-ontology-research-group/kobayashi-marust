package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.util.*;

/**
 * One one-shot {@code km classify --lines} run on the committed ontology
 * extended with fresh axioms: definitions {@code Q ≡ CE} of fresh classes, or
 * assertions about fresh individuals for a consistency test. The reductions in
 * {@link KMReasoner} build the extra axioms; this class renders them after the
 * committed source, runs km, and parses the rows.
 *
 * <p>Fresh names live under {@code urn:kobayashi-marust:fresh:<uuid>:}, a
 * prefix that no IRI of the ontology starts with (checked), so they never
 * collide with the signature, and the readers drop every name outside the
 * signature from the answers.
 */
final class ExtendedRun {

    private ExtendedRun() {}

    /** Parsed rows of one run; IRIs without angle brackets. */
    static final class Answer {
        boolean consistent = true;
        /** Subject IRI to the IRIs of all its entailed named superclasses (SUB rows). */
        final Map<String, Set<String>> supers = new HashMap<>();
        final Set<String> unsat = new HashSet<>();
        /** Classes equivalent to owl:Thing (TOP rows). */
        final Set<String> top = new HashSet<>();
        /** Individual IRI to its entailed named types (TYPE rows). */
        final Map<String, Set<String>> types = new HashMap<>();
        final List<String[]> same = new ArrayList<>();

        Set<String> supersOf(String iri) {
            Set<String> s = supers.get(iri);
            return s == null ? Collections.<String>emptySet() : s;
        }

        boolean hasType(String individual, String cls) {
            Set<String> t = types.get(individual);
            return t != null && t.contains(cls);
        }
    }

    /** Generator of names that are fresh for one ontology revision. */
    static final class Fresh {
        private final String base;
        private int counter;

        Fresh(OWLOntology ontology) {
            String candidate;
            do {
                candidate = "urn:kobayashi-marust:fresh:" + UUID.randomUUID() + ":";
            } while (used(ontology, candidate));
            base = candidate;
        }

        private static boolean used(OWLOntology ontology, String prefix) {
            for (OWLEntity e : ontology.getSignature()) {
                if (e.getIRI().toString().startsWith(prefix)) return true;
            }
            for (OWLAnonymousIndividual i : ontology.getAnonymousIndividuals()) {
                if (i.toStringID().startsWith(prefix)) return true;
            }
            return false;
        }

        IRI next(String kind) {
            return IRI.create(base + kind + (counter++));
        }

        boolean isFresh(String iri) {
            return iri.startsWith(base);
        }
    }

    private static OWLOntology renderContext;

    private static synchronized OWLOntology context() throws OWLOntologyCreationException {
        if (renderContext == null) renderContext = OWLManager.createOWLOntologyManager().createOntology();
        return renderContext;
    }

    static String strip(String iri) {
        if (iri.length() >= 2 && iri.charAt(0) == '<' && iri.charAt(iri.length() - 1) == '>') {
            return iri.substring(1, iri.length() - 1);
        }
        return iri;
    }

    /**
     * The functional syntax of {@code base} with {@code extra} (and a
     * declaration of every non built-in entity they mention) added before the
     * closing parenthesis of the ontology.
     */
    static String extend(String base, OWLDataFactory df, Collection<? extends OWLAxiom> extra) throws Exception {
        Set<OWLAxiom> axioms = new LinkedHashSet<>();
        for (OWLAxiom ax : extra) {
            for (OWLEntity e : ax.getSignature()) {
                if (!e.isBuiltIn()) axioms.add(df.getOWLDeclarationAxiom(e));
            }
        }
        axioms.addAll(extra);
        OWLOntology ctx = context();
        StringBuilder text = new StringBuilder();
        for (OWLAxiom ax : axioms) {
            text.append(RetainedFunctionalSyntax.renderAxiom(ctx, ax)).append('\n');
        }
        int close = base.lastIndexOf(')');
        if (close < 0) throw new IllegalStateException("the committed source has no ontology body");
        return base.substring(0, close) + "\n" + text + base.substring(close);
    }

    /**
     * Run km on the extended source. A dropped clause or an approximate answer
     * is refused, as for every other native run of the plugin.
     */
    static Answer run(String base, OWLDataFactory df, Collection<? extends OWLAxiom> extra, boolean realize,
                      boolean top, String label, java.util.function.Consumer<Process> onStart) throws Exception {
        return run(base, df, extra, realize, top, false, label, onStart);
    }

    static Answer run(String base, OWLDataFactory df, Collection<? extends OWLAxiom> extra, boolean realize,
                      boolean top, boolean freeUnknownDatatypes, String label,
                      java.util.function.Consumer<Process> onStart) throws Exception {
        return runSource(extend(base, df, extra), extra.size(), realize, top, freeUnknownDatatypes, label, onStart);
    }

    /**
     * Run km on an already extended source ({@link #extend}). Touches no
     * reasoner state, so a batch run can execute it on a background thread.
     */
    static Answer runSource(String source, int extraCount, boolean realize, boolean top,
                            boolean freeUnknownDatatypes, String label,
                            java.util.function.Consumer<Process> onStart) throws Exception {
        List<String> flags = new ArrayList<>();
        if (realize) flags.add("--realize");
        if (top) flags.add("--top");
        if (freeUnknownDatatypes) flags.add("--unknown-datatypes=free");
        String keep = System.getProperty("km.trace.dir");
        if (keep != null && !keep.isEmpty()) {
            // Developer aid: keep each extended input for reproduction.
            java.nio.file.Files.write(java.nio.file.Paths.get(keep, "run-" + System.nanoTime() + "-"
                    + label.replace(' ', '-') + ".ofn"), source.getBytes(java.nio.charset.StandardCharsets.UTF_8));
        }
        long started = System.nanoTime();
        List<String> lines;
        try {
            lines = Classifier.oneShot(source, flags.toArray(new String[0]), label, onStart);
        } finally {
            if (Boolean.getBoolean("km.trace.runs")) {
                System.err.printf("km-run\t%s\t%d\t%.3f%n", label, extraCount,
                        (System.nanoTime() - started) / 1e9);
            }
        }
        String approximate = Classifier.approximate(lines);
        if (approximate != null) {
            throw new RuntimeException("Kobayashi-MaRust declined a complete answer to the " + label
                    + ": the answer is approximate (" + approximate + ")");
        }
        int dropped = Classifier.droppedRow(lines);
        if (dropped != 0) {
            throw new RuntimeException("Kobayashi-MaRust declined a complete answer to the " + label
                    + ": " + dropped + " clause(s) were dropped");
        }
        Answer a = new Answer();
        a.consistent = Classifier.consistentRow(lines);
        for (String line : lines) {
            String[] f = line.split("\t");
            if (f.length == 3 && f[0].equals("SUB")) {
                a.supers.computeIfAbsent(strip(f[1]), k -> new HashSet<>()).add(strip(f[2]));
            } else if (f.length == 2 && f[0].equals("UNSAT")) {
                a.unsat.add(strip(f[1]));
            } else if (f.length == 2 && f[0].equals("TOP")) {
                a.top.add(strip(f[1]));
            } else if (f.length == 3 && f[0].equals("TYPE")) {
                a.types.computeIfAbsent(strip(f[1]), k -> new HashSet<>()).add(strip(f[2]));
            } else if (f.length == 3 && f[0].equals("SAME")) {
                a.same.add(new String[]{strip(f[1]), strip(f[2])});
            }
        }
        return a;
    }
}
