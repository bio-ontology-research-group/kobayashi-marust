package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.io.BufferedReader;
import java.io.File;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Bridge to the Kobayashi-MaRust engine: serialise the ontology to OWL
 * functional syntax, run the {@code --lines} classifier, and parse the result.
 *
 * <p>Prefers the pure-Rust {@code km classify --lines} (the multi-call binary
 * that spawns its own ofn/elc/engine/tableau workers) when {@code km.bin} /
 * {@code KM_BIN} is configured; otherwise falls back to
 * {@code python owl_classify.py --lines}.
 *
 * <p>Configuration (system property, else environment variable, else default):
 * <ul>
 *   <li>{@code km.bin} / {@code KM_BIN} — path to the {@code km} binary. When
 *       set, {@code km classify --lines} is used (no Python). Default: none.</li>
 *   <li>{@code km.home} / {@code KM_HOME} — repository root (to locate the
 *       bridge script and engine). Default: {@code user.dir}.</li>
 *   <li>{@code km.python} / {@code KM_PYTHON} — Python interpreter (fallback).
 *       Default {@code python3}.</li>
 *   <li>{@code km.classify} / {@code KM_CLASSIFY} — path to owl_classify.py
 *       (fallback). Default {@code <km.home>/engine/py/owl_classify.py}.</li>
 *   <li>{@code km.engine} / {@code KM_ENGINE} — path to the engine binary
 *       (else autodetected / self-dispatched).</li>
 * </ul>
 */
public final class Classifier {

    /** Parsed classification result, in terms of short class-name fragments. */
    public static final class Result {
        public boolean consistent = true;
        public int dropped = 0;
        public final List<String[]> subsumptions = new ArrayList<>(); // {sub, super}
        public final List<String> unsatisfiable = new ArrayList<>();
    }

    private Classifier() {}

    private static String cfg(String prop, String env, String def) {
        String v = System.getProperty(prop);
        if (v == null || v.isEmpty()) v = System.getenv(env);
        return (v == null || v.isEmpty()) ? def : v;
    }

    public static Result classify(OWLOntology ontology) throws Exception {
        String home = cfg("km.home", "KM_HOME", System.getProperty("user.dir"));
        String kmBin = cfg("km.bin", "KM_BIN", null);
        String python = cfg("km.python", "KM_PYTHON", "python3");
        String script = cfg("km.classify", "KM_CLASSIFY",
                home + File.separator + "engine" + File.separator + "py"
                     + File.separator + "owl_classify.py");
        String engine = cfg("km.engine", "KM_ENGINE", null);

        // 1. Serialise the ontology to a temporary .ofn file.
        Path tmp = Files.createTempFile("kmarust-", ".ofn");
        try {
            OWLOntologyManager mgr = ontology.getOWLOntologyManager();
            mgr.saveOntology(ontology, new FunctionalSyntaxDocumentFormat(),
                    org.semanticweb.owlapi.model.IRI.create(tmp.toUri()));

            // 2. Run the classifier: the pure-Rust `km classify --lines` when a
            //    km binary is configured, else the Python `owl_classify.py`.
            ProcessBuilder pb = (kmBin != null)
                    ? new ProcessBuilder(kmBin, "classify", "--lines", tmp.toString())
                    : new ProcessBuilder(python, script, "--lines", tmp.toString());
            if (engine != null) pb.environment().put("KM_ENGINE", engine);
            pb.redirectErrorStream(false);
            Process proc = pb.start();

            Result r = new Result();
            try (BufferedReader in = new BufferedReader(new InputStreamReader(
                    proc.getInputStream(), StandardCharsets.UTF_8))) {
                String line;
                while ((line = in.readLine()) != null) {
                    String[] f = line.split("\t");
                    if (line.startsWith("CONSISTENT ")) {
                        r.consistent = line.trim().endsWith("1");
                    } else if (line.startsWith("DROPPED ")) {
                        try { r.dropped = Integer.parseInt(line.trim().substring(8)); }
                        catch (NumberFormatException ignore) {}
                    } else if (f.length == 3 && f[0].equals("SUB")) {
                        r.subsumptions.add(new String[]{f[1], f[2]});
                    } else if (f.length == 2 && f[0].equals("UNSAT")) {
                        r.unsatisfiable.add(f[1]);
                    }
                }
            }
            StringBuilder err = new StringBuilder();
            try (BufferedReader e = new BufferedReader(new InputStreamReader(
                    proc.getErrorStream(), StandardCharsets.UTF_8))) {
                String line;
                while ((line = e.readLine()) != null) err.append(line).append('\n');
            }
            int rc = proc.waitFor();
            if (rc != 0) {
                throw new RuntimeException(
                        "kobayashi-marust classification failed (rc=" + rc + "):\n" + err);
            }
            return r;
        } finally {
            Files.deleteIfExists(tmp);
        }
    }
}
