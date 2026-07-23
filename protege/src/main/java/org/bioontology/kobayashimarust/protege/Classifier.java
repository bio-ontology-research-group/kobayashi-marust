package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.OWLOntology;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * Bridge to the Kobayashi-MaRust engine: serialise the ontology to OWL
 * functional syntax, run the {@code --lines} classifier, and parse the result.
 *
 * <p>Invokes the pure-Rust {@code km classify --lines} multi-call binary.
 *
 * <p>Configuration (system property, else environment variable, else default):
 * <ul>
 *   <li>{@code km.bin} / {@code KM_BIN} — path to the {@code km} binary.
 *       Default: {@code km}, resolved from {@code PATH}.</li>
 *   <li>{@code km.timeout.seconds} / {@code KM_TIMEOUT_SECONDS} — maximum
 *       classification time. Default: 600 seconds.</li>
 * </ul>
 */
public final class Classifier {

    /** Parsed classification result, in terms of complete class IRIs. */
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
        String kmBin = cfg("km.bin", "KM_BIN", "km");
        long timeout;
        try {
            timeout = Long.parseLong(cfg(
                    "km.timeout.seconds", "KM_TIMEOUT_SECONDS", "600"));
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException(
                    "km.timeout.seconds must be an integer number of seconds", e);
        }
        if (timeout <= 0) {
            throw new IllegalArgumentException(
                    "km.timeout.seconds must be greater than zero");
        }

        // Flatten the complete imports closure. KM intentionally rejects
        // unresolved owl:imports declarations rather than classifying a
        // partial ontology.
        Path tmp = Files.createTempFile("kmarust-", ".ofn");
        Path log = Files.createTempFile("kmarust-", ".log");
        try {
            FlattenedOntology.save(ontology, tmp);

            ProcessBuilder pb = new ProcessBuilder(
                    kmBin, "classify", "--lines", "--format", "functional",
                    tmp.toString());
            pb.redirectErrorStream(true);
            pb.redirectOutput(log.toFile());
            Process proc = pb.start();

            if (!proc.waitFor(timeout, TimeUnit.SECONDS)) {
                proc.destroyForcibly();
                throw new RuntimeException(
                        "Kobayashi-MaRust classification timed out after "
                        + timeout + " seconds");
            }
            int rc = proc.exitValue();
            List<String> lines = Files.readAllLines(log, StandardCharsets.UTF_8);
            if (rc != 0) {
                throw new RuntimeException(
                        "Kobayashi-MaRust classification failed (exit "
                        + rc + "):\n" + String.join("\n", lines));
            }
            Result r = new Result();
            boolean protocolSeen = false;
            for (String line : lines) {
                String[] f = line.split("\t");
                if (line.startsWith("CONSISTENT ")) {
                    protocolSeen = true;
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
            if (!protocolSeen) {
                throw new RuntimeException(
                        "Kobayashi-MaRust returned no classification result:\n"
                        + String.join("\n", lines));
            }
            if (r.dropped != 0) {
                throw new RuntimeException(
                        "Kobayashi-MaRust declined a complete classification: "
                        + r.dropped + " clause(s) were dropped");
            }
            return r;
        } finally {
            Files.deleteIfExists(tmp);
            Files.deleteIfExists(log);
        }
    }
}
