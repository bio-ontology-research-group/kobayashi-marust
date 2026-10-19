package org.bioontology.kobayashimarust.protege;

import com.google.gson.Gson;
import com.google.gson.JsonObject;
import org.semanticweb.owlapi.model.OWLOntology;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * Bridge to the Kobayashi-MaRust engine: serialise the ontology to OWL
 * functional syntax, maintain a native incremental session, and parse results.
 *
 * <p>The persistent path invokes {@code km incremental-source}; the static
 * one-shot compatibility method invokes {@code km classify --lines}.
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

    /** Receipt for the last native source-level transaction. */
    public static final class IncrementalReceipt {
        public long revision;
        public String route_before;
        public String route_after;
        public boolean route_migrated;
        public String strategy;
        public boolean reused_fixpoint;
        public int reused_subsumptions;
        public int reused_edges;
        public int retained_states;
        public int invalidated_states;
        public int added_normalized_clauses;
        public int removed_normalized_clauses;
        public int added_rules;
        public int removed_rules;
        public boolean meaningful_incremental_update;
        // The default source session retains exact answers and locality rows;
        // these counters distinguish that work from resumed worker fixpoints.
        public long base_revision_statements;
        public long removed_statements;
        public long removed_axioms;
        public long added_statements;
        public long added_axioms;
        public long reused_index_axioms;
        public long rebuilt_index_axioms;
        // Null means an older native receipt did not report this work.
        public Long index_build_calls;
        public Long index_build_failures;
        public Long cross_revision_compiled_axioms;
        public Long same_update_compiled_axioms;
        public Long compiled_locality_axioms;
        public Long csr_axiom_records;
        public Long csr_conjunctions;
        public Long csr_literal_records;
        public long resumed_backend_states;
        public boolean reused_complete_answer;
        public boolean statement_delta_verified;
        public long affected_subjects;
        public long reclassified_subjects;
        public long module_axioms;
        public long index_axioms;
        public long reused_subjects;
        public long told_subjects;
        public long published_pairs;
        public double seconds;
        public String fallback_reason;
    }

    /**
     * Persistent native source session used by an OWLReasoner instance.
     * Commands are serialized because OWLAPI reasoner lifecycle methods may be
     * called from different UI threads while KM owns one transactional state.
     */
    public static final class Session implements AutoCloseable {
        private final String kmBin;
        private final long timeoutSeconds;
        private final Path log;
        private final Process process;
        private final BufferedWriter input;
        private final BufferedReader output;
        private final ExecutorService reads;
        private final Gson gson = new Gson();
        /** The retained committed answer: subject IRI to its superclass IRIs (non-empty rows only). */
        private final Map<String, String[]> rows = new HashMap<>();
        /** One String instance per distinct IRI: the retained rows must not hold 2 copies per pair. */
        private Map<String, String> pool = new HashMap<>();
        private List<String> unsat = new ArrayList<>();
        private boolean consistent = true;
        private int dropped;
        /** Revision of the committed answer; -1 until the first one. */
        private long committedRevision = -1;
        private Result result;
        private IncrementalReceipt receipt;
        private volatile boolean closed;

        public Session(OWLOntology ontology) throws Exception {
            this(FlattenedOntology.functionalSyntax(ontology));
        }

        public Session(String functionalSyntax) throws Exception {
            this.kmBin = cfg("km.bin", "KM_BIN", "km");
            this.timeoutSeconds = parseTimeout();
            this.log = Files.createTempFile("kmarust-incremental-", ".log");
            ProcessBuilder builder = new ProcessBuilder(kmBin, "incremental-source");
            builder.redirectError(log.toFile());
            this.process = builder.start();
            this.input = new BufferedWriter(new OutputStreamWriter(
                    process.getOutputStream(), StandardCharsets.UTF_8));
            this.output = new BufferedReader(new InputStreamReader(
                    process.getInputStream(), StandardCharsets.UTF_8));
            this.reads = Executors.newSingleThreadExecutor(runnable -> {
                Thread thread = new Thread(runnable, "km-incremental-response");
                thread.setDaemon(true);
                return thread;
            });
            try {
                transact("init", functionalSyntax);
            } catch (Exception error) {
                close();
                throw error;
            }
        }

        public synchronized Result replace(OWLOntology ontology) throws Exception {
            return replace(FlattenedOntology.functionalSyntax(ontology));
        }

        public synchronized Result replace(String functionalSyntax) throws Exception {
            replaceRows(functionalSyntax);
            return result();
        }

        /**
         * Replace the source and patch the retained rows. Returns whether the
         * answer (rows, unsatisfiable classes, consistency) differs from the
         * committed one. A refused or failed update leaves the committed answer
         * untouched.
         */
        public synchronized boolean replaceRows(String functionalSyntax) throws Exception {
            return transact("replace", functionalSyntax);
        }

        public synchronized Result result() {
            if (result == null && committedRevision >= 0) {
                Result r = new Result();
                r.consistent = consistent;
                r.dropped = dropped;
                for (Map.Entry<String, String[]> e : rows.entrySet()) {
                    for (String o : e.getValue()) r.subsumptions.add(new String[]{e.getKey(), o});
                }
                r.unsatisfiable.addAll(unsat);
                result = r;
            }
            return result;
        }

        /** Retained subject rows; the map is the live committed state, read it under no concurrent update. */
        public synchronized Map<String, String[]> rows() { return Collections.unmodifiableMap(rows); }

        public synchronized List<String> unsatisfiable() { return Collections.unmodifiableList(unsat); }

        public synchronized boolean consistent() { return consistent; }

        public synchronized int dropped() { return dropped; }

        public synchronized IncrementalReceipt receipt() {
            return receipt;
        }

        /**
         * One transaction. The native answer is a row delta against the committed
         * revision when it can be, else the complete taxonomy. A delta that does
         * not apply to the committed revision is replaced by a complete answer
         * for the same native revision (`classify`). Nothing is committed until
         * the whole answer has been validated.
         */
        private boolean transact(String op, String source) throws Exception {
            WireResponse wire = exchange(op, source,
                    "replace".equals(op) && committedRevision >= 0 ? committedRevision : null);
            if (wire.revision != null && wire.receipt != null) wire.receipt.revision = wire.revision;
            boolean isDelta = wire.result.delta != null && wire.result.delta;
            if (isDelta && (wire.result.base_revision == null || wire.revision == null
                    || committedRevision < 0 || wire.result.base_revision != committedRevision
                    || wire.revision != committedRevision + 1)) {
                WireResponse full = exchange("classify", null, null);
                if (full.result.delta != null && full.result.delta) {
                    throw failure("KM answered a complete-answer request with a delta");
                }
                if (full.revision == null || !full.revision.equals(wire.revision)) {
                    throw failure("KM complete answer is for revision " + full.revision
                            + ", not " + wire.revision);
                }
                wire = new WireResponse(wire, full.result);
                isDelta = false;
            }
            WireResult r = wire.result;
            if (r.dropped != 0) {
                throw new RuntimeException("Kobayashi-MaRust declined a complete classification: "
                        + r.dropped + " clause(s) were dropped");
            }
            List<String> newUnsat = r.unsatisfiable == null ? new ArrayList<>() : r.unsatisfiable;
            boolean changed;
            if (isDelta) {
                // Validate every row before the first mutation.
                if (r.rows != null) for (WireRow row : r.rows) {
                    if (row == null || row.s == null) throw failure("KM returned a malformed delta row");
                }
                changed = r.rows != null && !r.rows.isEmpty();
                if (r.rows != null) for (WireRow row : r.rows) {
                    if (row.o == null || row.o.length == 0) {
                        rows.remove(row.s);
                    } else {
                        String[] o = new String[row.o.length];
                        for (int i = 0; i < o.length; i++) o[i] = intern(row.o[i]);
                        rows.put(intern(row.s), o);
                    }
                }
                changed |= !newUnsat.equals(unsat) || r.consistent != consistent;
            } else {
                Map<String, ArrayList<String>> grouped = new HashMap<>();
                if (r.subsumptions != null) for (String[] p : r.subsumptions) {
                    grouped.computeIfAbsent(p[0], k -> new ArrayList<>()).add(p[1]);
                }
                rows.clear();
                pool = new HashMap<>();
                for (Map.Entry<String, ArrayList<String>> e : grouped.entrySet()) {
                    String[] o = new String[e.getValue().size()];
                    for (int i = 0; i < o.length; i++) o[i] = intern(e.getValue().get(i));
                    rows.put(intern(e.getKey()), o);
                }
                changed = true;
            }
            unsat = newUnsat;
            consistent = r.consistent;
            dropped = r.dropped;
            committedRevision = wire.revision == null ? committedRevision + 1 : wire.revision;
            receipt = wire.receipt;
            if (changed) result = null;
            return changed;
        }

        private String intern(String iri) {
            String known = pool.putIfAbsent(iri, iri);
            return known == null ? iri : known;
        }

        private WireResponse exchange(String op, String source, Long baseRevision) throws Exception {
            if (closed || !process.isAlive()) {
                throw failure("KM incremental process is not running");
            }
            JsonObject command = new JsonObject();
            command.addProperty("op", op);
            if (source != null) command.addProperty("functional_syntax", source);
            if (baseRevision != null) command.addProperty("base_revision", baseRevision);
            // Stream the request: same bytes as toJson(command), without a second
            // copy of the whole source as an intermediate String.
            gson.toJson(command, input);
            input.newLine();
            input.flush();

            Future<String> pending = reads.submit(output::readLine);
            final String line;
            try {
                line = pending.get(timeoutSeconds, TimeUnit.SECONDS);
            } catch (InterruptedException error) {
                pending.cancel(true);
                NativeProcessTree.terminateAndWait(process);
                Thread.currentThread().interrupt();
                throw failure("KM incremental request was interrupted", error);
            } catch (Exception error) {
                pending.cancel(true);
                NativeProcessTree.terminateAndWait(process);
                throw failure("KM incremental request timed out after "
                        + timeoutSeconds + " seconds", error);
            }
            if (line == null) {
                throw failure("KM incremental process closed its output");
            }
            WireResponse wire;
            try {
                wire = gson.fromJson(line, WireResponse.class);
            } catch (RuntimeException error) {
                throw failure("KM returned invalid incremental JSON: "
                        + (line.length() > 4096 ? line.substring(0, 4096) + "..." : line), error);
            }
            if (wire == null || !"ok".equals(wire.status) || wire.result == null) {
                throw failure("KM incremental " + op + " failed: "
                        + (wire == null ? line : wire.error));
            }
            return wire;
        }

        private RuntimeException failure(String message) {
            return failure(message, null);
        }

        private RuntimeException failure(String message, Throwable cause) {
            String diagnostics = "";
            try {
                diagnostics = new String(Files.readAllBytes(log), StandardCharsets.UTF_8);
            } catch (Exception ignored) {
                // The primary protocol error remains authoritative.
            }
            String complete = diagnostics.isEmpty() ? message : message + "\n" + diagnostics;
            return cause == null ? new RuntimeException(complete)
                    : new RuntimeException(complete, cause);
        }

        /** Cancel an active native request without waiting for the session lock. */
        public void interrupt() {
            closed = true;
            NativeProcessTree.terminateAndWait(process);
            reads.shutdownNow();
            try { input.close(); } catch (Exception ignored) { }
            try { output.close(); } catch (Exception ignored) { }
            try { Files.deleteIfExists(log); } catch (Exception ignored) { }
        }

        @Override
        public synchronized void close() {
            if (closed) return;
            closed = true;
            try { input.close(); } catch (Exception ignored) { }
            NativeProcessTree.terminateAndWait(process);
            reads.shutdownNow();
            try { Files.deleteIfExists(log); } catch (Exception ignored) { }
        }
    }

    private static final class WireResponse {
        String status;
        String error;
        Long revision;
        WireResult result;
        IncrementalReceipt receipt;

        WireResponse() {}

        /** The replace response's receipt and revision with the complete answer of that revision. */
        WireResponse(WireResponse base, WireResult result) {
            this.status = base.status;
            this.revision = base.revision;
            this.receipt = base.receipt;
            this.result = result;
        }
    }

    private static final class WireRow {
        String s;
        String[] o;
    }

    private static final class WireResult {
        boolean consistent;
        int dropped;
        List<String[]> subsumptions;
        List<String> unsatisfiable;
        // Row-delta answers: only subjects whose superclass set changed.
        Boolean delta;
        Long base_revision;
        List<WireRow> rows;
    }

    private Classifier() {}

    private static String cfg(String prop, String env, String def) {
        String v = System.getProperty(prop);
        if (v == null || v.isEmpty()) v = System.getenv(env);
        return (v == null || v.isEmpty()) ? def : v;
    }

    private static long parseTimeout() {
        final long timeout;
        try {
            timeout = Long.parseLong(cfg(
                    "km.timeout.seconds", "KM_TIMEOUT_SECONDS", "600"));
        } catch (NumberFormatException error) {
            throw new IllegalArgumentException(
                    "km.timeout.seconds must be an integer number of seconds", error);
        }
        if (timeout <= 0) {
            throw new IllegalArgumentException(
                    "km.timeout.seconds must be greater than zero");
        }
        return timeout;
    }

    public static Result classify(OWLOntology ontology) throws Exception {
        String kmBin = cfg("km.bin", "KM_BIN", "km");
        long timeout = parseTimeout();

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
                NativeProcessTree.terminateAndWait(proc);
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
