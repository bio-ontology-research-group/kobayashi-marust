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
import java.util.List;
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
                Response response = command("init", functionalSyntax);
                this.result = response.result;
                this.receipt = response.receipt;
            } catch (Exception error) {
                close();
                throw error;
            }
        }

        public synchronized Result replace(OWLOntology ontology) throws Exception {
            return replace(FlattenedOntology.functionalSyntax(ontology));
        }

        public synchronized Result replace(String functionalSyntax) throws Exception {
            Response response = command("replace", functionalSyntax);
            this.result = response.result;
            this.receipt = response.receipt;
            return result;
        }

        public synchronized Result result() {
            return result;
        }

        public synchronized IncrementalReceipt receipt() {
            return receipt;
        }

        private Response command(String op, String source) throws Exception {
            if (closed || !process.isAlive()) {
                throw failure("KM incremental process is not running");
            }
            JsonObject command = new JsonObject();
            command.addProperty("op", op);
            command.addProperty("functional_syntax", source);
            input.write(gson.toJson(command));
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
                throw failure("KM returned invalid incremental JSON: " + line, error);
            }
            if (wire == null || !"ok".equals(wire.status) || wire.result == null) {
                throw failure("KM incremental " + op + " failed: "
                        + (wire == null ? line : wire.error));
            }
            return new Response(toResult(wire.result), wire.receipt);
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

    private static final class Response {
        final Result result;
        final IncrementalReceipt receipt;

        Response(Result result, IncrementalReceipt receipt) {
            this.result = result;
            this.receipt = receipt;
        }
    }

    private static final class WireResponse {
        String status;
        String error;
        WireResult result;
        IncrementalReceipt receipt;
    }

    private static final class WireResult {
        boolean consistent;
        int dropped;
        List<String[]> subsumptions;
        List<String> unsatisfiable;
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

    private static Result toResult(WireResult wire) {
        Result result = new Result();
        result.consistent = wire.consistent;
        result.dropped = wire.dropped;
        if (wire.subsumptions != null) result.subsumptions.addAll(wire.subsumptions);
        if (wire.unsatisfiable != null) result.unsatisfiable.addAll(wire.unsatisfiable);
        if (result.dropped != 0) {
            throw new RuntimeException("Kobayashi-MaRust declined a complete classification: "
                    + result.dropped + " clause(s) were dropped");
        }
        return result;
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
