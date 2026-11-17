package org.bioontology.kobayashimarust.parity;

import com.google.gson.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.FileDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.util.SimpleIRIMapper;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;

/**
 * Differential run of HermiT and the KM plugin reasoner on one ontology.
 *
 * <pre>
 * ParityRun [options] &lt;ontology file&gt; &lt;out.json&gt;
 *   --timeout S       wall budget per reasoner, in seconds (default 120)
 *   --call-timeout S  cap for one query after precompute, in seconds (default 20)
 *   --seed N          sampling seed (default 1)
 *   --sample N        at most N entities per kind (default 200)
 *   --xmx 6g          heap of each worker process
 *   --only hermit|km  run one reasoner (the report then has no verdicts)
 * </pre>
 *
 * Each reasoner runs in its own JVM (a worker). A worker that hangs is killed
 * by the parent and its missing answers are recorded as timeouts. The KM
 * reasoner is found by class name, so the plugin classes only need to be on
 * the class path ({@code -Dkm.bin=} names the km executable).
 */
public final class ParityRun {

    static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    static final String KM_FACTORY = "org.bioontology.kobayashimarust.protege.KMReasonerFactory";

    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("--worker")) {
            worker(args);
            return;
        }
        int timeout = 120, callTimeout = 20, sample = 200;
        long seed = 1;
        String xmx = "6g", only = null, hermitFrom = null;
        List<String> pos = new ArrayList<>();
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--timeout": timeout = Integer.parseInt(args[++i]); break;
                case "--call-timeout": callTimeout = Integer.parseInt(args[++i]); break;
                case "--seed": seed = Long.parseLong(args[++i]); break;
                case "--sample": sample = Integer.parseInt(args[++i]); break;
                case "--xmx": xmx = args[++i]; break;
                case "--only": only = args[++i]; break;
                case "--hermit-from": hermitFrom = args[++i]; break;
                default: pos.add(args[i]);
            }
        }
        if (pos.size() != 2) {
            System.err.println("usage: ParityRun [--timeout S] [--call-timeout S] [--seed N] [--sample N] [--xmx 6g]"
                    + " [--only hermit|km] [--hermit-from DIR] <ontology file> <out.json>");
            System.exit(2);
        }
        File ontFile = new File(pos.get(0)).getAbsoluteFile();
        File out = new File(pos.get(1)).getAbsoluteFile();
        parent(ontFile, out, timeout, callTimeout, seed, sample, xmx, only, hermitFrom);
    }

    // ------------------------------------------------------------------ loading

    static OWLOntology load(File file) throws OWLOntologyCreationException {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        // The W3C wine ontology imports food by its W3C IRI; map siblings.
        File dir = file.getParentFile();
        if (dir != null) {
            File[] sib = dir.listFiles((d, n) -> n.endsWith(".rdf"));
            if (sib != null) {
                for (File f : sib) {
                    String base = f.getName().substring(0, f.getName().length() - 4);
                    m.getIRIMappers().add(new SimpleIRIMapper(
                            IRI.create("http://www.w3.org/TR/2003/PR-owl-guide-20031209/" + base), IRI.create(f)));
                }
            }
        }
        OWLOntologyLoaderConfiguration cfg = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.SILENT);
        return m.loadOntologyFromOntologyDocument(new FileDocumentSource(file), cfg);
    }

    // ------------------------------------------------------------------- worker

    static OWLReasoner createReasoner(String which, OWLOntology ont) throws Exception {
        if (which.equals("hermit")) {
            // The configuration Protege builds: ignoreUnsupportedDatatypes = true.
            org.semanticweb.HermiT.Configuration c = new org.semanticweb.HermiT.Configuration();
            c.ignoreUnsupportedDatatypes = true;
            return new org.semanticweb.HermiT.ReasonerFactory().createReasoner(ont, c);
        }
        OWLReasonerFactory f = (OWLReasonerFactory) Class.forName(KM_FACTORY).getDeclaredConstructor().newInstance();
        return f.createReasoner(ont, new SimpleConfiguration());
    }

    /** Canonical form of an answer: type tag plus sorted strings; nodes keep their structure. */
    static JsonObject canon(Object o) {
        JsonObject j = new JsonObject();
        if (o == null) {
            j.addProperty("t", "void");
        } else if (o instanceof Boolean) {
            j.addProperty("t", "bool");
            j.addProperty("v", (Boolean) o);
        } else if (o instanceof NodeSet) {
            j.addProperty("t", "nodeset");
            j.add("nodes", nodes(((NodeSet<?>) o).getNodes()));
        } else if (o instanceof Node) {
            j.addProperty("t", "node");
            j.add("nodes", nodes(Collections.singleton((Node<?>) o)));
        } else if (o instanceof Collection) {
            j.addProperty("t", "set");
            TreeSet<String> s = new TreeSet<>();
            for (Object e : (Collection<?>) o) s.add(Plan.name(e));
            JsonArray a = new JsonArray();
            for (String e : s) a.add(e);
            j.add("items", a);
        } else {
            j.addProperty("t", "str");
            j.addProperty("v", String.valueOf(o));
        }
        return j;
    }

    static JsonArray nodes(Collection<? extends Node<?>> ns) {
        List<List<String>> all = new ArrayList<>();
        for (Node<?> n : ns) {
            List<String> one = new ArrayList<>();
            for (Object e : n.getEntities()) one.add(Plan.name(e));
            Collections.sort(one);
            all.add(one);
        }
        all.sort(Comparator.comparing(Object::toString));
        JsonArray a = new JsonArray();
        for (List<String> one : all) {
            JsonArray x = new JsonArray();
            for (String s : one) x.add(s);
            a.add(x);
        }
        return a;
    }

    static void worker(String[] args) throws Exception {
        String which = args[1];
        File ontFile = new File(args[2]);
        File resFile = new File(args[3]);
        long budgetMs = Long.parseLong(args[4]) * 1000L;
        long seed = Long.parseLong(args[5]);
        int sample = Integer.parseInt(args[6]);
        long callCapMs = Long.parseLong(args[7]) * 1000L;
        long t0 = System.nanoTime();
        try (PrintWriter w = new PrintWriter(Files.newBufferedWriter(resFile.toPath(), StandardCharsets.UTF_8))) {
            ExecutorService ex = Executors.newSingleThreadExecutor(r -> {
                Thread t = new Thread(r, "parity-" + which);
                t.setDaemon(true);
                return t;
            });
            try {
                OWLOntology ont = load(ontFile);
                Plan plan = new Plan(ont, seed, sample);
                // Creation.
                final OWLOntology fOnt = ont;
                Future<OWLReasoner> cf = ex.submit(() -> createReasoner(which, fOnt));
                long c0 = System.nanoTime();
                OWLReasoner reasoner;
                try {
                    reasoner = cf.get(budgetMs, TimeUnit.MILLISECONDS);
                } catch (TimeoutException te) {
                    emit(w, "__create", Plan.CREATE, "timeout", null, null, msSince(c0));
                    halt(w, which, "create timeout");
                    return;
                } catch (ExecutionException ee) {
                    emit(w, "__create", Plan.CREATE, "exception", null, ee.getCause(), msSince(c0));
                    halt(w, which, "create failed");
                    return;
                }
                emit(w, "__create", Plan.CREATE, "ok", null, null, msSince(c0));
                for (Plan.Call call : plan.calls) {
                    long remaining = budgetMs - (System.nanoTime() - t0) / 1_000_000L;
                    boolean early = call.phase.equals(Plan.CONSISTENCY) || call.phase.equals(Plan.PRECOMPUTE);
                    long cap = early ? remaining : Math.min(remaining, callCapMs);
                    if (cap <= 0) {
                        halt(w, which, "budget exhausted before " + call.id);
                        return;
                    }
                    long s0 = System.nanoTime();
                    final OWLReasoner fr = reasoner;
                    Future<Object> f = ex.submit(() -> call.fn.apply(fr));
                    try {
                        Object a = f.get(cap, TimeUnit.MILLISECONDS);
                        emit(w, call.id, call.phase, "ok", a, null, msSince(s0), call);
                    } catch (TimeoutException te) {
                        emit(w, call.id, call.phase, "timeout", null, null, msSince(s0), call);
                        try { reasoner.interrupt(); } catch (Throwable ignore) { }
                        try {
                            f.get(5, TimeUnit.SECONDS);
                        } catch (TimeoutException stuck) {
                            halt(w, which, "call did not return after interrupt: " + call.id);
                            return;
                        } catch (Throwable ignore) { }
                        if (early) {
                            halt(w, which, "precompute phase timed out");
                            return;
                        }
                    } catch (ExecutionException ee) {
                        emit(w, call.id, call.phase, "exception", null, ee.getCause(), msSince(s0), call);
                    }
                }
                long d0 = System.nanoTime();
                Future<Object> df = ex.submit(() -> { reasoner.dispose(); return null; });
                try {
                    df.get(30, TimeUnit.SECONDS);
                    emit(w, "dispose()", Plan.META, "ok", null, null, msSince(d0));
                } catch (Throwable t) {
                    emit(w, "dispose()", Plan.META, "exception", null, t, msSince(d0));
                }
                JsonObject end = new JsonObject();
                end.addProperty("end", "completed");
                end.addProperty("wall_ms", msSince(t0));
                w.println(GSON.toJson(end));
            } catch (Throwable t) {
                JsonObject end = new JsonObject();
                end.addProperty("end", "crashed");
                end.addProperty("error", t.toString());
                w.println(GSON.toJson(end));
            }
            w.flush();
        }
        System.out.flush();
        killChildren();
        Runtime.getRuntime().halt(0);
    }

    static void halt(PrintWriter w, String which, String why) {
        JsonObject end = new JsonObject();
        end.addProperty("end", "aborted");
        end.addProperty("why", why);
        w.println(GSON.toJson(end));
        w.flush();
        killChildren();
        Runtime.getRuntime().halt(0);
    }

    /** The KM reasoner runs km as a child process; halt would leave it running. */
    static void killChildren() {
        ProcessHandle.current().descendants().forEach(ProcessHandle::destroyForcibly);
    }

    static long msSince(long nano) { return (System.nanoTime() - nano) / 1_000_000L; }

    static void emit(PrintWriter w, String id, String phase, String status, Object ans, Throwable exc, long ms) {
        emit(w, id, phase, status, ans, exc, ms, null);
    }

    static void emit(PrintWriter w, String id, String phase, String status, Object ans, Throwable exc, long ms,
                     Plan.Call call) {
        JsonObject j = new JsonObject();
        j.addProperty("id", id);
        j.addProperty("phase", phase);
        if (call != null) {
            j.addProperty("method", call.method);
            j.addProperty("info", call.info);
        }
        j.addProperty("status", status);
        j.addProperty("ms", ms);
        if (status.equals("ok")) j.add("ans", canon(ans));
        if (exc != null) {
            j.addProperty("exc", exc.getClass().getSimpleName());
            String m = String.valueOf(exc.getMessage());
            j.addProperty("msg", m.length() > 300 ? m.substring(0, 300) : m);
        }
        w.println(GSON.toJson(j));
        w.flush();
    }

    // ------------------------------------------------------------------- parent

    static final class WorkerResult {
        String end = "none";
        String detail = "";
        long wallMs;
        final Map<String, JsonObject> byId = new LinkedHashMap<>();
        String stderrTail = "";
    }

    static WorkerResult runWorker(String which, File ont, File dir, int timeout, int callTimeout, long seed,
                                  int sample, String xmx) throws Exception {
        File res = new File(dir, which + ".jsonl");
        File err = new File(dir, which + ".err");
        List<String> cmd = new ArrayList<>();
        cmd.add(Paths.get(System.getProperty("java.home"), "bin", "java").toString());
        cmd.add("-Xmx" + xmx);
        String tmp = System.getProperty("java.io.tmpdir");
        cmd.add("-Djava.io.tmpdir=" + tmp);
        if (System.getProperty("km.bin") != null) cmd.add("-Dkm.bin=" + System.getProperty("km.bin"));
        cmd.add("-cp");
        cmd.add(System.getProperty("java.class.path"));
        cmd.add(ParityRun.class.getName());
        cmd.addAll(Arrays.asList("--worker", which, ont.getPath(), res.getPath(), String.valueOf(timeout),
                String.valueOf(seed), String.valueOf(sample), String.valueOf(callTimeout)));
        ProcessBuilder pb = new ProcessBuilder(cmd);
        pb.environment().put("KM_THREADS", "1");
        pb.environment().put("TMPDIR", tmp);
        pb.redirectError(err);
        pb.redirectOutput(ProcessBuilder.Redirect.DISCARD);
        long t0 = System.nanoTime();
        Process p = pb.start();
        // Grace on top of the budget: loading and the final bookkeeping.
        boolean done = p.waitFor(timeout + 60L, TimeUnit.SECONDS);
        WorkerResult wr = new WorkerResult();
        if (!done) {
            p.descendants().forEach(ProcessHandle::destroyForcibly);
            p.destroyForcibly();
            p.waitFor(10, TimeUnit.SECONDS);
            wr.end = "killed";
            wr.detail = "worker did not exit " + (timeout + 60) + " s after start";
        }
        wr.wallMs = msSince(t0);
        if (res.isFile()) {
            for (String line : Files.readAllLines(res.toPath(), StandardCharsets.UTF_8)) {
                if (line.isBlank()) continue;
                JsonObject j = JsonParser.parseString(line).getAsJsonObject();
                if (j.has("end")) {
                    if (wr.end.equals("none")) wr.end = j.get("end").getAsString();
                    if (j.has("why")) wr.detail = j.get("why").getAsString();
                    if (j.has("error")) wr.detail = j.get("error").getAsString();
                } else {
                    wr.byId.put(j.get("id").getAsString(), j);
                }
            }
        }
        if (wr.end.equals("none")) {
            wr.end = "crashed";
            wr.detail = "worker exit code " + (p.isAlive() ? "?" : p.exitValue());
        }
        if (err.isFile()) {
            List<String> lines = Files.readAllLines(err.toPath(), StandardCharsets.UTF_8);
            int from = Math.max(0, lines.size() - 8);
            StringBuilder sb = new StringBuilder();
            for (String l : lines.subList(from, lines.size())) {
                if (l.startsWith("Picked up JAVA_TOOL_OPTIONS")) continue;
                sb.append(l.length() > 300 ? l.substring(0, 300) : l).append('\n');
            }
            wr.stderrTail = sb.toString().trim();
        }
        return wr;
    }

    static WorkerResult loadCachedWorker(String which, File fromDir, String baseName, File workDir) throws Exception {
        File wdir = new File(fromDir, baseName + ".workers");
        File res = new File(wdir, which + ".jsonl");
        File err = new File(wdir, which + ".err");
        File parentJson = new File(fromDir, baseName + ".json");
        if (!res.isFile() || !parentJson.isFile()) return null;
        Files.copy(res.toPath(), new File(workDir, which + ".jsonl").toPath(), StandardCopyOption.REPLACE_EXISTING);
        if (err.isFile()) {
            Files.copy(err.toPath(), new File(workDir, which + ".err").toPath(), StandardCopyOption.REPLACE_EXISTING);
        }
        WorkerResult wr = new WorkerResult();
        for (String line : Files.readAllLines(res.toPath(), StandardCharsets.UTF_8)) {
            if (line.isBlank()) continue;
            JsonObject j = JsonParser.parseString(line).getAsJsonObject();
            if (j.has("end")) {
                if (wr.end.equals("none")) wr.end = j.get("end").getAsString();
                if (j.has("why")) wr.detail = j.get("why").getAsString();
                if (j.has("error")) wr.detail = j.get("error").getAsString();
            } else {
                wr.byId.put(j.get("id").getAsString(), j);
            }
        }
        JsonObject pj = JsonParser.parseString(Files.readString(parentJson.toPath(), StandardCharsets.UTF_8)).getAsJsonObject();
        if (pj.has("reasoners") && pj.getAsJsonObject("reasoners").has(which)) {
            JsonObject rj = pj.getAsJsonObject("reasoners").getAsJsonObject(which);
            if (rj.has("wall_ms")) wr.wallMs = rj.get("wall_ms").getAsLong();
            if (wr.end.equals("none") && rj.has("end")) wr.end = rj.get("end").getAsString();
            if (wr.detail.isEmpty() && rj.has("detail")) wr.detail = rj.get("detail").getAsString();
            if (rj.has("stderr_tail")) wr.stderrTail = rj.get("stderr_tail").getAsString();
        }
        return wr;
    }

    static void parent(File ontFile, File out, int timeout, int callTimeout, long seed, int sample, String xmx,
                       String only, String hermitFrom) throws Exception {
        long t0 = System.nanoTime();
        OWLOntology ont = load(ontFile);
        long loadMs = msSince(t0);
        Plan plan = new Plan(ont, seed, sample);
        Path work = Files.createTempDirectory(
                out.getParentFile() == null ? Paths.get(".") : out.getParentFile().toPath(), ".parity-work-");
        WorkerResult h = null, k = null;
        String baseName = out.getName().replaceAll("\\.json$", "");
        try {
            if (only == null || only.equals("hermit")) {
                if (hermitFrom != null) {
                    h = loadCachedWorker("hermit", new File(hermitFrom), baseName, work.toFile());
                }
                if (h == null) {
                    h = runWorker("hermit", ontFile, work.toFile(), timeout, callTimeout, seed, sample, xmx);
                }
            }
            if (only == null || only.equals("km")) k = runWorker("km", ontFile, work.toFile(), timeout, callTimeout, seed, sample, xmx);
        } finally {
            // keep the raw worker output next to the result for debugging
            Path keep = out.toPath().resolveSibling(out.getName().replaceAll("\\.json$", "") + ".workers");
            deleteTree(keep);
            Files.move(work, keep);
        }
        JsonObject root = new JsonObject();
        root.addProperty("ontology", ontFile.getName());
        root.addProperty("path", ontFile.getPath());
        root.addProperty("bytes", ontFile.length());
        root.addProperty("seed", seed);
        root.addProperty("sample", sample);
        root.addProperty("timeout_s", timeout);
        root.addProperty("call_timeout_s", callTimeout);
        root.addProperty("load_ms", loadMs);
        root.add("signature", GSON.toJsonTree(plan.signature));
        JsonObject reasoners = new JsonObject();
        if (h != null) reasoners.add("hermit", summary(h, plan));
        if (k != null) reasoners.add("km", summary(k, plan));
        root.add("reasoners", reasoners);
        JsonArray calls = new JsonArray();
        for (Plan.Call c : plan.calls) {
            JsonObject j = new JsonObject();
            j.addProperty("id", c.id);
            j.addProperty("method", c.method);
            j.addProperty("phase", c.phase);
            JsonObject ha = h == null ? null : answer(h, c.id);
            JsonObject ka = k == null ? null : answer(k, c.id);
            if (ha != null) j.add("hermit", ha);
            if (ka != null) j.add("km", ka);
            if (ha != null && ka != null) {
                j.addProperty("verdict", c.info ? "info" : verdict(c.method, ha, ka));
            }
            calls.add(j);
        }
        root.add("calls", calls);
        Files.write(out.toPath(), GSON.toJson(root).getBytes(StandardCharsets.UTF_8));
    }

    static void deleteTree(Path p) throws IOException {
        if (!Files.exists(p)) return;
        try (java.util.stream.Stream<Path> s = Files.walk(p)) {
            s.sorted(Comparator.reverseOrder()).forEach(x -> x.toFile().delete());
        }
    }

    static JsonObject summary(WorkerResult w, Plan plan) {
        JsonObject j = new JsonObject();
        j.addProperty("end", w.end);
        j.addProperty("detail", w.detail);
        j.addProperty("wall_ms", w.wallMs);
        if (!w.stderrTail.isEmpty()) j.addProperty("stderr_tail", w.stderrTail);
        JsonObject cr = w.byId.get("__create");
        if (cr != null) {
            j.addProperty("create_status", cr.get("status").getAsString());
            j.addProperty("create_ms", cr.get("ms").getAsLong());
            if (cr.has("exc")) j.addProperty("create_exc", cr.get("exc").getAsString() + ": " + cr.get("msg").getAsString());
        }
        Map<String, Long> phases = new LinkedHashMap<>();
        int answered = 0, timeouts = 0, exceptions = 0;
        for (JsonObject c : w.byId.values()) {
            String ph = c.get("phase").getAsString();
            phases.merge(ph, c.get("ms").getAsLong(), Long::sum);
            if (c.has("method")) {
                String st = c.get("status").getAsString();
                if (st.equals("ok")) answered++;
                else if (st.equals("timeout")) timeouts++;
                else exceptions++;
            }
        }
        j.add("phase_ms", GSON.toJsonTree(phases));
        j.addProperty("calls_planned", plan.calls.size());
        j.addProperty("calls_ok", answered);
        j.addProperty("calls_exception", exceptions);
        j.addProperty("calls_timeout", timeouts);
        j.addProperty("calls_missing", plan.calls.size() - answered - timeouts - exceptions);
        return j;
    }

    private static String normalizeCallId(String id) {
        if (id == null || !id.contains("Generated by the OWL API")) {
            return id;
        }
        return id.replaceAll("(Generated by the OWL API [^\\\"]*? on )[^\\\"]+", "$1<DATE>");
    }

    /** The recorded call, or a "missing" record when the worker never reached it. */
    static JsonObject answer(WorkerResult w, String id) {
        JsonObject c = w.byId.get(id);
        if (c == null && id.contains("Generated by the OWL API")) {
            String nid = normalizeCallId(id);
            for (Map.Entry<String, JsonObject> e : w.byId.entrySet()) {
                if (e.getKey().contains("Generated by the OWL API") && normalizeCallId(e.getKey()).equals(nid)) {
                    c = e.getValue();
                    break;
                }
            }
        }
        JsonObject j = new JsonObject();
        if (c == null) {
            j.addProperty("status", "missing");
            JsonObject cr = w.byId.get("__create");
            if (cr != null && !cr.get("status").getAsString().equals("ok")) {
                // The reasoner never existed: every call inherits the creation outcome.
                j.addProperty("status", cr.get("status").getAsString());
                if (cr.has("exc")) j.addProperty("exc", cr.get("exc").getAsString());
                if (cr.has("msg")) j.addProperty("msg", cr.get("msg").getAsString());
            }
            return j;
        }
        for (String f : new String[]{"status", "ms", "ans", "exc", "msg"}) {
            if (c.has(f)) j.add(f, c.get(f));
        }
        return j;
    }

    static boolean ok(JsonObject a) { return a.get("status").getAsString().equals("ok"); }

    /**
     * agree, differ_content, differ_structure, km_unsupported (KM threw, HermiT
     * answered), km_timeout, hermit_error (HermiT threw, KM answered),
     * both_error_same (counts as agreement), both_error_different, both_failed,
     * hermit_timeout (HermiT timed out or never reached the call: no comparison).
     */
    static String verdict(JsonObject h, JsonObject k) { return verdict("", h, k); }

    /**
     * Two methods report what the reasoner can do, not a fact about the ontology. When KM says it cannot
     * (isEntailmentCheckingSupported false where HermiT says true, isPrecomputed false where HermiT says true,
     * or fewer precomputable inference types)
     * the call counts as km_unsupported, the same column as a thrown UnsupportedOperationException.
     */
    static String verdict(String method, JsonObject h, JsonObject k) {
        boolean ho = ok(h), ko = ok(k);
        if (ho && ko) {
            JsonObject ha = h.getAsJsonObject("ans"), ka = k.getAsJsonObject("ans");
            String v = compare(ha, ka);
            if (v.equals("agree")) return v;
            if (method.equals("isEntailmentCheckingSupported")
                    && ha.get("t").getAsString().equals("bool") && ka.get("t").getAsString().equals("bool")
                    && ha.get("v").getAsBoolean() && !ka.get("v").getAsBoolean()) {
                return "km_unsupported";
            }
            if (method.equals("isPrecomputed") && ha.get("t").getAsString().equals("bool")
                    && ka.get("t").getAsString().equals("bool")
                    && ha.get("v").getAsBoolean() && !ka.get("v").getAsBoolean()) {
                // HermiT holds the type, KM does not compute it (object property assertions, or the data
                // property hierarchy outside its fragment).
                return "km_unsupported";
            }
            if (method.equals("getPrecomputableInferenceTypes") && ha.get("t").getAsString().equals("set")
                    && ka.get("t").getAsString().equals("set")) {
                Set<String> hs = new TreeSet<>(), ks = new TreeSet<>();
                for (JsonElement e : ha.getAsJsonArray("items")) hs.add(e.getAsString());
                for (JsonElement e : ka.getAsJsonArray("items")) ks.add(e.getAsString());
                if (hs.containsAll(ks) && !ks.equals(hs)) return "km_unsupported";
            }
            return v;
        }
        if (ho) {
            String ks = k.get("status").getAsString();
            return ks.equals("exception") ? "km_unsupported" : "km_timeout";
        }
        String hs = h.get("status").getAsString();
        if (!hs.equals("exception")) return "hermit_timeout";
        if (ko) return "hermit_error";
        boolean he = hs.equals("exception");
        boolean ke = k.get("status").getAsString().equals("exception");
        if (he && ke) {
            return h.get("exc").getAsString().equals(k.get("exc").getAsString())
                    ? "both_error_same" : "both_error_different";
        }
        return "both_failed";
    }

    static String compare(JsonObject h, JsonObject k) {
        String t = h.get("t").getAsString();
        if (!t.equals(k.get("t").getAsString())) return "differ_content";
        if (t.equals("nodeset") || t.equals("node")) {
            if (h.equals(k)) return "agree";
            return flat(h).equals(flat(k)) ? "differ_structure" : "differ_content";
        }
        return h.equals(k) ? "agree" : "differ_content";
    }

    static Set<String> flat(JsonObject nodes) {
        Set<String> s = new TreeSet<>();
        for (JsonElement n : nodes.getAsJsonArray("nodes")) {
            for (JsonElement e : n.getAsJsonArray()) s.add(e.getAsString());
        }
        return s;
    }
}
