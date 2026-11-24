package org.bioontology.kobayashimarust.protege;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.ReasonerInterruptedException;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.reasoner.TimeOutException;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * No km process may outlive the query that started it, however the query
 * ends: normally (then at dispose()), by interrupt(), by the configured time
 * out, by dispose(), by the JVM exiting (normally, SIGTERM, SIGKILL) or by the
 * km supervisor being killed. The slow input is a pigeonhole ABox (7 pairwise
 * different individuals in a 6-element nominal) whose consistency check runs
 * for minutes in the {@code km engine} worker of {@code km incremental-source}.
 */
public class NativeOrphanTest {

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    /** Pigeonhole ABox: n+1 different individuals, each one of n others. */
    static String pigeonhole(int n) {
        StringBuilder s = new StringBuilder("Prefix(:=<http://example.org/php#>)\nOntology(<http://example.org/php>\n");
        StringBuilder holes = new StringBuilder();
        for (int j = 0; j < n; j++) {
            s.append("Declaration(NamedIndividual(:h").append(j).append("))\n");
            holes.append(" :h").append(j);
        }
        StringBuilder pigeons = new StringBuilder();
        for (int i = 0; i <= n; i++) {
            s.append("Declaration(NamedIndividual(:p").append(i).append("))\n");
            s.append("ClassAssertion(ObjectOneOf(").append(holes.toString().trim()).append(") :p").append(i).append(")\n");
            pigeons.append(" :p").append(i);
        }
        s.append("DifferentIndividuals(").append(pigeons.toString().trim()).append(")\n)\n");
        return s.toString();
    }

    static final String SLOW = pigeonhole(6);
    static final String SMALL = IndividualsTest.SMALL;

    /** Live processes below {@code root} whose command line names the km executable or contains {@code text}. */
    static List<ProcessHandle> kmBelow(ProcessHandle root, String text) {
        String km = new File(System.getProperty("km.bin")).getName();
        return root.descendants().filter(ProcessHandle::isAlive).filter(p -> {
            String line = p.info().commandLine().orElse("");
            return line.contains(km) && (text == null || line.contains(text));
        }).collect(Collectors.toList());
    }

    static List<ProcessHandle> awaitKm(ProcessHandle root, String text, long seconds) throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(seconds);
        List<ProcessHandle> found = kmBelow(root, text);
        while (found.isEmpty() && System.nanoTime() < deadline) {
            Thread.sleep(50);
            found = kmBelow(root, text);
        }
        return found;
    }

    static void assertAllExit(List<ProcessHandle> processes, long seconds, String what) throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(seconds);
        while (processes.stream().anyMatch(ProcessHandle::isAlive) && System.nanoTime() < deadline) {
            Thread.sleep(50);
        }
        List<String> alive = processes.stream().filter(ProcessHandle::isAlive)
                .map(p -> p.pid() + " " + p.info().commandLine().orElse("?")).collect(Collectors.toList());
        for (ProcessHandle p : processes) if (p.isAlive()) p.destroyForcibly();
        assertEquals(what, new ArrayList<String>(), alive);
    }

    static KMReasoner reasoner(String text, long timeOutMillis) throws Exception {
        OWLOntology o = IndividualsTest.parse(text);
        KMReasonerFactory f = new KMReasonerFactory();
        return (KMReasoner) (timeOutMillis > 0 ? f.createReasoner(o, new SimpleConfiguration(timeOutMillis))
                : f.createReasoner(o));
    }

    private static final ProcessHandle SELF = ProcessHandle.current();

    /** km processes of other tests in this JVM, alive when a test starts. */
    private final java.util.Set<Long> before = kmBelow(SELF, null).stream().map(ProcessHandle::pid)
            .collect(Collectors.toSet());

    private List<ProcessHandle> mine(String text) {
        return kmBelow(SELF, text).stream().filter(p -> !before.contains(p.pid())).collect(Collectors.toList());
    }

    @Test
    public void normalEndThenDispose() throws Exception {
        KMReasoner r = reasoner(SMALL, 0);
        assertTrue(r.isConsistent());
        List<ProcessHandle> session = mine(null);
        r.dispose();
        assertAllExit(session, 5, "km processes after dispose()");
    }

    @Test
    public void interruptDuringClassification() throws Exception {
        KMReasoner r = reasoner(SLOW, 0);
        ExecutorService ex = Executors.newSingleThreadExecutor();
        try {
            Future<Boolean> call = ex.submit(r::isConsistent);
            List<ProcessHandle> running = awaitKm(SELF, " engine", 60);
            assertFalse("the km engine worker started", running.isEmpty());
            running = mine(null);
            r.interrupt();
            try {
                call.get(30, TimeUnit.SECONDS);
                fail("the call was interrupted");
            } catch (java.util.concurrent.ExecutionException expected) {
                assertTrue(String.valueOf(expected.getCause()), expected.getCause() instanceof ReasonerInterruptedException);
            }
            assertAllExit(running, 5, "km processes after interrupt()");
        } finally {
            r.dispose();
            ex.shutdownNow();
        }
    }

    @Test
    public void timeOutDuringClassification() throws Exception {
        KMReasoner r = reasoner(SLOW, 3000);
        ExecutorService ex = Executors.newSingleThreadExecutor();
        try {
            Future<Boolean> call = ex.submit(r::isConsistent);
            List<ProcessHandle> running = awaitKm(SELF, " engine", 60);
            assertFalse("the km engine worker started", running.isEmpty());
            running = mine(null);
            try {
                call.get(60, TimeUnit.SECONDS);
                fail("the call timed out");
            } catch (java.util.concurrent.ExecutionException expected) {
                assertTrue(String.valueOf(expected.getCause()), expected.getCause() instanceof TimeOutException);
            }
            assertAllExit(running, 5, "km processes after the time out");
        } finally {
            r.dispose();
            ex.shutdownNow();
        }
    }

    @Test
    public void disposeAfterAStoppedCall() throws Exception {
        KMReasoner r = reasoner(SLOW, 2000);
        try {
            r.isConsistent();
            fail("the call timed out");
        } catch (TimeOutException expected) {
            // the classification was stopped
        }
        List<ProcessHandle> left = mine(null);
        r.dispose();
        assertAllExit(left, 5, "km processes after dispose()");
    }

    @Test
    public void killedSupervisorTakesItsWorkersDown() throws Exception {
        KMReasoner r = reasoner(SLOW, 0);
        ExecutorService ex = Executors.newSingleThreadExecutor();
        try {
            Future<Boolean> call = ex.submit(r::isConsistent);
            List<ProcessHandle> engines = awaitKm(SELF, " engine", 60);
            assertFalse("the km engine worker started", engines.isEmpty());
            List<ProcessHandle> supervisors = mine("incremental-source");
            assertEquals(1, supervisors.size());
            supervisors.get(0).destroyForcibly();
            try {
                call.get(30, TimeUnit.SECONDS);
                fail("the session died");
            } catch (java.util.concurrent.ExecutionException expected) {
                // the plugin reports the dead session
            }
            assertAllExit(engines, 5, "km engine after its supervisor was killed");
        } finally {
            r.dispose();
            ex.shutdownNow();
        }
    }

    @Test
    public void jvmKilledBySigkill() throws Exception {
        jvmEnds("KILL");
    }

    @Test
    public void jvmTerminatedBySigterm() throws Exception {
        jvmEnds("TERM");
    }

    @Test
    public void jvmExitsNormallyDuringAQuery() throws Exception {
        jvmEnds("EXIT");
    }

    /**
     * A child JVM runs the slow query; once its km engine runs, the child is
     * killed (SIGKILL), terminated (SIGTERM) or calls System.exit. No km
     * process of the child may survive it.
     */
    private void jvmEnds(String how) throws Exception {
        Path dir = Files.createTempDirectory(Paths.get("target"), "orphan-child");
        Path ontology = dir.resolve("slow.ofn");
        Files.write(ontology, SLOW.getBytes(StandardCharsets.UTF_8));
        List<String> cmd = new ArrayList<>();
        cmd.add(Paths.get(System.getProperty("java.home"), "bin", "java").toString());
        cmd.add("-Dkm.bin=" + System.getProperty("km.bin"));
        cmd.add("-Djava.io.tmpdir=" + System.getProperty("java.io.tmpdir"));
        cmd.add("-cp");
        cmd.add(System.getProperty("java.class.path"));
        cmd.add(OrphanChild.class.getName());
        cmd.add(ontology.toString());
        cmd.add(how.equals("EXIT") ? "exit-after-engine" : "wait");
        Process child = new ProcessBuilder(cmd).redirectErrorStream(true)
                .redirectOutput(dir.resolve("child.log").toFile()).start();
        try {
            ProcessHandle handle = child.toHandle();
            List<ProcessHandle> engines = awaitKm(handle, " engine", 90);
            assertFalse("the child's km engine started: " + new String(Files.readAllBytes(dir.resolve("child.log"))),
                    engines.isEmpty());
            List<ProcessHandle> all = kmBelow(handle, null);
            if (how.equals("KILL")) {
                handle.destroyForcibly();
            } else if (how.equals("TERM")) {
                handle.destroy();
            }
            assertTrue("the child JVM ended", child.waitFor(30, TimeUnit.SECONDS));
            // After SIGKILL no hook runs: the workers watch the JVM's pid and the
            // incremental-source supervisor exits when its worker and its stdin are gone.
            assertAllExit(all, how.equals("KILL") ? 10 : 5, "km processes after the JVM ended (" + how + ")");
        } finally {
            if (child.isAlive()) child.destroyForcibly();
        }
    }

    /** The child JVM of {@link #jvmEnds}. */
    public static final class OrphanChild {
        public static void main(String[] args) throws Exception {
            OWLOntology o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(args[0]));
            OWLReasoner r = new KMReasonerFactory().createReasoner(o);
            if (args[1].equals("exit-after-engine")) {
                Thread exit = new Thread(() -> {
                    try {
                        awaitKm(ProcessHandle.current(), " engine", 90);
                        Thread.sleep(500);
                    } catch (InterruptedException ignored) {
                        // exit anyway
                    }
                    System.exit(0);
                });
                exit.setDaemon(true);
                exit.start();
            }
            System.out.println("consistent " + r.isConsistent());
        }
    }
}
