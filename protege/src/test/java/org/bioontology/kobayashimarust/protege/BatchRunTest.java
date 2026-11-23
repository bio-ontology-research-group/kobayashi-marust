package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.ReasonerInterruptedException;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.reasoner.TimeOutException;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static org.junit.Assert.*;

/**
 * Batch runs (all data property values, the realization) and the two ways a
 * call ends (protege/README.md, "Time outs, interrupts and batch runs"): the
 * configured time out leaves the batch going and later calls are answered
 * from it without a new run; interrupt(), dispose() and a new revision stop
 * it. A stub km delays the batch run it is told to delay by a few seconds and
 * then runs the real km, so the eventual answer is the real one.
 */
public class BatchRunTest {

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();
    private String saved;

    @After
    public void restore() {
        for (OWLReasoner r : open) r.dispose();
        if (saved == null) System.clearProperty("km.bin"); else System.setProperty("km.bin", saved);
    }

    /** Count runs whose command line contains {@code pattern} in {@code log}; delay each by {@code seconds}. */
    private Path stub(Path dir, String pattern, int seconds) throws Exception {
        saved = System.getProperty("km.bin");
        String real = saved;
        Path log = dir.resolve("runs.log");
        Path script = dir.resolve("km");
        String body = "#!/bin/sh\n"
                + "case \" $* \" in\n"
                + "*'" + pattern + "'*)\n"
                + "  echo run >> '" + log.toAbsolutePath() + "'\n"
                + "  sleep " + seconds + "\n"
                + "  exec '" + real + "' \"$@\";;\n"
                + "esac\n"
                + "exec '" + real + "' \"$@\"\n";
        Files.write(script, body.getBytes("UTF-8"));
        assertTrue(script.toFile().setExecutable(true));
        System.setProperty("km.bin", script.toAbsolutePath().toString());
        return log;
    }

    private static int runs(Path log) throws Exception {
        return Files.exists(log) ? Files.readAllLines(log).size() : 0;
    }

    /**
     * The ABox of InterruptRecoveryTest plus a value of num that no assertion
     * states, so getDataPropertyValues needs the native batch run.
     */
    static final String DATA = InterruptRecoveryTest.ABOX.substring(0, InterruptRecoveryTest.ABOX.lastIndexOf(')'))
            + "SubClassOf(:Dog DataHasValue(:num \"7\"^^xsd:integer))\n)\n";

    private KMReasoner reasoner(long timeOutMillis) throws Exception {
        OWLOntology o = IndividualsTest.parse(DATA);
        KMReasonerFactory f = new KMReasonerFactory();
        KMReasoner r = (KMReasoner) (timeOutMillis > 0 ? f.createReasoner(o, new SimpleConfiguration(timeOutMillis))
                : f.createReasoner(o));
        open.add(r);
        return r;
    }

    private static OWLDataFactory df(OWLReasoner r) {
        return r.getRootOntology().getOWLOntologyManager().getOWLDataFactory();
    }

    private static OWLNamedIndividual ind(OWLReasoner r, String name) {
        return df(r).getOWLNamedIndividual(IRI.create("http://example.org/intr#" + name));
    }

    private static OWLDataProperty dp(OWLReasoner r, String name) {
        return df(r).getOWLDataProperty(IRI.create("http://example.org/intr#" + name));
    }

    /** The values of rex for num (3 through age, 7 through Dog), from a reasoner without stub. */
    private Set<OWLLiteral> expectedValues() throws Exception {
        KMReasoner plain = reasoner(0);
        return plain.getDataPropertyValues(ind(plain, "rex"), dp(plain, "num"));
    }

    private static final String DATA_BATCH = "data property value query";

    /** km processes of this JVM whose command line contains {@code text}. */
    private static List<ProcessHandle> running(String text) {
        return ProcessHandle.current().descendants().filter(ProcessHandle::isAlive)
                .filter(p -> p.info().commandLine().orElse("").contains(text)).collect(Collectors.toList());
    }

    private static void awaitGone(String text, long seconds) throws InterruptedException {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(seconds);
        while (!running(text).isEmpty() && System.nanoTime() < deadline) Thread.sleep(50);
        assertEquals("processes still running for '" + text + "'", Collections.emptyList(),
                running(text).stream().map(p -> p.info().commandLine().orElse("?")).collect(Collectors.toList()));
    }

    @Test
    public void aTimeOutLeavesTheDataValueBatchGoingForLaterCalls() throws Exception {
        Set<OWLLiteral> expected = expectedValues();
        assertEquals(2, expected.size());
        Path log = stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), DATA_BATCH, 8);
        KMReasoner r = reasoner(3000);
        assertTrue(r.isConsistent());
        int stopped = 0;
        Set<OWLLiteral> got = null;
        long start = System.nanoTime();
        while (got == null && System.nanoTime() - start < TimeUnit.SECONDS.toNanos(60)) {
            try {
                got = r.getDataPropertyValues(ind(r, "rex"), dp(r, "num"));
            } catch (TimeOutException expectedStop) {
                stopped++;
            }
        }
        assertTrue("at least one call timed out", stopped >= 1);
        assertEquals("one batch run served every call", 1, runs(log));
        assertEquals(expected, got);
        // Later calls read the stored answer.
        assertEquals(expected, r.getDataPropertyValues(ind(r, "rex"), dp(r, "num")));
        assertEquals(1, runs(log));
    }

    @Test
    public void aTimeOutLeavesTheRealizationGoingForLaterCalls() throws Exception {
        KMReasoner plain = reasoner(0);
        OWLClass animal = df(plain).getOWLClass(IRI.create("http://example.org/intr#Animal"));
        Set<OWLNamedIndividual> expected = plain.getInstances(animal, false).getFlattened();
        Path log = stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), "--realize", 8);
        KMReasoner r = reasoner(3000);
        assertTrue(r.isConsistent());
        int stopped = 0;
        Set<OWLNamedIndividual> got = null;
        long start = System.nanoTime();
        while (got == null && System.nanoTime() - start < TimeUnit.SECONDS.toNanos(60)) {
            try {
                got = r.getInstances(animal, false).getFlattened();
            } catch (TimeOutException expectedStop) {
                stopped++;
            }
        }
        assertTrue("at least one call timed out", stopped >= 1);
        assertEquals("one realization run", 1, runs(log));
        assertEquals(expected, got);
    }

    @Test
    public void interruptDiscardsTheBatch() throws Exception {
        Set<OWLLiteral> expected = expectedValues();
        Path log = stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), DATA_BATCH, 8);
        KMReasoner r = reasoner(0);
        assertTrue(r.isConsistent());
        ExecutorService ex = Executors.newSingleThreadExecutor();
        try {
            Future<Set<OWLLiteral>> call = ex.submit(() -> r.getDataPropertyValues(ind(r, "rex"), dp(r, "num")));
            long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(60);
            while (runs(log) == 0 && System.nanoTime() < deadline) Thread.sleep(20);
            assertEquals(1, runs(log));
            Thread.sleep(500);
            long stop = System.nanoTime();
            r.interrupt();
            try {
                call.get(10, TimeUnit.SECONDS);
                fail("the call was interrupted");
            } catch (java.util.concurrent.ExecutionException e) {
                assertTrue(String.valueOf(e.getCause()), e.getCause() instanceof ReasonerInterruptedException);
            }
            assertTrue("interrupt() stopped the call promptly",
                    System.nanoTime() - stop < TimeUnit.SECONDS.toNanos(5));
            awaitGone(DATA_BATCH, 5);
        } finally {
            ex.shutdownNow();
        }
        // The batch was discarded: the next call runs it again.
        assertEquals(expected, r.getDataPropertyValues(ind(r, "rex"), dp(r, "num")));
        assertEquals(2, runs(log));
    }

    @Test
    public void disposeStopsABatchThatOutlivedItsCall() throws Exception {
        stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), DATA_BATCH, 30);
        KMReasoner r = reasoner(2000);
        assertTrue(r.isConsistent());
        try {
            r.getDataPropertyValues(ind(r, "rex"), dp(r, "num"));
            fail("the call timed out");
        } catch (TimeOutException expected) {
            // the batch goes on
        }
        assertFalse("the batch run goes on after the time out", running(DATA_BATCH).isEmpty());
        r.dispose();
        awaitGone(DATA_BATCH, 5);
    }

    @Test
    public void interruptWhileIdleStopsABatchThatOutlivedItsCall() throws Exception {
        stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), DATA_BATCH, 30);
        KMReasoner r = reasoner(2000);
        assertTrue(r.isConsistent());
        try {
            r.getDataPropertyValues(ind(r, "rex"), dp(r, "num"));
            fail("the call timed out");
        } catch (TimeOutException expected) {
            // the batch goes on
        }
        assertFalse(running(DATA_BATCH).isEmpty());
        r.interrupt();
        awaitGone(DATA_BATCH, 5);
    }

    @Test
    public void aNewRevisionStopsTheBatchOfTheOldOne() throws Exception {
        Path log = stub(Files.createTempDirectory(Paths.get("target"), "batch-km"), DATA_BATCH, 30);
        KMReasoner r = reasoner(2000);
        assertTrue(r.isConsistent());
        try {
            r.getDataPropertyValues(ind(r, "rex"), dp(r, "num"));
            fail("the call timed out");
        } catch (TimeOutException expected) {
            // the batch goes on
        }
        assertFalse(running(DATA_BATCH).isEmpty());
        OWLOntology o = r.getRootOntology();
        o.getOWLOntologyManager().addAxiom(o, df(r).getOWLDataPropertyAssertionAxiom(
                dp(r, "age"), ind(r, "alice"), df(r).getOWLLiteral(40)));
        r.flush();
        awaitGone(DATA_BATCH, 5);
        assertEquals(1, runs(log));
    }
}
