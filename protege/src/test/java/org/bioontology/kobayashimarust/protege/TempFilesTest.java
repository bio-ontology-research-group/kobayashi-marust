package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.ReasonerInterruptedException;
import org.semanticweb.owlapi.reasoner.SimpleConfiguration;
import org.semanticweb.owlapi.reasoner.TimeOutException;

import java.io.IOException;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.*;

/**
 * The plugin's temporary files live in java.io.tmpdir and are gone when a
 * query ends, however it ends. A stub km delays the realization so the query
 * can be interrupted or time out while its files exist.
 */
public class TempFilesTest {

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    private String saved;
    /** Files of other tests' live reasoners in this JVM, present before the test. */
    private final Set<String> before = new HashSet<>(mineNow());

    private static List<String> mineNow() {
        try {
            return mine();
        } catch (IOException e) {
            throw new IllegalStateException(e);
        }
    }

    @After
    public void restore() {
        if (saved != null) System.setProperty("km.bin", saved);
    }

    /** This JVM's kmarust-* files in java.io.tmpdir. */
    private static List<String> mine() throws IOException {
        List<String> out = new ArrayList<>();
        String prefix = TempFiles.PREFIX + ProcessHandle.current().pid() + "-";
        try (DirectoryStream<Path> files = Files.newDirectoryStream(
                Paths.get(System.getProperty("java.io.tmpdir")), prefix + "*")) {
            for (Path f : files) out.add(f.getFileName().toString());
        }
        Collections.sort(out);
        return out;
    }

    /** Files this test made that still exist. */
    private List<String> made() throws IOException {
        List<String> out = mine();
        out.removeAll(before);
        return out;
    }

    private void awaitNone() throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
        while (!made().isEmpty() && System.nanoTime() < deadline) Thread.sleep(50);
        assertEquals("kmarust files left behind", Collections.<String>emptyList(), made());
    }

    private static KMReasoner reasoner(long timeOutMillis) throws Exception {
        OWLOntology o = IndividualsTest.parse(BatchRunTest.DATA);
        KMReasonerFactory f = new KMReasonerFactory();
        return (KMReasoner) (timeOutMillis > 0 ? f.createReasoner(o, new SimpleConfiguration(timeOutMillis))
                : f.createReasoner(o));
    }

    private static OWLNamedIndividual rex(KMReasoner r) {
        return r.getRootOntology().getOWLOntologyManager().getOWLDataFactory()
                .getOWLNamedIndividual(IRI.create("http://example.org/intr#rex"));
    }

    private static OWLDataProperty num(KMReasoner r) {
        return r.getRootOntology().getOWLOntologyManager().getOWLDataFactory()
                .getOWLDataProperty(IRI.create("http://example.org/intr#num"));
    }

    private void delayRealize(int seconds) throws Exception {
        saved = System.getProperty("km.bin");
        Path dir = Files.createTempDirectory(Paths.get("target"), "temp-km");
        Path script = dir.resolve("km");
        String body = "#!/bin/sh\ncase \" $* \" in\n*'--realize'*) sleep " + seconds + ";;\nesac\nexec '"
                + saved + "' \"$@\"\n";
        Files.write(script, body.getBytes("UTF-8"));
        assertTrue(script.toFile().setExecutable(true));
        System.setProperty("km.bin", script.toAbsolutePath().toString());
    }

    @Test
    public void finishedQueriesLeaveNoFile() throws Exception {
        KMReasoner r = reasoner(0);
        assertTrue(r.isConsistent());
        r.precomputeInferences(InferenceType.CLASS_ASSERTIONS, InferenceType.OBJECT_PROPERTY_ASSERTIONS);
        assertEquals(2, r.getDataPropertyValues(rex(r), num(r)).size());
        r.getTypes(rex(r), false);
        r.getObjectPropertyValues(rex(r), r.getRootOntology().getOWLOntologyManager().getOWLDataFactory()
                .getOWLObjectProperty(IRI.create("http://example.org/intr#ownedBy")));
        // Only the open incremental session keeps its log while the reasoner lives.
        assertTrue(String.valueOf(made()), made().stream().allMatch(f -> f.contains("-incremental-")));
        r.dispose();
        awaitNone();
    }

    @Test
    public void anInterruptedQueryLeavesNoFile() throws Exception {
        delayRealize(30);
        KMReasoner r = reasoner(0);
        assertTrue(r.isConsistent());
        ExecutorService ex = Executors.newSingleThreadExecutor();
        try {
            Future<?> call = ex.submit(() -> r.getDataPropertyValues(rex(r), num(r)));
            long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(30);
            while (made().stream().noneMatch(f -> f.endsWith(".ofn")) && System.nanoTime() < deadline) {
                Thread.sleep(20);
            }
            assertTrue("the query wrote its input: " + made(), made().stream().anyMatch(f -> f.endsWith(".ofn")));
            r.interrupt();
            try {
                call.get(10, TimeUnit.SECONDS);
                fail("interrupted");
            } catch (java.util.concurrent.ExecutionException e) {
                assertTrue(String.valueOf(e.getCause()), e.getCause() instanceof ReasonerInterruptedException);
            }
            assertTrue(String.valueOf(made()), made().stream().allMatch(f -> f.contains("-incremental-")));
        } finally {
            ex.shutdownNow();
            r.dispose();
        }
        awaitNone();
    }

    @Test
    public void aTimedOutQueryLeavesNoFileOnceDisposed() throws Exception {
        delayRealize(30);
        KMReasoner r = reasoner(2000);
        assertTrue(r.isConsistent());
        try {
            r.getDataPropertyValues(rex(r), num(r));
            fail("timed out");
        } catch (TimeOutException expected) {
            // the batch goes on with its input file
        }
        r.dispose();
        awaitNone();
    }
}
