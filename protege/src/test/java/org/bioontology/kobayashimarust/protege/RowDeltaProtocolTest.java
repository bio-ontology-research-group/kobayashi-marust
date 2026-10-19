package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.*;

/**
 * Row-delta protocol of {@link Classifier.Session}: patching, empty delta,
 * subject removal, revision-mismatch fallback to a complete answer, and a
 * failed update followed by the next update. Half of it runs against the real
 * native session, half against a scripted stand-in that can send a stale delta.
 */
public class RowDeltaProtocolTest {

    private String savedBin;
    private Path script;
    private Path opsLog;

    @Before
    public void remember() { savedBin = System.getProperty("km.bin"); }

    @After
    public void restore() throws Exception {
        if (savedBin == null) System.clearProperty("km.bin"); else System.setProperty("km.bin", savedBin);
        if (script != null) Files.deleteIfExists(script);
        if (opsLog != null) Files.deleteIfExists(opsLog);
    }

    private static Set<String> pairs(Classifier.Session s) {
        Set<String> out = new TreeSet<>();
        for (Map.Entry<String, String[]> e : s.rows().entrySet()) {
            assertTrue("rows hold non-empty entries only", e.getValue().length > 0);
            for (String o : e.getValue()) out.add(e.getKey() + ">" + o);
        }
        return out;
    }

    private static Set<String> pairs(Classifier.Result r) {
        Set<String> out = new TreeSet<>();
        for (String[] p : r.subsumptions) out.add(p[0] + ">" + p[1]);
        return out;
    }

    private static String source(String axioms) {
        return "Ontology(Declaration(Class(<urn:d:A>)) Declaration(Class(<urn:d:B>)) "
                + "Declaration(Class(<urn:d:C>)) " + axioms + ")";
    }

    @Test
    public void nativeDeltaSequenceEqualsFreshAnswers() throws Exception {
        ReasonerTest.locateKm();
        String[] sources = {
            source("SubClassOf(<urn:d:A> <urn:d:B>)"),
            source("SubClassOf(<urn:d:A> <urn:d:B>) SubClassOf(<urn:d:B> <urn:d:C>)"),
            source("SubClassOf(<urn:d:A> <urn:d:B>) SubClassOf(<urn:d:B> <urn:d:C>)"), // unchanged
            source("SubClassOf(<urn:d:B> <urn:d:C>)"),                                  // subject A removed
            source("SubClassOf(<urn:d:A> <urn:d:B>) SubClassOf(<urn:d:B> <urn:d:C>) SubClassOf(<urn:d:C> owl:Nothing)"),
        };
        boolean[] changed = {true, true, false, true, true};
        try (Classifier.Session s = new Classifier.Session(sources[0])) {
            for (int i = 1; i < sources.length; i++) {
                assertEquals("update " + i, changed[i], s.replaceRows(sources[i]));
                try (Classifier.Session fresh = new Classifier.Session(sources[i])) {
                    assertEquals("rows after update " + i, pairs(fresh), pairs(s));
                    assertEquals(fresh.unsatisfiable(), s.unsatisfiable());
                    assertEquals(pairs(fresh.result()), pairs(s.result()));
                }
                assertEquals(i + 1L, s.receipt().revision);
            }
        }
    }

    @Test
    public void nativeFailedUpdateKeepsCommittedRowsAndNextUpdateIsExact() throws Exception {
        ReasonerTest.locateKm();
        String first = source("SubClassOf(<urn:d:A> <urn:d:B>)");
        String second = source("SubClassOf(<urn:d:A> <urn:d:B>) SubClassOf(<urn:d:B> <urn:d:C>)");
        try (Classifier.Session s = new Classifier.Session(first)) {
            Set<String> before = pairs(s);
            Classifier.Result cached = s.result();
            try {
                s.replaceRows("Ontology(Declaration(Class(<urn:d:A>)) SubClassOf(<urn:d:A> <urn:d:Missing>))");
                fail("an undeclared class must be rejected");
            } catch (RuntimeException expected) {
                // refused
            }
            assertEquals(before, pairs(s));
            assertSame(cached, s.result());
            assertEquals(1L, s.receipt().revision);
            assertTrue(s.replaceRows(second));
            try (Classifier.Session fresh = new Classifier.Session(second)) {
                assertEquals(pairs(fresh), pairs(s));
            }
            assertEquals(2L, s.receipt().revision);
        }
    }

    /** A scripted native session: full init, then answers taken from per-op JSON lines. */
    private void fakeKm(String... responses) throws Exception {
        opsLog = Files.createTempFile("kmfake-ops-", ".log");
        script = Files.createTempFile("kmfake-", ".py");
        StringBuilder list = new StringBuilder();
        for (String r : responses) list.append(r.replace("\\", "\\\\").replace("'''", "\\'\\'\\'")).append("\n");
        String py = "#!/usr/bin/env python3\nimport sys\n"
                + "answers = '''" + list + "'''.splitlines()\n"
                + "log = open(" + pyString(opsLog.toString()) + ", 'a')\n"
                + "for line in sys.stdin:\n"
                + "    log.write(line.strip().split(',')[0] + ' ' + ('base' if 'base_revision' in line else 'nobase') + '\\n'); log.flush()\n"
                + "    sys.stdout.write(answers.pop(0) + '\\n'); sys.stdout.flush()\n";
        Files.write(script, py.getBytes(StandardCharsets.UTF_8));
        Files.setPosixFilePermissions(script, PosixFilePermissions.fromString("rwxr-xr-x"));
        System.setProperty("km.bin", script.toString());
    }

    private static String pyString(String s) { return "'" + s.replace("\\", "\\\\").replace("'", "\\'") + "'"; }

    private static String full(int revision, String pairsJson, String unsat) {
        return "{\"status\":\"ok\",\"op\":\"x\",\"revision\":" + revision + ",\"receipt\":{},\"result\":{\"consistent\":true,"
                + "\"subsumptions\":" + pairsJson + ",\"unsatisfiable\":" + unsat + ",\"dropped\":0}}";
    }

    private static String delta(int revision, long base, String rows, String unsat) {
        return "{\"status\":\"ok\",\"op\":\"replace\",\"revision\":" + revision + ",\"receipt\":{},\"result\":{\"delta\":true,"
                + "\"base_revision\":" + base + ",\"consistent\":true,\"dropped\":0,\"rows\":" + rows
                + ",\"unsatisfiable\":" + unsat + "}}";
    }

    @Test
    public void emptyDeltaKeepsRowsAndReportsNoChange() throws Exception {
        fakeKm(full(1, "[[\"a\",\"b\"],[\"a\",\"c\"],[\"b\",\"c\"]]", "[]"),
               delta(2, 1, "[]", "[]"));
        try (Classifier.Session s = new Classifier.Session("Ontology()")) {
            Classifier.Result before = s.result();
            assertFalse(s.replaceRows("Ontology()"));
            assertSame(before, s.result());
            assertEquals(new TreeSet<>(Arrays.asList("a>b", "a>c", "b>c")), pairs(s));
            assertEquals(2L, s.receipt().revision);
        }
        assertEquals(Arrays.asList("{\"op\":\"init\" nobase", "{\"op\":\"replace\" base"),
                Files.readAllLines(opsLog));
    }

    @Test
    public void deltaRemovesSubjectAndPatchesRows() throws Exception {
        fakeKm(full(1, "[[\"a\",\"b\"],[\"a\",\"c\"],[\"b\",\"c\"]]", "[\"u\"]"),
               delta(2, 1, "[{\"s\":\"a\",\"o\":[]},{\"s\":\"b\",\"o\":[\"c\",\"d\"]}]", "[]"));
        try (Classifier.Session s = new Classifier.Session("Ontology()")) {
            assertTrue(s.replaceRows("Ontology()"));
            assertEquals(new TreeSet<>(Arrays.asList("b>c", "b>d")), pairs(s));
            assertEquals(new TreeSet<>(Arrays.asList("b>c", "b>d")), pairs(s.result()));
            assertTrue(s.unsatisfiable().isEmpty());
        }
    }

    @Test
    public void revisionMismatchRequestsCompleteAnswerOfTheSameRevision() throws Exception {
        fakeKm(full(1, "[[\"a\",\"b\"]]", "[]"),
               delta(2, 7, "[{\"s\":\"zzz\",\"o\":[\"q\"]}]", "[]"),   // stale: must not be applied
               full(2, "[[\"a\",\"b\"],[\"b\",\"c\"]]", "[]"),
               delta(3, 2, "[{\"s\":\"b\",\"o\":[]}]", "[]"));
        try (Classifier.Session s = new Classifier.Session("Ontology()")) {
            assertTrue(s.replaceRows("Ontology()"));
            assertEquals(new TreeSet<>(Arrays.asList("a>b", "b>c")), pairs(s));
            assertEquals(2L, s.receipt().revision);
            assertTrue(s.replaceRows("Ontology()"));       // the delta base now matches again
            assertEquals(new TreeSet<>(Arrays.asList("a>b")), pairs(s));
            assertEquals(3L, s.receipt().revision);
        }
        List<String> ops = Files.readAllLines(opsLog);
        assertEquals("{\"op\":\"classify\"} nobase", ops.get(2));
    }

    @Test
    public void failedUpdateThenDeltaAppliesToTheCommittedRows() throws Exception {
        fakeKm(full(1, "[[\"a\",\"b\"]]", "[]"),
               "{\"status\":\"error\",\"op\":\"replace\",\"error\":\"refused\"}",
               delta(2, 1, "[{\"s\":\"b\",\"o\":[\"c\"]}]", "[]"));
        try (Classifier.Session s = new Classifier.Session("Ontology()")) {
            Classifier.Result before = s.result();
            try {
                s.replaceRows("Ontology()");
                fail("refused update");
            } catch (RuntimeException expected) {
                assertTrue(expected.getMessage().contains("refused"));
            }
            assertSame(before, s.result());
            assertEquals(1L, s.receipt().revision);
            assertTrue(s.replaceRows("Ontology()"));
            assertEquals(new TreeSet<>(Arrays.asList("a>b", "b>c")), pairs(s));
        }
        // Both replaces named the committed revision 1 as their base.
        assertEquals(Arrays.asList("{\"op\":\"init\" nobase", "{\"op\":\"replace\" base", "{\"op\":\"replace\" base"),
                Files.readAllLines(opsLog));
    }
}
