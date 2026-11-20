package org.bioontology.kobayashimarust.protege;

import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
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

import static org.junit.Assert.*;

/**
 * After an interrupted or timed-out query the reasoner must answer every later
 * query as a fresh reasoner does, or throw; it must never return a partial
 * answer as complete, and it must not replay the failure of the stopped run.
 *
 * <p>The ontologies are small, so a test-only stub {@code km} delays the first
 * native run whose command line contains a given text. The stub sleeps and
 * then exits 143, as a killed process does; the reasoner stops it with
 * {@link OWLReasoner#interrupt()} or with the configured time out. The delay
 * runs longer than the 5 s (interrupt) and 2 s (time out) thresholds above
 * which the plugin used to remember the stopped run's failure.
 */
public class InterruptRecoveryTest {

    static final String NS = "http://example.org/intr#";
    private static final String HEAD = "Prefix(:=<" + NS + ">)\n"
            + "Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n"
            + "Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n";

    /**
     * A reflexive role and a forest ABox: the plugin rolls the ABox up and
     * reads property values from the classification session's rows. The
     * disjointness keeps the object property hierarchy on the native
     * {@code --properties} run (as in ore_ont_9662).
     */
    static final String REFLEXIVE = HEAD + "Ontology(<http://example.org/intr-refl>\n"
            + "Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n"
            + "Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:s)) Declaration(ObjectProperty(:t))\n"
            + "Declaration(DataProperty(:d))\n"
            + "ReflexiveObjectProperty(:r)\nSubObjectPropertyOf(:r :s)\n"
            + "SubClassOf(:A :C)\nDisjointClasses(:A :B)\n"
            + "ObjectPropertyDomain(:t :C)\n"
            + "ClassAssertion(:A :a)\nClassAssertion(:B :b)\nObjectPropertyAssertion(:t :a :b)\n"
            + "DataPropertyAssertion(:d :a \"1\"^^xsd:integer)\n"
            + ")\n";

    /** No reflexive role: realization and property values come from native runs. */
    static final String ABOX = HEAD + "Ontology(<http://example.org/intr-abox>\n"
            + "Declaration(Class(:Animal)) Declaration(Class(:Dog)) Declaration(Class(:Person))\n"
            + "Declaration(Class(:Pet)) Declaration(Class(:Owner))\n"
            + "Declaration(ObjectProperty(:ownedBy)) Declaration(ObjectProperty(:owns))\n"
            + "Declaration(ObjectProperty(:related)) Declaration(ObjectProperty(:spouse))\n"
            + "Declaration(DataProperty(:age)) Declaration(DataProperty(:num))\n"
            + "SubClassOf(:Dog :Animal)\n"
            + "EquivalentClasses(:Pet ObjectIntersectionOf(:Animal ObjectSomeValuesFrom(:ownedBy :Person)))\n"
            + "EquivalentClasses(:Owner ObjectSomeValuesFrom(:owns owl:Thing))\n"
            + "InverseObjectProperties(:owns :ownedBy)\nSubObjectPropertyOf(:ownedBy :related)\n"
            + "FunctionalObjectProperty(:spouse)\n"
            + "SubDataPropertyOf(:age :num)\nDataPropertyDomain(:age :Animal)\n"
            + "ClassAssertion(:Dog :rex)\nClassAssertion(:Person :alice)\nClassAssertion(:Person :bob)\n"
            + "ObjectPropertyAssertion(:ownedBy :rex :alice)\n"
            + "ObjectPropertyAssertion(:spouse :alice :bob)\nObjectPropertyAssertion(:spouse :alice :robert)\n"
            + "DataPropertyAssertion(:age :rex \"3\"^^xsd:integer)\n"
            + ")\n";

    @BeforeClass
    public static void locateKm() {
        HermitDifferentialTest.locateKm();
    }

    private final List<OWLReasoner> open = new ArrayList<>();
    private final ExecutorService worker = Executors.newSingleThreadExecutor(r -> {
        Thread t = new Thread(r, "interrupt-recovery-test");
        t.setDaemon(true);
        return t;
    });

    @After
    public void close() {
        for (OWLReasoner r : open) r.dispose();
        worker.shutdownNow();
    }

    // ---- interrupt() from another thread ---------------------------------------

    @Test public void reflexiveInterruptedClassification() throws Exception {
        stopAndCompare(REFLEXIVE, "incremental-source", 0);
    }

    @Test public void reflexiveInterruptedObjectPropertyClassification() throws Exception {
        stopAndCompare(REFLEXIVE, "--properties", 0);
    }

    @Test public void aboxInterruptedClassification() throws Exception {
        stopAndCompare(ABOX, "incremental-source", 0);
    }

    @Test public void aboxInterruptedRealization() throws Exception {
        stopAndCompare(ABOX, "--realize", 0);
    }

    @Test public void aboxInterruptedObjectPropertyClassification() throws Exception {
        stopAndCompare(ABOX, "--properties", 0);
    }

    @Test public void aboxInterruptedFirstReduction() throws Exception {
        stopAndCompare(ABOX, " classify ", 0);
    }

    // ---- the time out of the reasoner configuration ----------------------------

    private static final long TIME_OUT_MS = 10_000L;

    @Test public void reflexiveTimedOutObjectPropertyClassification() throws Exception {
        stopAndCompare(REFLEXIVE, "--properties", TIME_OUT_MS);
    }

    @Test public void aboxTimedOutClassification() throws Exception {
        stopAndCompare(ABOX, "incremental-source", TIME_OUT_MS);
    }

    @Test public void aboxTimedOutRealization() throws Exception {
        stopAndCompare(ABOX, "--realize", TIME_OUT_MS);
    }

    @Test public void aboxTimedOutObjectPropertyClassification() throws Exception {
        stopAndCompare(ABOX, "--properties", TIME_OUT_MS);
    }

    /**
     * Run the query battery on a reasoner whose first native run matching
     * {@code pattern} hangs, stop that run (interrupt, or the configured time
     * out when {@code timeOutMillis > 0}), and check: the battery that saw the
     * stop answers every query as a fresh reasoner does or throws the stop's
     * exception, and a second battery on the same reasoner answers every query
     * as a fresh reasoner does.
     */
    private void stopAndCompare(String ontology, String pattern, long timeOutMillis) throws Exception {
        Map<String, String> expected = battery(fresh(ontology, 0));
        Path dir = Files.createTempDirectory(Paths.get("target"), "stub-km");
        Path started = dir.resolve("started");
        Path stub = delayingStub(dir, pattern);
        String saved = System.getProperty("km.bin");
        System.setProperty("km.bin", stub.toString());
        try {
            KMReasoner k = fresh(ontology, timeOutMillis);
            // The battery thread waits after the stopped query until the stop
            // has fully run (interrupt() returned, or the time-out timer had
            // time to stop the native processes), as a caller that issues its
            // next query after the cancel does. Otherwise the next query races
            // with the stop and the outcome varies from run to run.
            java.util.concurrent.CountDownLatch stopDone = new java.util.concurrent.CountDownLatch(1);
            Runnable afterStop = timeOutMillis == 0 ? () -> await(stopDone) : () -> pause(8_000);
            Future<Map<String, String>> during = worker.submit(() -> battery(k, afterStop));
            long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(120);
            while (!Files.exists(started) && !during.isDone() && System.nanoTime() < deadline) {
                Thread.sleep(20);
            }
            assertTrue("the delayed native run for '" + pattern + "' started", Files.exists(started));
            if (timeOutMillis == 0) {
                Thread.sleep(6_000);
                k.interrupt();
                stopDone.countDown();
            }
            Map<String, String> first = during.get(240, TimeUnit.SECONDS);
            String stop = timeOutMillis == 0 ? ReasonerInterruptedException.class.getSimpleName()
                    : TimeOutException.class.getSimpleName();
            int stopped = 0;
            List<String> wrong = new ArrayList<>();
            for (Map.Entry<String, String> e : expected.entrySet()) {
                String got = first.get(e.getKey());
                if (got.equals(e.getValue())) continue;
                if (got.startsWith("throws " + stop)) {
                    stopped++;
                    continue;
                }
                wrong.add(e.getKey() + ": expected " + e.getValue() + ", got " + got);
            }
            assertTrue("at least one query was stopped", stopped >= 1);
            assertEquals("answers during the battery that was stopped", Collections.emptyList(), wrong);
            Map<String, String> after = battery(k);
            List<String> differ = new ArrayList<>();
            for (Map.Entry<String, String> e : expected.entrySet()) {
                if (!e.getValue().equals(after.get(e.getKey()))) {
                    differ.add(e.getKey() + ": expected " + e.getValue() + ", got " + after.get(e.getKey()));
                }
            }
            assertEquals("answers after the stop", Collections.emptyList(), differ);
        } finally {
            if (saved == null) System.clearProperty("km.bin"); else System.setProperty("km.bin", saved);
        }
    }

    /**
     * A stub that delays the first native run whose arguments contain
     * {@code pattern}: it records the start, sleeps, and exits 143 like a
     * killed process. Every other run executes the real km.
     */
    private static Path delayingStub(Path dir, String pattern) throws Exception {
        String real = System.getProperty("km.bin");
        Path script = dir.resolve("km");
        String body = "#!/bin/sh\n"
                + "case \" $* \" in\n"
                + "*'" + pattern + "'*)\n"
                + "  if mkdir '" + dir.resolve("claimed").toAbsolutePath() + "' 2>/dev/null; then\n"
                + "    touch '" + dir.resolve("started").toAbsolutePath() + "'\n"
                + "    sleep 120\n"
                + "    exit 143\n"
                + "  fi;;\n"
                + "esac\n"
                + "exec '" + real + "' \"$@\"\n";
        Files.write(script, body.getBytes("UTF-8"));
        assertTrue(script.toFile().setExecutable(true));
        return script.toAbsolutePath();
    }

    private KMReasoner fresh(String ontology, long timeOutMillis) throws Exception {
        OWLOntology o = IndividualsTest.parse(ontology);
        KMReasonerFactory factory = new KMReasonerFactory();
        KMReasoner r = (KMReasoner) (timeOutMillis > 0
                ? factory.createReasoner(o, new SimpleConfiguration(timeOutMillis))
                : factory.createReasoner(o));
        open.add(r);
        return r;
    }

    // ---- the query battery ---------------------------------------------------------

    private interface Query { Object run(); }

    /**
     * One query of every family, in a fixed order: class hierarchy, object and
     * data property hierarchy, types, instances, same individuals, object and
     * data property values, entailment. Each answer, or the class of the
     * exception it throws, is rendered as text.
     */
    private static Map<String, String> battery(OWLReasoner r) {
        return battery(r, null);
    }

    private static Map<String, String> battery(OWLReasoner r, Runnable afterStop) {
        OWLOntology o = r.getRootOntology();
        OWLDataFactory df = o.getOWLOntologyManager().getOWLDataFactory();
        Map<String, String> out = new LinkedHashMap<>();
        AFTER_STOP.set(afterStop);
        List<OWLClass> classes = sorted(o.getClassesInSignature());
        List<OWLObjectProperty> ops = sorted(o.getObjectPropertiesInSignature());
        List<OWLDataProperty> dps = sorted(o.getDataPropertiesInSignature());
        List<OWLNamedIndividual> inds = sorted(o.getIndividualsInSignature());

        ask(out, "consistent", () -> r.isConsistent());
        ask(out, "class sub Thing", () -> nodes(r.getSubClasses(df.getOWLThing(), false)));
        ask(out, "unsatisfiable", () -> node(r.getUnsatisfiableClasses()));
        for (OWLClass c : classes) {
            ask(out, "class supers " + c, () -> nodes(r.getSuperClasses(c, true)));
            ask(out, "class equivalents " + c, () -> node(r.getEquivalentClasses(c)));
        }
        ask(out, "object top node", () -> node(r.getTopObjectPropertyNode()));
        ask(out, "object sub top", () -> nodes(r.getSubObjectProperties(df.getOWLTopObjectProperty(), false)));
        for (OWLObjectProperty p : ops) {
            ask(out, "object supers " + p, () -> nodes(r.getSuperObjectProperties(p, false)));
        }
        ask(out, "data top node", () -> node(r.getTopDataPropertyNode()));
        ask(out, "data sub top", () -> nodes(r.getSubDataProperties(df.getOWLTopDataProperty(), false)));
        for (OWLDataProperty p : dps) {
            ask(out, "data supers " + p, () -> nodes(r.getSuperDataProperties(p, false)));
        }
        for (OWLNamedIndividual i : inds) {
            ask(out, "types " + i, () -> nodes(r.getTypes(i, false)));
            ask(out, "direct types " + i, () -> nodes(r.getTypes(i, true)));
        }
        for (OWLClass c : classes) {
            ask(out, "instances " + c, () -> nodes(r.getInstances(c, false)));
        }
        ask(out, "instances Thing", () -> nodes(r.getInstances(df.getOWLThing(), false)));
        for (OWLNamedIndividual i : inds) {
            ask(out, "same " + i, () -> node(r.getSameIndividuals(i)));
        }
        for (OWLNamedIndividual i : inds) {
            for (OWLObjectProperty p : ops) {
                ask(out, "object values " + i + " " + p, () -> nodes(r.getObjectPropertyValues(i, p)));
            }
            for (OWLDataProperty p : dps) {
                ask(out, "data values " + i + " " + p, () -> new TreeSet<>(literals(r.getDataPropertyValues(i, p))));
            }
        }
        List<OWLAxiom> axioms = new ArrayList<>();
        for (OWLNamedIndividual i : inds) {
            for (OWLObjectProperty p : ops) axioms.add(df.getOWLObjectPropertyAssertionAxiom(p, i, i));
            for (OWLClass c : classes) axioms.add(df.getOWLClassAssertionAxiom(c, i));
        }
        for (OWLClass c : classes) {
            for (OWLClass d : classes) if (!c.equals(d)) axioms.add(df.getOWLSubClassOfAxiom(c, d));
        }
        for (OWLObjectProperty p : ops) {
            for (OWLObjectProperty q : ops) if (!p.equals(q)) axioms.add(df.getOWLSubObjectPropertyOfAxiom(p, q));
        }
        for (OWLAxiom ax : axioms) {
            ask(out, "entailed " + ax, () -> r.isEntailed(ax));
        }
        return out;
    }

    private static void ask(Map<String, String> out, String key, Query q) {
        String answer;
        try {
            answer = String.valueOf(q.run());
        } catch (RuntimeException e) {
            answer = "throws " + e.getClass().getSimpleName();
            if ((e instanceof ReasonerInterruptedException || e instanceof TimeOutException)
                    && AFTER_STOP.get() != null) {
                AFTER_STOP.get().run();
                AFTER_STOP.set(null);
            }
        }
        out.put(key, answer);
    }

    /** What the battery thread does after its first stopped query. */
    private static final ThreadLocal<Runnable> AFTER_STOP = new ThreadLocal<>();

    private static void await(java.util.concurrent.CountDownLatch latch) {
        try {
            assertTrue(latch.await(120, TimeUnit.SECONDS));
        } catch (InterruptedException e) {
            throw new AssertionError(e);
        }
    }

    private static void pause(long millis) {
        try {
            Thread.sleep(millis);
        } catch (InterruptedException e) {
            throw new AssertionError(e);
        }
    }

    private static <T extends OWLEntity> List<T> sorted(Set<T> in) {
        List<T> out = new ArrayList<>(in);
        out.sort(Comparator.comparing(e -> e.getIRI().toString()));
        return out;
    }

    private static List<String> literals(Set<OWLLiteral> in) {
        List<String> out = new ArrayList<>();
        for (OWLLiteral l : in) out.add(l.toString());
        return out;
    }

    private static String node(Node<? extends OWLObject> n) {
        List<String> one = new ArrayList<>();
        for (OWLObject e : n.getEntities()) one.add(e.toString());
        Collections.sort(one);
        return one.toString();
    }

    private static Set<String> nodes(NodeSet<? extends OWLObject> ns) {
        Set<String> out = new TreeSet<>();
        for (Node<? extends OWLObject> n : ns.getNodes()) out.add(node(n));
        return out;
    }
}
