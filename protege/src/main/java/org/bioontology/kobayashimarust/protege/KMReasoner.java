package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNode;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNode;
import org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNodeSet;
import org.semanticweb.owlapi.util.Version;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;

import java.util.*;

/**
 * An {@link OWLReasoner} backed by the Kobayashi-MaRust SROIQ context engine.
 * It computes the named-class hierarchy and unsatisfiable classes. It answers
 * the individual queries ({@code getTypes}, {@code getInstances} for named
 * classes, {@code getSameIndividuals}) from {@code km classify --realize},
 * which it runs once per ontology revision on the first such query. It
 * answers the object property queries (hierarchy, equivalents, inverses,
 * domains, ranges) from {@code km classify --properties}, likewise run once
 * per revision, only when a property query or a precompute of
 * {@code OBJECT_PROPERTY_HIERARCHY} needs it.
 *
 * <p>A query the plugin cannot answer soundly and completely throws
 * {@link UnsupportedOperationException} (or {@link UnsupportedEntailmentTypeException}
 * for {@code isEntailed}); it never returns an empty or guessed answer. The
 * class hierarchy follows HermiT's conventions: owl:Nothing is a strict
 * subclass of every satisfiable class, the bottom node holds owl:Nothing and
 * the unsatisfiable classes, and a leaf class has the bottom node as its
 * direct subclass. The data property hierarchy and the data property domains
 * come from {@link DataPropertyModel} for the ontologies inside its fragment
 * and throw outside it.
 */
public class KMReasoner extends org.semanticweb.owlapi.reasoner.impl.OWLReasonerBase {

    private final OWLDataFactory df;
    private final OWLClass owlThing;
    private final OWLClass owlNothing;

    private static final int[] EMPTY_INTS = new int[0];
    private static final IRI NOT_DECIDED_PROFILE = IRI.create("http://www.w3.org/ns/owl-profile/DL");

    private boolean consistent = true;
    private int dropped = 0;
    private OWLClass[] classById = new OWLClass[0];
    private final Map<OWLClass, Integer> idByClass = new HashMap<>();
    private final Map<String, Integer> idByIri = new HashMap<>();
    private int[][] rawSup = new int[0][];
    private int[] repId = EMPTY_INTS;
    private OWLClassNode[] nodeByRepId = new OWLClassNode[0];
    private int[][] supersByRep = new int[0][];
    private int[][] subsByRep;
    private int thingId = -1;
    private int nothingId = -1;
    private final Set<OWLClass> unsatisfiable = new HashSet<>();
    private volatile Classifier.Session incrementalSession;
    private final RetainedFunctionalSyntax serialized = new RetainedFunctionalSyntax();
    private boolean sourceSynchronized;
    /**
     * True once one classification has committed an answer. It never goes back
     * to false: a later failed transaction keeps the previous answers. Before
     * it is true the reasoner holds no native session and no taxonomy; the
     * first query or precomputeInferences classifies the ontology as it is
     * then.
     */
    private volatile boolean classified;
    private Set<OWLOntology> committedImports = Collections.emptySet();
    private boolean lastPreparationUsedDelta;
    private boolean hierarchyBuilt;
    private Set<OWLClass> lastPreparedClasses;
    private Set<OWLClass> lastClasses;
    private FlushContext flushContext;
    /** Individual realization of the committed revision; null until first needed. */
    private volatile Realized realized;
    /** Object property hierarchy of the committed revision; null until first needed. */
    private volatile ObjectPropertyModel propertyModel;
    /** Data property hierarchy of the committed revision; null until first needed. */
    private volatile DataPropertyModel dataModel;
    /**
     * The failure of the last native run of each kind on the current ontology
     * version. A later call rethrows it without a new run, until the ontology
     * changes or flush() runs (or, for realization, properties and the data
     * model, the next classification commits).
     */
    private volatile RuntimeException classificationFailure;
    private volatile RuntimeException realizeFailure;
    private volatile RuntimeException propertiesFailure;
    private volatile RuntimeException dataFailure;
    /** The one-shot native process of a running realization or property run. */
    private volatile Process realizeProcess;
    /** True while a monitored task runs; interrupt() acts only then. */
    private volatile boolean taskRunning;
    private volatile boolean interruptRequested;
    private volatile boolean timedOut;
    /** Identifies the running task so a late timer cannot hit the next one. */
    private volatile long taskGeneration;
    private int taskDepth;
    private static final java.util.concurrent.ScheduledExecutorService TIMER =
            java.util.concurrent.Executors.newSingleThreadScheduledExecutor(runnable -> {
                Thread thread = new Thread(runnable, "km-reasoner-timeout");
                thread.setDaemon(true);
                return thread;
            });

    private static final class FlushContext {
        final boolean allowDelta;
        boolean handled;
        FlushContext(boolean allowDelta) { this.allowDelta = allowDelta; }
    }

    boolean lastPreparationUsedDelta() { return lastPreparationUsedDelta; }

    protected KMReasoner(OWLOntology rootOntology, OWLReasonerConfiguration config,
                         BufferingMode bufferingMode) {
        super(rootOntology, config, bufferingMode);
        this.df = rootOntology.getOWLOntologyManager().getOWLDataFactory();
        this.owlThing = df.getOWLThing();
        this.owlNothing = df.getOWLNothing();
        // No native work here. Protege stores the reasoner only after this
        // constructor returns, and interrupt() can reach it only then. The
        // first query or precomputeInferences classifies (as HermiT does).
    }

    // ---- classification -------------------------------------------------

    private synchronized void classify() { classify(null, null); }

    /**
     * Run native work the way HermiT runs a task: report to the progress
     * monitor of the configuration (started, busy, stopped), end it with
     * {@link TimeOutException} once {@code getTimeOut()} milliseconds have
     * passed, and end it with {@link ReasonerInterruptedException} when
     * {@link #interrupt()} was called. Protege catches only the latter, so a
     * killed native process must not surface as a plain failure. Callers hold
     * the reasoner monitor; nested calls join the outer task.
     */
    private void runTask(String title, Runnable work) {
        if (taskDepth > 0) {
            work.run();
            return;
        }
        ReasonerProgressMonitor monitor = getReasonerConfiguration().getProgressMonitor();
        long limit = getTimeOut();
        long generation = ++taskGeneration;
        interruptRequested = false;
        timedOut = false;
        taskDepth++;
        taskRunning = true;
        java.util.concurrent.ScheduledFuture<?> timer = null;
        if (monitor != null) {
            monitor.reasonerTaskStarted(title);
            monitor.reasonerTaskBusy();
        }
        try {
            if (limit > 0 && limit < Long.MAX_VALUE) {
                timer = TIMER.schedule(() -> {
                    if (taskGeneration == generation) {
                        timedOut = true;
                        killNative();
                    }
                }, limit, java.util.concurrent.TimeUnit.MILLISECONDS);
            }
            try {
                work.run();
            } catch (RuntimeException failure) {
                throw translate(failure);
            }
        } finally {
            if (timer != null) timer.cancel(false);
            taskRunning = false;
            taskDepth--;
            taskGeneration++;
            if (monitor != null) monitor.reasonerTaskStopped();
            interruptRequested = false;
            timedOut = false;
        }
    }

    private RuntimeException translate(RuntimeException failure) {
        if (failure instanceof ReasonerInterruptedException || failure instanceof TimeOutException) {
            return failure;
        }
        if (timedOut) {
            return new TimeOutException("Kobayashi-MaRust exceeded the time out of "
                    + getTimeOut() + " ms");
        }
        if (interruptRequested || Thread.interrupted()) {
            return new ReasonerInterruptedException(failure);
        }
        return failure;
    }

    /** Stop the native work of the running task. Does not wait for the reasoner monitor. */
    private void killNative() {
        Process realizing = realizeProcess;
        if (realizing != null) NativeProcessTree.terminateAndWait(realizing);
        Classifier.Session session = incrementalSession;
        if (session != null) {
            session.interrupt();
            if (incrementalSession == session) incrementalSession = null;
        }
    }

    /**
     * Run the first classification if it has not happened. The ontology
     * changes buffered since construction are folded into this run: they are
     * dropped from the pending list first, because the run reads the ontology
     * as it is now.
     */
    private synchronized void ensureClassified() {
        if (classified) return;
        if (!getPendingChanges().isEmpty()) flush();
        if (classificationFailure != null) throw classificationFailure;
        try {
            runTask(ReasonerProgressMonitor.CLASSIFYING, this::classify);
        } catch (RuntimeException failure) {
            if (cacheable(failure)) classificationFailure = failure;
            throw failure;
        }
    }

    /**
     * Whether a failed run is remembered for the current ontology version. An
     * interrupt or a time out comes from the caller, not from the ontology, so
     * the next call starts a new run.
     */
    private static boolean cacheable(RuntimeException failure) {
        return !(failure instanceof ReasonerInterruptedException || failure instanceof TimeOutException);
    }

    private void forgetFailures() {
        classificationFailure = null;
        realizeFailure = null;
        propertiesFailure = null;
        dataFailure = null;
    }

    private void classify(Set<OWLAxiom> added, Set<OWLAxiom> removed) {
        try {
            classifySource(added, removed);
            sourceSynchronized = true;
            classified = true;
        } catch (RuntimeException | Error failure) {
            sourceSynchronized = false;
            throw failure;
        }
    }

    private void classifySource(Set<OWLAxiom> added, Set<OWLAxiom> removed) {
        OWLOntology ont = getRootOntology();
        final RetainedFunctionalSyntax.Prepared prepared;
        final String candidateSource;
        try {
            prepared = added == null ? serialized.prepare(ont) : serialized.prepare(ont, added, removed);
            candidateSource = prepared.source;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }

        // Whether the native answer differs from the one the Java hierarchy was built from.
        boolean answerChanged;
        Classifier.Session session;
        try {
            if (incrementalSession == null) {
                // Register the session as soon as its process runs, so interrupt()
                // reaches the first (longest) transaction too.
                incrementalSession = new Classifier.Session(candidateSource, s -> {
                    incrementalSession = s;
                    // An interrupt or time out that came before the process existed.
                    if (interruptRequested || timedOut) s.interrupt();
                });
                answerChanged = true;
            } else {
                answerChanged = incrementalSession.replaceRows(candidateSource);
            }
            session = incrementalSession;
        } catch (Exception e) {
            // A protocol failure may have terminated the native process. Drop
            // the handle so a later OWLAPI flush can start a clean session;
            // the last committed Java hierarchy remains untouched.
            if (incrementalSession != null) {
                incrementalSession.close();
                incrementalSession = null;
            }
            throw new ReasonerInternalException(e);
        }
        // The native transaction has succeeded. Commit the retained source
        // state now; preparation and native refusal never mutate this cache.
        serialized.commit(prepared);
        committedImports = prepared.imports;
        // Class ids are rebuilt below and the ABox may have changed, so the
        // realization of the previous revision no longer applies.
        realized = null;
        propertyModel = null;
        dataModel = null;
        realizeFailure = null;
        propertiesFailure = null;
        dataFailure = null;
        // Commit the Java-side hierarchy only after the native transaction has
        // succeeded. A declined update therefore leaves the preceding answers
        // intact, matching the native session's atomic revision contract.
        // The hierarchy is a function of the retained rows, the unsatisfiable
        // classes, consistency and the declared class set; when none changed
        // (an empty row delta) the built hierarchy is already exact.
        boolean samePreparedClasses = lastPreparedClasses != null && lastPreparedClasses == prepared.classes;
        Set<OWLClass> classes;
        if (samePreparedClasses && lastClasses != null) {
            classes = lastClasses;
        } else {
            classes = new HashSet<>(prepared.classes);
            classes.add(owlThing); classes.add(owlNothing);
        }
        boolean classSetChanged = lastClasses == null || (classes != lastClasses && !lastClasses.equals(classes));
        if (!hierarchyBuilt || answerChanged || classSetChanged) {
            boolean incremental = hierarchyBuilt && !classSetChanged && session.lastDeltaSubjects() != null;
            hierarchyBuilt = false;
            rebuildHierarchy(session, classes, incremental);
            lastPreparedClasses = prepared.classes;
            lastClasses = classes;
            hierarchyBuilt = true;
        }
        lastPreparationUsedDelta = prepared.usedSuppliedDelta;
    }

    private int[] encodeRow(int a, String[] vals) {
        if (vals == null || vals.length == 0) {
            return a == thingId ? EMPTY_INTS : new int[]{thingId};
        }
        int[] buf = new int[vals.length + 1];
        int count = 0;
        for (String o : vals) {
            Integer bBox = idByIri.get(normalizeIri(o));
            if (bBox != null && bBox != a) {
                buf[count++] = bBox;
            }
        }
        if (a != thingId) {
            buf[count++] = thingId;
        }
        Arrays.sort(buf, 0, count);
        int u = 0;
        for (int i = 0; i < count; i++) {
            if (i == 0 || buf[i] != buf[i - 1]) buf[u++] = buf[i];
        }
        return u == buf.length ? buf : Arrays.copyOf(buf, u);
    }

    private void rebuildHierarchy(Classifier.Session session, Set<OWLClass> classes, boolean incremental) {
        subsByRep = null;
        consistent = session.consistent();
        dropped = session.dropped();

        int n = classes.size();
        if (!incremental || classById.length != n || rawSup.length != n) {
            unsatisfiable.clear();
            classById = new OWLClass[n];
            idByClass.clear();
            idByIri.clear();
            int idx = 0;
            for (OWLClass c : classes) {
                classById[idx] = c;
                idByClass.put(c, idx);
                idByIri.put(c.getIRI().toString(), idx);
                idx++;
            }
            thingId = idByClass.get(owlThing);
            nothingId = idByClass.get(owlNothing);

            for (String u : session.unsatisfiable()) {
                Integer uId = idByIri.get(normalizeIri(u));
                if (uId != null) unsatisfiable.add(classById[uId]);
            }

            rawSup = new int[n][];
            for (int i = 0; i < n; i++) {
                rawSup[i] = i == thingId ? EMPTY_INTS : new int[]{thingId};
            }
            for (Map.Entry<String, String[]> row : session.rows().entrySet()) {
                Integer aBox = idByIri.get(normalizeIri(row.getKey()));
                if (aBox == null) continue;
                int a = aBox;
                rawSup[a] = encodeRow(a, row.getValue());
            }
        } else {
            if (session.lastUnsatOrConsistentChanged()) {
                unsatisfiable.clear();
                for (String u : session.unsatisfiable()) {
                    Integer uId = idByIri.get(normalizeIri(u));
                    if (uId != null) unsatisfiable.add(classById[uId]);
                }
            }
            Map<String, String[]> sessionRows = session.rows();
            for (String sIri : session.lastDeltaSubjects()) {
                Integer aBox = idByIri.get(normalizeIri(sIri));
                if (aBox == null) continue;
                int a = aBox;
                rawSup[a] = encodeRow(a, sessionRows.get(sIri));
            }
        }

        // Equivalence = mutual subsumption (union-find by representative ID)
        repId = new int[n];
        for (int i = 0; i < n; i++) repId[i] = i;
        for (int c = 0; c < n; c++) {
            for (int d : rawSup[c]) {
                if (c < d && Arrays.binarySearch(rawSup[d], c) >= 0) {
                    unionId(c, d);
                }
            }
        }
        for (OWLClass u : unsatisfiable) {
            Integer uId = idByClass.get(u);
            if (uId != null) unionId(uId, nothingId);
        }
        for (int i = 0; i < n; i++) findId(i);

        @SuppressWarnings("unchecked")
        Set<OWLClass>[] groups = new Set[n];
        for (int c = 0; c < n; c++) {
            int r = repId[c];
            if (groups[r] == null) groups[r] = new HashSet<>();
            groups[r].add(classById[c]);
        }
        nodeByRepId = new OWLClassNode[n];
        for (int r = 0; r < n; r++) {
            if (groups[r] != null) nodeByRepId[r] = new OWLClassNode(groups[r]);
        }

        // Condensed proper supers over representatives
        supersByRep = new int[n][];
        for (int c = 0; c < n; c++) {
            int rc = repId[c];
            if (supersByRep[rc] != null) continue;
            int[] s = rawSup[c];
            int[] buf = new int[s.length];
            int count = 0;
            for (int d : s) {
                int rd = repId[d];
                if (rc != rd && rd != repId[nothingId]) buf[count++] = rd;
            }
            Arrays.sort(buf, 0, count);
            int u = 0;
            for (int i = 0; i < count; i++) {
                if (i == 0 || buf[i] != buf[i - 1]) buf[u++] = buf[i];
            }
            supersByRep[rc] = u == 0 ? EMPTY_INTS : (u == buf.length ? buf : Arrays.copyOf(buf, u));
        }
        // The bottom node sits below every other node. The queries add that edge
        // themselves (bottomSupers, bottom as a sub class), so no array holds it.
        supersByRep[repId[nothingId]] = EMPTY_INTS;
    }

    private int findId(int c) {
        int r = repId[c];
        while (r != repId[r]) r = repId[r];
        int cur = c;
        while (cur != r) {
            int next = repId[cur];
            repId[cur] = r;
            cur = next;
        }
        return r;
    }

    private void unionId(int a, int b) {
        int ra = findId(a), rb = findId(b);
        if (ra != rb) repId[ra] = rb;
    }

    private static String normalizeIri(String iri) {
        if (iri.length() >= 2 && iri.charAt(0) == '<'
                && iri.charAt(iri.length() - 1) == '>') {
            return iri.substring(1, iri.length() - 1);
        }
        return iri;
    }

    /**
     * HermiT's checkPreConditions: queries on an inconsistent ontology throw
     * {@link InconsistentOntologyException} (Reasoner.throwInconsistentOntologyExceptionIfNecessary).
     * Protege catches it around the classification run and opens its
     * inconsistency explanation. isConsistent does not throw here;
     * getTopClassNode, getBottomClassNode and getUnsatisfiableClasses do, as
     * in HermiT 1.4.3 (parity run of 2026-11-14, ore_ont_5014).
     */
    private void checkPreConditions() {
        ensureClassified();
        if (!consistent) throw new InconsistentOntologyException();
    }

    // ---- node helpers ---------------------------------------------------

    private OWLClassNode nodeOfId(int r) {
        OWLClassNode node = nodeByRepId[r];
        return node != null ? node : new OWLClassNode(Collections.singleton(classById[r]));
    }

    private int repIdOf(OWLClassExpression ce) {
        if (ce.isOWLThing()) return repId[thingId];
        if (ce.isOWLNothing()) return repId[nothingId];
        if (ce instanceof OWLClass) {
            Integer id = idByClass.get((OWLClass) ce);
            return id != null ? repId[id] : -1;
        }
        return -1; // complex expressions are not classified
    }

    private int[][] ensureSubsByRep() {
        if (subsByRep == null) {
            int n = classById.length;
            int[] counts = new int[n];
            for (int r = 0; r < n; r++) {
                int[] sups = supersByRep[r];
                if (sups != null) {
                    for (int sup : sups) counts[sup]++;
                }
            }
            int[][] built = new int[n][];
            for (int r = 0; r < n; r++) {
                built[r] = counts[r] == 0 ? EMPTY_INTS : new int[counts[r]];
            }
            int[] pos = new int[n];
            for (int r = 0; r < n; r++) {
                int[] sups = supersByRep[r];
                if (sups != null) {
                    for (int sup : sups) built[sup][pos[sup]++] = r;
                }
            }
            subsByRep = built;
        }
        return subsByRep;
    }

    // ---- class hierarchy queries ---------------------------------------

    @Override public synchronized Node<OWLClass> getTopClassNode() {
        checkPreConditions();
        return nodeOfId(repId[thingId]);
    }
    @Override public synchronized Node<OWLClass> getBottomClassNode() {
        checkPreConditions();
        return nodeOfId(repId[nothingId]);
    }

    /**
     * A named class outside the signature. HermiT's default FreshEntityPolicy
     * (ALLOW) gives it a node of its own with owl:Thing above and owl:Nothing
     * below (Reasoner.getHierarchyNode); isEntailed follows the same shape.
     */
    private boolean isFresh(OWLClassExpression ce) {
        return ce instanceof OWLClass && !ce.isOWLThing() && !ce.isOWLNothing()
                && !idByClass.containsKey((OWLClass) ce);
    }

    private static UnsupportedOperationException unsupported(String query, String argument) {
        return new UnsupportedOperationException("Kobayashi-MaRust does not answer " + query
                + " for " + argument + " yet: the answer needs reasoning the plugin does not run");
    }

    /**
     * The taxonomy holds named classes only. A class expression argument needs
     * the engine (a fresh class defined as the expression, then a new
     * classification), so it throws instead of returning an empty or partial
     * answer.
     */
    private static void requireNamed(OWLClassExpression ce, String query) {
        if (ce.isAnonymous()) throw unsupported(query, "the class expression " + ce);
    }

    @Override public synchronized Node<OWLClass> getEquivalentClasses(OWLClassExpression ce) {
        checkPreConditions();
        requireNamed(ce, "getEquivalentClasses");
        if (isFresh(ce)) return new OWLClassNode(Collections.singleton(ce.asOWLClass()));
        int r = repIdOf(ce);
        if (r < 0) throw new IllegalStateException("a class of the signature has no node: " + ce);
        return nodeOfId(r);
    }

    /** The representatives of every node (one per equivalence class), the bottom node excluded. */
    private int[] nonBottomReps() {
        int bottom = repId[nothingId];
        int[] buf = new int[repId.length];
        int count = 0;
        for (int c = 0; c < repId.length; c++) {
            if (repId[c] == c && c != bottom) buf[count++] = c;
        }
        return Arrays.copyOf(buf, count);
    }

    @Override public synchronized NodeSet<OWLClass> getSuperClasses(OWLClassExpression ce, boolean direct) {
        checkPreConditions();
        requireNamed(ce, "getSuperClasses");
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (isFresh(ce)) {
            ns.addNode(nodeOfId(repId[thingId]));
            return ns;
        }
        int r = repIdOf(ce);
        if (r == repId[nothingId]) {
            // Every other node is above the bottom node; the direct ones are the leaves.
            int[][] subs = ensureSubsByRep();
            for (int s : nonBottomReps()) {
                if (!direct || subs[s].length == 0) ns.addNode(nodeOfId(s));
            }
            return ns;
        }
        int[] all = supersByRep[r];
        if (all == null || all.length == 0) return ns;
        if (!direct) {
            for (int s : all) ns.addNode(nodeOfId(s));
        } else {
            for (int s : minimalIds(all)) ns.addNode(nodeOfId(s));
        }
        return ns;
    }

    @Override public synchronized NodeSet<OWLClass> getSubClasses(OWLClassExpression ce, boolean direct) {
        checkPreConditions();
        requireNamed(ce, "getSubClasses");
        OWLClassNodeSet ns = new OWLClassNodeSet();
        Node<OWLClass> bottom = nodeOfId(repId[nothingId]);
        if (isFresh(ce)) {
            ns.addNode(bottom);
            return ns;
        }
        int r = repIdOf(ce);
        if (r == repId[nothingId]) return ns;
        int[][] subs = ensureSubsByRep();
        int[] all = subs[r];
        if (all == null || all.length == 0) {
            // A leaf: the bottom node is its only sub node.
            ns.addNode(bottom);
            return ns;
        }
        if (!direct) {
            for (int s : all) ns.addNode(nodeOfId(s));
            ns.addNode(bottom);
        } else {
            for (int s : maximalIds(all, subs)) ns.addNode(nodeOfId(s));
        }
        return ns;
    }

    /** super-reps with no intermediate (direct supers). */
    private int[] minimalIds(int[] set) {
        int[] buf = new int[set.length];
        int count = 0;
        for (int x : set) {
            boolean isDirect = true;
            for (int y : set) {
                if (x != y) {
                    int[] ySups = supersByRep[y];
                    if (ySups != null && Arrays.binarySearch(ySups, x) >= 0) {
                        isDirect = false;
                        break;
                    }
                }
            }
            if (isDirect) buf[count++] = x;
        }
        return count == buf.length ? buf : Arrays.copyOf(buf, count);
    }

    /** sub-reps with no intermediate (direct subs). */
    private int[] maximalIds(int[] set, int[][] subs) {
        int[] buf = new int[set.length];
        int count = 0;
        for (int x : set) {
            boolean isDirect = true;
            for (int y : set) {
                if (x != y) {
                    int[] ySubs = subs[y];
                    if (ySubs != null && Arrays.binarySearch(ySubs, x) >= 0) {
                        isDirect = false;
                        break;
                    }
                }
            }
            if (isDirect) buf[count++] = x;
        }
        return count == buf.length ? buf : Arrays.copyOf(buf, count);
    }

    @Override public synchronized Node<OWLClass> getUnsatisfiableClasses() {
        checkPreConditions();
        return nodeOfId(repId[nothingId]);
    }

    @Override public synchronized boolean isConsistent() {
        ensureClassified();
        return consistent;
    }

    @Override public synchronized boolean isSatisfiable(OWLClassExpression ce) {
        checkPreConditions();
        if (ce.isAnonymous()) {
            // The taxonomy cannot decide an anonymous expression, and answering
            // "satisfiable" would be wrong for unsatisfiable ones. Protege's
            // frame sections and DL Query catch exceptions from the reasoner;
            // ClassExpressionNotInProfileException is the one the OWLReasoner
            // interface declares for isSatisfiable.
            // TODO W5: decide anonymous expressions with a fresh definition Q = CE.
            throw new ClassExpressionNotInProfileException(ce, NOT_DECIDED_PROFILE);
        }
        if (ce.isOWLNothing()) return false;
        int r = repIdOf(ce);
        if (r < 0) return true; // a class outside the signature is satisfiable
        return r != repId[nothingId];
    }

    /** convenience for tests: dropped-clause count from the last classification. */
    public synchronized int getDroppedClauseCount() {
        ensureClassified();
        return dropped;
    }

    /** Last native transaction receipt; null for the initial revision. */
    public synchronized Classifier.IncrementalReceipt getLastIncrementalReceipt() {
        return incrementalSession == null ? null : incrementalSession.receipt();
    }

    /** A detached copy of the source snapshot backing the current answers. */
    public synchronized OWLOntology getCommittedOntologySnapshot() {
        ensureClassified();
        if (!serialized.hasCommittedRevision()) {
            throw new ReasonerInternalException("KM has no committed ontology revision");
        }
        try {
            return serialized.committedSnapshot();
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
    }

    /**
     * Create an OWL Explanation API generator bound to this reasoner's current
     * committed revision. Pending buffered changes remain invisible until
     * {@link #flush()} succeeds.
     */
    public synchronized ExplanationGenerator<OWLAxiom> createExplanationGenerator() {
        return new KMExplanationGeneratorFactory().createExplanationGenerator(this);
    }

    // ---- precompute / metadata -----------------------------------------

    @Override public String getReasonerName() { return "Kobayashi-MaRust"; }
    @Override public Version getReasonerVersion() { return versionOf(KMExecutable.pluginVersion()); }

    /** Parse "1.6.4" or "1.7.0-rc1" into a Version; "dev" and unparsable text give 0.0.0.0. */
    static Version versionOf(String text) {
        int[] part = new int[3];
        String[] pieces = text.split("[.\\-+]");
        for (int i = 0; i < 3 && i < pieces.length; i++) {
            try {
                part[i] = Integer.parseInt(pieces[i]);
            } catch (NumberFormatException e) {
                break;
            }
        }
        return new Version(part[0], part[1], part[2], 0);
    }

    @Override public synchronized void precomputeInferences(InferenceType... types) {
        checkPreConditions();
        // checkPreConditions has classified. Individual inferences and the
        // object property hierarchy cost one more native run each, made on demand.
        for (InferenceType type : types) {
            if (type == InferenceType.CLASS_ASSERTIONS || type == InferenceType.SAME_INDIVIDUAL) {
                ensureRealized();
            } else if (type == InferenceType.OBJECT_PROPERTY_HIERARCHY) {
                ensureProperties();
            } else if (type == InferenceType.DATA_PROPERTY_HIERARCHY && dataHierarchyInFragment()) {
                try {
                    ensureDataProperties();
                } catch (UnsupportedOperationException outsideFragment) {
                    // The taxonomy does not decide this ontology's data property
                    // hierarchy; the query throws the same exception. A request
                    // to precompute a type the reasoner cannot compute is ignored.
                }
            }
            // The remaining types (object property assertions, data property
            // assertions, different individuals, disjoint classes, ...) are
            // not computed; their queries throw.
        }
    }
    /**
     * True only for a type whose answer is held now: the class hierarchy once
     * classified, the individual types once realized, the object property
     * hierarchy once classified. Every other type is
     * not computed at all. Not synchronized: Protege may ask while a
     * classification runs on another thread.
     */
    @Override public boolean isPrecomputed(InferenceType inferenceType) {
        if (inferenceType == InferenceType.CLASS_HIERARCHY) return classified;
        if (inferenceType == InferenceType.CLASS_ASSERTIONS
                || inferenceType == InferenceType.SAME_INDIVIDUAL) {
            return realized != null;
        }
        if (inferenceType == InferenceType.OBJECT_PROPERTY_HIERARCHY) {
            return propertyModel != null;
        }
        if (inferenceType == InferenceType.DATA_PROPERTY_HIERARCHY) {
            return dataModel != null;
        }
        return false;
    }
    /**
     * The types this reasoner computes. HermiT lists six; KM lists the class
     * hierarchy, the object property hierarchy, the individual types and
     * equalities, and the data property hierarchy for an ontology inside the
     * fragment of {@link DataPropertyModel}. Object and data property
     * assertions are not computed, so they are not listed (Protege
     * precomputes only the types a reasoner lists).
     */
    @Override public Set<InferenceType> getPrecomputableInferenceTypes() {
        Set<InferenceType> types = new HashSet<>(Arrays.asList(InferenceType.CLASS_HIERARCHY,
                InferenceType.OBJECT_PROPERTY_HIERARCHY,
                InferenceType.CLASS_ASSERTIONS, InferenceType.SAME_INDIVIDUAL));
        if (dataHierarchyInFragment()) types.add(InferenceType.DATA_PROPERTY_HIERARCHY);
        return types;
    }

    /** Syntactic test on the ontology as the reasoner will read it (pending edits included). */
    private boolean dataHierarchyInFragment() {
        return DataPropertyModel.outsideFragment(getRootOntology()) == null;
    }

    @Override public synchronized void flush() {
        // A flush is the caller's request to look at the ontology again, so a
        // remembered failure no longer applies.
        forgetFailures();
        if (!classified) {
            // Nothing is committed yet, so there is nothing to update: drop the
            // pending list (handleChanges ignores it) and let the first
            // classification read the ontology as it is.
            super.flush();
            return;
        }
        // Nothing pending and in step with the native session: nothing to do,
        // so no progress report either.
        if (getPendingChanges().isEmpty() && sourceSynchronized
                && RetainedFunctionalSyntax.importsView(getRootOntology()).equals(committedImports)) {
            return;
        }
        runTask(ReasonerProgressMonitor.CLASSIFYING, this::flushClassified);
    }

    private void flushClassified() {
        // OWLReasonerBase advances its private bookkeeping before handleChanges
        // succeeds. Its effective delta is usable only while both revisions agree.
        Set<OWLOntology> closure = RetainedFunctionalSyntax.importsView(getRootOntology());
        boolean safe = sourceSynchronized && closure.equals(committedImports);
        for (OWLOntologyChange change : getPendingChanges()) {
            if (!closure.contains(change.getOntology()) && !committedImports.contains(change.getOntology()))
                continue; // unrelated ontology in the same source manager
            if (!(change instanceof AddAxiom) && !(change instanceof RemoveAxiom)) {
                safe = false;
            } else if (!RetainedFunctionalSyntax.safeDeltaAxiom(change.getAxiom())) {
                safe = false;
            }
        }
        FlushContext previous = flushContext;
        FlushContext current = new FlushContext(safe);
        flushContext = current;
        try {
            super.flush();
            // Empty base diffs can suppress the callback after a failed native
            // revision, or for annotations/ontology identity/import changes.
            if (!current.handled && !safe) classify();
        } catch (RuntimeException | Error failure) {
            sourceSynchronized = false;
            throw failure;
        } finally {
            flushContext = previous;
        }
    }

    @Override protected void handleChanges(Set<OWLAxiom> addAxioms, Set<OWLAxiom> removeAxioms) {
        FlushContext context = flushContext;
        if (context != null) context.handled = true;
        if (!classified) return;
        if (context != null && context.allowDelta) classify(addAxioms, removeAxioms);
        else classify();
    }

    /**
     * Cancel the running classification, realization or property run. Like HermiT's
     * interrupt flag it has no effect when nothing runs, and the thread that
     * computes then fails with {@link ReasonerInterruptedException}. Not
     * synchronized: the computing thread holds the reasoner monitor.
     */
    @Override public void interrupt() {
        if (!taskRunning) return;
        interruptRequested = true;
        killNative();
    }

    @Override public synchronized void dispose() {
        if (incrementalSession != null) {
            incrementalSession.close();
            incrementalSession = null;
        }
        super.dispose();
    }

    // ---- entailment ----------------------------------------------------

    @Override public synchronized boolean isEntailed(OWLAxiom axiom) {
        checkPreConditions();
        // Declarations and annotation axioms have no model-theoretic content, so
        // every ontology entails them (HermiT answers true for them too).
        if (!axiom.isLogicalAxiom()) return true;
        if (axiom instanceof OWLClassAssertionAxiom) return isEntailedClassAssertion((OWLClassAssertionAxiom) axiom);
        if (axiom instanceof OWLSameIndividualAxiom) return isEntailedSameIndividual((OWLSameIndividualAxiom) axiom);
        if (axiom instanceof OWLSubObjectPropertyOfAxiom
                || axiom instanceof OWLEquivalentObjectPropertiesAxiom
                || axiom instanceof OWLInverseObjectPropertiesAxiom
                || axiom instanceof OWLSymmetricObjectPropertyAxiom
                || axiom instanceof OWLObjectPropertyDomainAxiom
                || axiom instanceof OWLObjectPropertyRangeAxiom) {
            return isEntailedObjectPropertyAxiom(axiom);
        }
        if (!(axiom instanceof OWLSubClassOfAxiom)) {
            throw new UnsupportedEntailmentTypeException(axiom);
        }
        OWLSubClassOfAxiom subClassOf = (OWLSubClassOfAxiom) axiom;
        if (subClassOf.getSubClass().isAnonymous()
                || subClassOf.getSuperClass().isAnonymous()) {
            throw new UnsupportedEntailmentTypeException(axiom);
        }
        OWLClass sub = subClassOf.getSubClass().asOWLClass();
        OWLClass sup = subClassOf.getSuperClass().asOWLClass();
        // Bottom and an unsatisfiable named class entail every class.
        if (sub.isOWLNothing() || sup.isOWLThing() || sub.equals(sup)) {
            return true;
        }
        int subRep = repIdOf(sub);
        if (subRep >= 0 && subRep == repId[nothingId]) return true;
        int supRep = repIdOf(sup);
        // A class outside the signature is only below owl:Thing and above
        // owl:Nothing (and unsatisfiable classes, handled above).
        if (subRep < 0 && supRep < 0) return false;
        if (subRep < 0) return supRep == repId[thingId];
        if (supRep < 0) return false;
        if (subRep == supRep) return true;
        int[] sups = supersByRep[subRep];
        return sups != null && Arrays.binarySearch(sups, supRep) >= 0;
    }

    @Override public synchronized boolean isEntailed(Set<? extends OWLAxiom> axioms) {
        checkPreConditions();
        // HermiT's EntailmentChecker.entails(Set) skips non-logical axioms
        // (annotations, declarations); they hold in every ontology.
        for (OWLAxiom a : axioms) {
            if (a.isLogicalAxiom() && !isEntailed(a)) return false;
        }
        return true;
    }

    @Override public boolean isEntailmentCheckingSupported(AxiomType<?> axiomType) {
        if (!axiomType.isLogical()) return true;
        return AxiomType.SUBCLASS_OF.equals(axiomType)
                || AxiomType.CLASS_ASSERTION.equals(axiomType)
                || AxiomType.SAME_INDIVIDUAL.equals(axiomType)
                || AxiomType.SUB_OBJECT_PROPERTY.equals(axiomType)
                || AxiomType.EQUIVALENT_OBJECT_PROPERTIES.equals(axiomType)
                || AxiomType.INVERSE_OBJECT_PROPERTIES.equals(axiomType)
                || AxiomType.SYMMETRIC_OBJECT_PROPERTY.equals(axiomType)
                || AxiomType.OBJECT_PROPERTY_DOMAIN.equals(axiomType)
                || AxiomType.OBJECT_PROPERTY_RANGE.equals(axiomType);
    }


    // ---- individuals (from km classify --realize) -----------------------

    /**
     * Entailed types and equalities of the named individuals at the committed
     * revision. Individuals that KM reports as equal share one component.
     */
    private static final class Realized {
        final Map<OWLNamedIndividual, Integer> componentOf = new HashMap<>();
        final List<Set<OWLNamedIndividual>> members = new ArrayList<>();
        /** Per component: representative ids of all entailed types, owl:Thing included. */
        final List<int[]> allTypes = new ArrayList<>();
        /** Per component: representative ids of the most specific types. */
        final List<int[]> directTypes = new ArrayList<>();
    }

    private Realized ensureRealized() {
        ensureClassified();
        if (realized != null) return realized;
        if (realizeFailure != null) throw realizeFailure;
        Realized[] out = new Realized[1];
        try {
            runTask(ReasonerProgressMonitor.REALIZING, () -> out[0] = realizeNow());
        } catch (RuntimeException failure) {
            if (cacheable(failure)) realizeFailure = failure;
            throw failure;
        }
        return out[0];
    }

    private Realized realizeNow() {
        Realized built = new Realized();
        if (!consistent) {
            // Like the class queries, answer an inconsistent ontology with empty sets.
            realized = built;
            return built;
        }
        try {
            OWLOntology snapshot = getCommittedOntologySnapshot();
            Set<OWLNamedIndividual> individuals = new LinkedHashSet<>(snapshot.getIndividualsInSignature());
            Classifier.Realization result;
            if (individuals.isEmpty()) {
                // A TBox needs no native run.
                result = new Classifier.Realization();
            } else {
                result = Classifier.realize(FlattenedOntology.functionalSyntaxOfSnapshot(snapshot),
                        process -> {
                            realizeProcess = process;
                            if (process != null && (interruptRequested || timedOut)) {
                                NativeProcessTree.terminateAndWait(process);
                            }
                        });
            }
            if (!result.consistent) {
                realized = built;
                return built;
            }
            fillRealized(built, individuals, result);
        } catch (RuntimeException error) {
            throw error;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
        realized = built;
        return built;
    }

    private void fillRealized(Realized out, Set<OWLNamedIndividual> individuals, Classifier.Realization result) {
        // Union-find over the individual universe and the SAME pairs.
        List<OWLNamedIndividual> all = new ArrayList<>(individuals);
        Map<OWLNamedIndividual, Integer> index = new HashMap<>();
        for (OWLNamedIndividual i : all) index.put(i, index.size());
        java.util.function.Function<String, Integer> indexOf = iri -> {
            OWLNamedIndividual i = df.getOWLNamedIndividual(IRI.create(normalizeIri(iri)));
            Integer at = index.get(i);
            if (at == null) {
                at = all.size();
                all.add(i);
                index.put(i, at);
            }
            return at;
        };
        for (String iri : result.types.keySet()) indexOf.apply(iri);
        for (String[] pair : result.same) { indexOf.apply(pair[0]); indexOf.apply(pair[1]); }
        int[] parent = new int[all.size()];
        for (int i = 0; i < parent.length; i++) parent[i] = i;
        for (String[] pair : result.same) {
            int a = find(parent, indexOf.apply(pair[0])), b = find(parent, indexOf.apply(pair[1]));
            if (a != b) parent[a] = b;
        }
        Map<Integer, Integer> componentOfRoot = new HashMap<>();
        for (int i = 0; i < parent.length; i++) {
            int root = find(parent, i);
            Integer c = componentOfRoot.get(root);
            if (c == null) {
                c = out.members.size();
                componentOfRoot.put(root, c);
                out.members.add(new LinkedHashSet<>());
            }
            out.members.get(c).add(all.get(i));
            out.componentOf.put(all.get(i), c);
        }
        List<Set<Integer>> typeSets = new ArrayList<>();
        for (int c = 0; c < out.members.size(); c++) {
            Set<Integer> reps = new TreeSet<>();
            reps.add(repId[thingId]);
            typeSets.add(reps);
        }
        for (Map.Entry<String, List<String>> e : result.types.entrySet()) {
            Set<Integer> reps = typeSets.get(out.componentOf.get(
                    df.getOWLNamedIndividual(IRI.create(normalizeIri(e.getKey())))));
            for (String classIri : e.getValue()) {
                Integer id = idByIri.get(normalizeIri(classIri));
                if (id == null) continue;
                int r = repId[id];
                reps.add(r);
                // The rows list every entailed type; closing under the taxonomy
                // keeps the answer a union of whole nodes.
                int[] sups = supersByRep[r];
                if (sups != null) for (int s : sups) reps.add(s);
            }
        }
        for (Set<Integer> reps : typeSets) {
            int[] closed = new int[reps.size()];
            int k = 0;
            for (int r : reps) closed[k++] = r;
            out.allTypes.add(closed);
            out.directTypes.add(minimalIds(closed));
        }
    }

    private static int find(int[] parent, int x) {
        while (parent[x] != x) {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        return x;
    }

    @Override public synchronized NodeSet<OWLClass> getTypes(OWLNamedIndividual ind, boolean direct) {
        checkPreConditions();
        OWLClassNodeSet ns = new OWLClassNodeSet();
        Realized data = ensureRealized();
        if (!consistent) return ns;
        Integer c = data.componentOf.get(ind);
        if (c == null) {
            // An individual outside the signature has no named type but owl:Thing.
            ns.addNode(nodeOfId(repId[thingId]));
            return ns;
        }
        for (int r : (direct ? data.directTypes : data.allTypes).get(c)) ns.addNode(nodeOfId(r));
        return ns;
    }

    @Override public synchronized NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression ce, boolean direct) {
        OWLNamedIndividualNodeSet ns = new OWLNamedIndividualNodeSet();
        ensureClassified();
        // HermiT checks the preconditions only when the ontology has individuals.
        if (!consistent && !getRootOntology().getIndividualsInSignature(Imports.INCLUDED).isEmpty()) {
            throw new InconsistentOntologyException();
        }
        if (ce.isAnonymous()) {
            // TODO W5: class expression queries (DL Query) via a fresh definition Q = CE.
            throw unsupported("getInstances", "the class expression " + ce);
        }
        Realized data = ensureRealized();
        if (!consistent) return ns;
        int r = repIdOf(ce);
        if (r < 0 || r == repId[nothingId]) return ns;
        // The policy decides the nodes: BY_NAME gives one node per individual,
        // BY_SAME_AS one node per group of individuals entailed to be the same.
        boolean grouped = getIndividualNodeSetPolicy() == IndividualNodeSetPolicy.BY_SAME_AS;
        for (int c = 0; c < data.members.size(); c++) {
            for (int t : (direct ? data.directTypes : data.allTypes).get(c)) {
                if (t == r) {
                    if (grouped) {
                        ns.addNode(new OWLNamedIndividualNode(data.members.get(c)));
                    } else {
                        for (OWLNamedIndividual member : data.members.get(c)) {
                            ns.addNode(new OWLNamedIndividualNode(member));
                        }
                    }
                    break;
                }
            }
        }
        return ns;
    }

    @Override public synchronized Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual ind) {
        checkPreConditions();
        Realized data = ensureRealized();
        Integer c = consistent ? data.componentOf.get(ind) : null;
        return c == null ? new OWLNamedIndividualNode(ind)
                : new OWLNamedIndividualNode(data.members.get(c));
    }

    private boolean isEntailedClassAssertion(OWLClassAssertionAxiom axiom) {
        if (axiom.getClassExpression().isAnonymous() || axiom.getIndividual().isAnonymous()) {
            throw new UnsupportedEntailmentTypeException(axiom);
        }
        if (!consistent || axiom.getClassExpression().isOWLThing()) return true;
        OWLNamedIndividual ind = axiom.getIndividual().asOWLNamedIndividual();
        int r = repIdOf(axiom.getClassExpression());
        if (r < 0) return false;
        Realized data = ensureRealized();
        Integer c = data.componentOf.get(ind);
        if (c == null) return r == repId[thingId];
        for (int t : data.allTypes.get(c)) if (t == r) return true;
        return false;
    }

    private boolean isEntailedSameIndividual(OWLSameIndividualAxiom axiom) {
        Set<OWLNamedIndividual> named = new HashSet<>();
        for (OWLIndividual i : axiom.getIndividuals()) {
            if (i.isAnonymous()) throw new UnsupportedEntailmentTypeException(axiom);
            named.add(i.asOWLNamedIndividual());
        }
        if (!consistent || named.size() <= 1) return true;
        Realized data = ensureRealized();
        Integer first = null;
        for (OWLNamedIndividual i : named) {
            Integer c = data.componentOf.get(i);
            if (c == null || (first != null && !first.equals(c))) return false;
            first = c;
        }
        return true;
    }

    // ---- object properties (from km classify --properties) ----------------

    private static final String CLASSIFYING_OBJECT_PROPERTIES = "Classifying object properties";

    private ObjectPropertyModel ensureProperties() {
        ensureClassified();
        ObjectPropertyModel model = propertyModel;
        if (model != null) return model;
        if (propertiesFailure != null) throw propertiesFailure;
        ObjectPropertyModel[] out = new ObjectPropertyModel[1];
        try {
            runTask(CLASSIFYING_OBJECT_PROPERTIES, () -> out[0] = propertiesNow());
        } catch (RuntimeException failure) {
            if (cacheable(failure)) propertiesFailure = failure;
            throw failure;
        }
        return out[0];
    }

    /**
     * HermiT only puts inverse roles into its role hierarchy when the
     * normalised ontology uses them (DLOntology.hasInverseRoles, set by
     * OWLAxiomsExpressivity). Those are the ontologies that mention
     * ObjectInverseOf, or that have an InverseObjectProperties, an
     * InverseFunctionalObjectProperty, a SymmetricObjectProperty or an
     * AsymmetricObjectProperty axiom, which HermiT's normalisation rewrites
     * with an inverse. The test reads the functional syntax of the revision.
     */
    private static final java.util.regex.Pattern USES_INVERSE = java.util.regex.Pattern.compile(
            "ObjectInverseOf\\(|InverseObjectProperties\\(|(?<![A-Za-z])(Symmetric|Asymmetric|InverseFunctional)ObjectProperty\\(");

    private int propertyRuns;

    /** Whether HermiT's rule counts the ontology as using inverse roles (for tests). */
    synchronized boolean usesInverseRoles() { return ensureProperties().hasInverseRoles(); }

    /** Native {@code --properties} runs made so far (for tests). */
    synchronized int propertyRunCount() { return propertyRuns; }

    private ObjectPropertyModel propertiesNow() {
        ObjectPropertyModel built;
        if (!consistent) {
            built = new ObjectPropertyModel(df, Collections.<OWLObjectProperty>emptySet(), null, false);
            propertyModel = built;
            return built;
        }
        try {
            OWLOntology snapshot = getCommittedOntologySnapshot();
            Set<OWLObjectProperty> signature = new LinkedHashSet<>(snapshot.getObjectPropertiesInSignature());
            signature.remove(df.getOWLTopObjectProperty());
            signature.remove(df.getOWLBottomObjectProperty());
            if (signature.isEmpty()) {
                // No object property: nothing to ask the engine.
                built = new ObjectPropertyModel(df, signature, null, false);
            } else {
                String source = FlattenedOntology.functionalSyntaxOfSnapshot(snapshot);
                propertyRuns++;
                Classifier.Properties rows = Classifier.properties(source,
                        process -> {
                            realizeProcess = process;
                            if (process != null && (interruptRequested || timedOut)) {
                                NativeProcessTree.terminateAndWait(process);
                            }
                        });
                built = rows.consistent
                        ? new ObjectPropertyModel(df, signature, rows, USES_INVERSE.matcher(source).find())
                        : new ObjectPropertyModel(df, Collections.<OWLObjectProperty>emptySet(), null, false);
            }
        } catch (RuntimeException error) {
            throw error;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
        propertyModel = built;
        return built;
    }

    /**
     * The distinct representatives of the classes that are domains of the
     * expression: every class entailed to contain all sources of the property
     * (rows plus owl:Thing, closed upwards), or every class for an empty
     * property. HermiT searches the class hierarchy for the classes C with
     * {@code r(a,b) and not C(a)} unsatisfiable (Reasoner.getObjectPropertyDomains).
     */
    private int[] domainReps(ObjectPropertyModel model, int code) {
        Set<Integer> reps = new TreeSet<>();
        if (model.isEmpty(code)) {
            for (int c = 0; c < repId.length; c++) reps.add(repId[c]);
        } else {
            reps.add(repId[thingId]);
            for (String iri : model.domainIris(code)) {
                Integer id = idByIri.get(normalizeIri(iri));
                if (id == null) continue;
                int r = repId[id];
                reps.add(r);
                int[] sups = supersByRep[r];
                if (sups != null) for (int s : sups) reps.add(s);
            }
        }
        int[] out = new int[reps.size()];
        int k = 0;
        for (int r : reps) out[k++] = r;
        return out;
    }

    private NodeSet<OWLClass> classNodeSet(int[] reps, boolean direct, boolean empty) {
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (direct && empty) {
            ns.addNode(nodeOfId(repId[nothingId]));
        } else {
            for (int r : direct ? minimalIds(reps) : reps) ns.addNode(nodeOfId(r));
        }
        return ns;
    }

    @Override public synchronized NodeSet<OWLClass> getObjectPropertyDomains(OWLObjectPropertyExpression pe, boolean direct) {
        checkPreConditions();
        ObjectPropertyModel model = ensureProperties();
        int code = model.code(pe);
        return classNodeSet(domainReps(model, code), direct, model.isEmpty(code));
    }
    @Override public synchronized NodeSet<OWLClass> getObjectPropertyRanges(OWLObjectPropertyExpression pe, boolean direct) {
        checkPreConditions();
        ObjectPropertyModel model = ensureProperties();
        // The range of r is the domain of its inverse.
        int code = ObjectPropertyModel.inverse(model.code(pe));
        return classNodeSet(domainReps(model, code), direct, model.isEmpty(code));
    }

    // ---- queries the taxonomy and the property models cannot answer in general ---
    //
    // A query either follows from data the plugin holds (the class taxonomy, the
    // object property hierarchy, the data property model, the realization) or
    // it throws UnsupportedOperationException. The cases that do follow:
    //  - a class that is disjoint with nothing but the unsatisfiable classes
    //    (owl:Thing, a class outside the signature) or with everything (an
    //    unsatisfiable class);
    //  - the same for properties: the top and the universal properties, the fresh
    //    ones and the empty ones.
    // Disjointness of two satisfiable named entities depends on domains, ranges,
    // disjointness axioms and the whole TBox, so it needs the engine.

    @Override public synchronized NodeSet<OWLClass> getDisjointClasses(OWLClassExpression ce) {
        checkPreConditions();
        requireNamed(ce, "getDisjointClasses");
        OWLClassNodeSet ns = new OWLClassNodeSet();
        Node<OWLClass> bottom = nodeOfId(repId[nothingId]);
        if (isFresh(ce) || (!ce.isOWLNothing() && repIdOf(ce) == repId[thingId])) {
            // D is disjoint with a class that has no constraints only when D is empty.
            ns.addNode(bottom);
            return ns;
        }
        if (repIdOf(ce) == repId[nothingId]) {
            // An empty class is disjoint with every class, itself included.
            for (int s : nonBottomReps()) ns.addNode(nodeOfId(s));
            ns.addNode(bottom);
            return ns;
        }
        throw unsupported("getDisjointClasses", "the satisfiable class " + ce);
    }

    @Override public synchronized NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty pe, boolean direct) {
        checkPreConditions();
        DataPropertyModel model = ensureDataProperties();
        if (model.isEmpty(pe)) {
            // No pair: every class is a domain, and the direct domain is the bottom node.
            int[] all = new int[repId.length];
            int count = 0;
            for (int c = 0; c < repId.length; c++) if (repId[c] == c) all[count++] = c;
            return classNodeSet(Arrays.copyOf(all, count), direct, true);
        }
        Set<Integer> reps = new TreeSet<>();
        reps.add(repId[thingId]);
        int lowest = model.domainRep(pe);
        if (lowest >= 0) {
            reps.add(lowest);
            int[] sups = supersByRep[lowest];
            if (sups != null) for (int sup : sups) reps.add(sup);
        }
        int[] out = new int[reps.size()];
        int k = 0;
        for (int r : reps) out[k++] = r;
        return classNodeSet(out, direct, false);
    }

    @Override public synchronized Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() {
        checkPreConditions();
        return ensureProperties().topNode();
    }
    @Override public synchronized Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() {
        checkPreConditions();
        return ensureProperties().bottomNode();
    }
    @Override public synchronized Node<OWLDataProperty> getTopDataPropertyNode() {
        checkPreConditions();
        return ensureDataProperties().topNode();
    }
    @Override public synchronized Node<OWLDataProperty> getBottomDataPropertyNode() {
        checkPreConditions();
        return ensureDataProperties().bottomNode();
    }

    @Override public synchronized NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(OWLObjectPropertyExpression pe, boolean direct) {
        checkPreConditions();
        return ensureProperties().subs(pe, direct);
    }
    @Override public synchronized NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(OWLObjectPropertyExpression pe, boolean direct) {
        checkPreConditions();
        return ensureProperties().supers(pe, direct);
    }
    @Override public synchronized Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(OWLObjectPropertyExpression pe) {
        checkPreConditions();
        return ensureProperties().equivalents(pe);
    }
    @Override public synchronized NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(OWLObjectPropertyExpression pe) {
        checkPreConditions();
        ObjectPropertyModel model = ensureProperties();
        int code = model.code(pe);
        if (model.isEmpty(code)) return model.allNodes();
        if (code == ObjectPropertyModel.FRESH || model.isUniversal(code)) {
            OWLObjectPropertyNodeSet ns = new OWLObjectPropertyNodeSet();
            ns.addNode(model.bottomNode());
            return ns;
        }
        throw unsupported("getDisjointObjectProperties", "the satisfiable object property " + pe);
    }
    /** HermiT answers {@code getEquivalentObjectProperties(pe^-)} (Reasoner.getInverseObjectProperties). */
    @Override public synchronized Node<OWLObjectPropertyExpression> getInverseObjectProperties(OWLObjectPropertyExpression pe) {
        checkPreConditions();
        return ensureProperties().equivalents(pe.getInverseProperty());
    }

    /**
     * Entailment of the property axioms HermiT's EntailmentChecker reduces to
     * the role hierarchy: sub-property (no chains), equivalence, inverse,
     * symmetry, and domain and range with a named class. A domain or range
     * with a class expression needs a class expression query.
     * TODO W5: domain and range with an anonymous class.
     */
    private boolean isEntailedObjectPropertyAxiom(OWLAxiom axiom) {
        ObjectPropertyModel model = ensureProperties();
        if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
            OWLSubObjectPropertyOfAxiom a = (OWLSubObjectPropertyOfAxiom) axiom;
            return model.entails(a.getSubProperty(), a.getSuperProperty());
        }
        if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
            // HermiT compares every property with the first one, in both directions.
            Iterator<OWLObjectPropertyExpression> it =
                    ((OWLEquivalentObjectPropertiesAxiom) axiom).getProperties().iterator();
            if (!it.hasNext()) return true;
            OWLObjectPropertyExpression first = it.next();
            while (it.hasNext()) {
                OWLObjectPropertyExpression other = it.next();
                if (!model.entails(first, other) || !model.entails(other, first)) return false;
            }
            return true;
        }
        if (axiom instanceof OWLInverseObjectPropertiesAxiom) {
            OWLInverseObjectPropertiesAxiom a = (OWLInverseObjectPropertiesAxiom) axiom;
            OWLObjectPropertyExpression first = a.getFirstProperty().getInverseProperty();
            OWLObjectPropertyExpression second = a.getSecondProperty();
            return model.entails(first, second) && model.entails(second, first);
        }
        if (axiom instanceof OWLSymmetricObjectPropertyAxiom) {
            OWLObjectPropertyExpression p = ((OWLSymmetricObjectPropertyAxiom) axiom).getProperty();
            return model.entails(p, p.getInverseProperty());
        }
        OWLObjectPropertyExpression property;
        OWLClassExpression cls;
        int code;
        if (axiom instanceof OWLObjectPropertyDomainAxiom) {
            property = ((OWLObjectPropertyDomainAxiom) axiom).getProperty();
            cls = ((OWLObjectPropertyDomainAxiom) axiom).getDomain();
            code = model.code(property);
        } else {
            property = ((OWLObjectPropertyRangeAxiom) axiom).getProperty();
            cls = ((OWLObjectPropertyRangeAxiom) axiom).getRange();
            code = ObjectPropertyModel.inverse(model.code(property));
        }
        if (cls.isAnonymous()) throw new UnsupportedEntailmentTypeException(axiom);
        if (cls.isOWLThing() || model.isEmpty(code)) return true;
        int r = repIdOf(cls);
        if (r < 0) return false; // a class outside the signature contains nothing it is not told to
        for (int rep : domainReps(model, code)) if (rep == r) return true;
        return false;
    }

    @Override public synchronized NodeSet<OWLNamedIndividual> getObjectPropertyValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) {
        checkPreConditions();
        throw unsupported("getObjectPropertyValues", "the individual " + ind + " and the property " + pe);
    }

    @Override public synchronized NodeSet<OWLDataProperty> getSubDataProperties(OWLDataProperty pe, boolean direct) {
        checkPreConditions();
        return ensureDataProperties().subs(pe, direct);
    }
    @Override public synchronized NodeSet<OWLDataProperty> getSuperDataProperties(OWLDataProperty pe, boolean direct) {
        checkPreConditions();
        return ensureDataProperties().supers(pe, direct);
    }
    @Override public synchronized Node<OWLDataProperty> getEquivalentDataProperties(OWLDataProperty pe) {
        checkPreConditions();
        return ensureDataProperties().equivalents(pe);
    }
    @Override public synchronized NodeSet<OWLDataProperty> getDisjointDataProperties(OWLDataPropertyExpression pe) {
        checkPreConditions();
        DataPropertyModel model = ensureDataProperties();
        OWLDataProperty named = pe.asOWLDataProperty();
        if (model.isEmpty(named)) return model.allNodes();
        if (model.isFresh(named) || model.isUniversal(named)) return model.bottomOnly();
        throw unsupported("getDisjointDataProperties", "the satisfiable data property " + pe);
    }
    @Override public synchronized Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual ind, OWLDataProperty pe) {
        checkPreConditions();
        throw unsupported("getDataPropertyValues", "the individual " + ind + " and the property " + pe);
    }

    @Override public synchronized NodeSet<OWLNamedIndividual> getDifferentIndividuals(OWLNamedIndividual ind) {
        checkPreConditions();
        throw unsupported("getDifferentIndividuals", "the individual " + ind);
    }

    // ---- data properties (from the stated axioms and the taxonomy) -----------

    private final DataPropertyModel.Taxonomy taxonomy = new DataPropertyModel.Taxonomy() {
        @Override public int rep(OWLClass c) { return repIdOf(c); }
        @Override public boolean isUnsatisfiable(int rep) { return rep == repId[nothingId]; }
        @Override public boolean below(int sub, int sup) {
            if (sub == sup) return true;
            int[] sups = supersByRep[sub];
            return sups != null && Arrays.binarySearch(sups, sup) >= 0;
        }
    };

    /** The data property model of the committed revision, or UnsupportedOperationException outside its fragment. */
    private DataPropertyModel ensureDataProperties() {
        ensureClassified();
        DataPropertyModel model = dataModel;
        if (model != null) return model;
        if (dataFailure != null) throw dataFailure;
        try {
            model = DataPropertyModel.build(df, getCommittedOntologySnapshot(), taxonomy);
        } catch (RuntimeException failure) {
            if (cacheable(failure)) dataFailure = failure;
            throw failure;
        }
        dataModel = model;
        return model;
    }
}
