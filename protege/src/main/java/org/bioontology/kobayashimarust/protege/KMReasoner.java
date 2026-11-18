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
 * <p>Class expression queries, disjoint classes and object properties,
 * property values, different individuals and most entailment checks are
 * answered by reduction: one km run on the ontology extended with fresh
 * definitions or with assertions about fresh individuals (see the section
 * "fresh-definition reductions" and protege/README.md).
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

    private static final List<String> ALL_REDUCTION_IDS = Collections.unmodifiableList(Arrays.asList(
            "R01_forest_abox_rollup",
            "R02_rollup_class_expression",
            "R03_rollup_different_individuals",
            "R04_rollup_data_property_values",
            "R05_positive_rbox_properties",
            "R06_positive_rbox_values",
            "R07_swrl_rule_pregrounding",
            "R08_object_properties_existential_probes",
            "R09_syntactic_data_property_model",
            "R10_data_properties_literal_probes",
            "R11_disjoint_data_properties",
            "R12_data_property_values_batch",
            "R13_object_property_values_probes",
            "R14_different_individuals_nominal_probes",
            "R15_disjoint_object_properties_probes",
            "R16_class_expression_extension",
            "R17_horn_complement_probes",
            "R18_min_cardinality_witness_probes",
            "R19_disjoint_classes_probes",
            "R20_tbox_conservativity_projection",
            "R21_entailment_subsumption_disjointness",
            "R22_entailment_property_domain_range",
            "R23_entailment_rbox_characteristics",
            "R24_entailment_abox_assertions",
            "R25_entailment_haskey_swrl"));

    private static final java.util.concurrent.ConcurrentHashMap<String, java.util.concurrent.atomic.LongAdder>
            REDUCTION_HITS = new java.util.concurrent.ConcurrentHashMap<>();

    static void recordReduction(String id) {
        REDUCTION_HITS.computeIfAbsent(id, k -> new java.util.concurrent.atomic.LongAdder()).increment();
    }

    public static List<String> allReductionIds() {
        return ALL_REDUCTION_IDS;
    }

    public static Map<String, Long> getReductionHits() {
        Map<String, Long> out = new LinkedHashMap<>();
        for (String id : ALL_REDUCTION_IDS) {
            java.util.concurrent.atomic.LongAdder a = REDUCTION_HITS.get(id);
            out.put(id, a == null ? 0L : a.sum());
        }
        return out;
    }

    public static void resetReductionHits() {
        REDUCTION_HITS.clear();
    }

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
    /** Precomputed object property values of the committed revision; null until precomputed. */
    private volatile Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> allObjectValues;
    /** Inference types requested via precomputeInferences on the current revision. */
    private final Set<InferenceType> precomputedTypes = EnumSet.noneOf(InferenceType.class);
    /** Rolled-up forest ABox of the committed revision; null when not applicable. */
    private volatile ForestABoxRollup activeRollup;
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
    private volatile RuntimeException valuesFailure;
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

    private static boolean cacheableWholeRevision(RuntimeException failure, long elapsedMillis) {
        if (cacheable(failure)) return true;
        if (failure instanceof TimeOutException && elapsedMillis >= 2_000L) return true;
        return failure instanceof ReasonerInterruptedException && elapsedMillis >= 5_000L;
    }

    private void forgetFailures() {
        classificationFailure = null;
        realizeFailure = null;
        propertiesFailure = null;
        dataFailure = null;
        valuesFailure = null;
        reductions.values().removeIf(held -> held instanceof RuntimeException);
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
        ForestABoxRollup rollup = ForestABoxRollup.tryBuild(ont, df, candidateSource);
        String pregrounded = null;
        if (rollup == null && added == null && removed == null
                && ont.getImportsClosure().size() == 1
                && !ont.getAxioms(AxiomType.SWRL_RULE).isEmpty()) {
            pregrounded = ForestABoxRollup.tryPregroundRules(ont, df);
        }
        String sessionSource = rollup != null ? rollup.rolledSource
                : (pregrounded != null ? pregrounded : candidateSource);

        // Whether the native answer differs from the one the Java hierarchy was built from.
        boolean answerChanged;
        Classifier.Session session;
        try {
            if (incrementalSession == null) {
                // Register the session as soon as its process runs, so interrupt()
                // reaches the first (longest) transaction too.
                incrementalSession = new Classifier.Session(sessionSource, s -> {
                    incrementalSession = s;
                    // An interrupt or time out that came before the process existed.
                    if (interruptRequested || timedOut) s.interrupt();
                });
                answerChanged = true;
            } else {
                answerChanged = incrementalSession.replaceRows(sessionSource);
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
        activeRollup = rollup;
        precomputedTypes.clear();
        // Class ids are rebuilt below and the ABox may have changed, so the
        // realization of the previous revision no longer applies.
        realized = null;
        propertyModel = null;
        dataModel = null;
        allObjectValues = null;
        realizeFailure = null;
        propertiesFailure = null;
        dataFailure = null;
        valuesFailure = null;
        clearReductions();
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
            rebuildHierarchy(session, classes, incremental, sessionSource);
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

    private void rebuildHierarchy(Classifier.Session session, Set<OWLClass> classes,
                                  boolean incremental, String sessionSource) {
        subsByRep = null;
        consistent = session.consistent();
        dropped = session.dropped();
        if (consistent && activeRollup != null) {
            Collection<String> unsatIris = session.unsatisfiable();
            for (String req : activeRollup.requiredSatisfiableIris) {
                if (unsatIris.contains(req)) {
                    consistent = false;
                    break;
                }
            }
        }

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
        if (consistent) {
            unionTopEquivalents(n, sessionSource);
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

    private void unionClassAndSupersWithThing(OWLClass cls) {
        Integer idBox = idByClass.get(cls);
        if (idBox == null) return;
        int id = idBox;
        if (findId(id) == findId(nothingId)) return;
        unionId(id, thingId);
        for (int sup : rawSup[id]) {
            if (findId(sup) != findId(nothingId)) unionId(sup, thingId);
        }
    }

    private void unionTopEquivalents(int n, String sessionSource) {
        Set<OWLOntology> closure = getRootOntology().getImportsClosure();
        Set<OWLObjectProperty> reflexiveProps = new HashSet<>();
        boolean canEntailTop = false;
        for (OWLOntology o : closure) {
            for (OWLAxiom ax : o.getLogicalAxioms()) {
                if (ax instanceof OWLSubClassOfAxiom) {
                    OWLSubClassOfAxiom sub = (OWLSubClassOfAxiom) ax;
                    if (sub.getSubClass().isOWLThing()) {
                        canEntailTop = true;
                        if (!sub.getSuperClass().isAnonymous()) {
                            unionClassAndSupersWithThing(sub.getSuperClass().asOWLClass());
                        }
                    } else if (sub.getSubClass() instanceof OWLObjectComplementOf
                            || sub.getSuperClass() instanceof OWLObjectUnionOf
                            || sub.getSuperClass() instanceof OWLObjectOneOf
                            || sub.getSuperClass() instanceof OWLObjectHasSelf) {
                        canEntailTop = true;
                    }
                } else if (ax instanceof OWLEquivalentClassesAxiom) {
                    OWLEquivalentClassesAxiom eq = (OWLEquivalentClassesAxiom) ax;
                    boolean hasThing = false;
                    for (OWLClassExpression ce : eq.getClassExpressions()) {
                        if (ce.isOWLThing()) hasThing = true;
                        if (ce instanceof OWLObjectUnionOf
                                || ce instanceof OWLObjectComplementOf
                                || ce instanceof OWLObjectOneOf
                                || ce instanceof OWLObjectHasSelf) {
                            canEntailTop = true;
                        }
                    }
                    if (hasThing) {
                        canEntailTop = true;
                        for (OWLClassExpression ce : eq.getClassExpressions()) {
                            if (!ce.isAnonymous()) unionClassAndSupersWithThing(ce.asOWLClass());
                        }
                    }
                } else if (ax instanceof OWLDisjointUnionAxiom) {
                    if (((OWLDisjointUnionAxiom) ax).getOWLClass().isOWLThing()) canEntailTop = true;
                } else if (ax instanceof OWLReflexiveObjectPropertyAxiom) {
                    canEntailTop = true;
                    reflexiveProps.add(((OWLReflexiveObjectPropertyAxiom) ax).getProperty().getNamedProperty());
                } else if (ax instanceof OWLObjectPropertyDomainAxiom) {
                    OWLObjectPropertyDomainAxiom dom = (OWLObjectPropertyDomainAxiom) ax;
                    if (dom.getProperty().isOWLTopObjectProperty()) {
                        canEntailTop = true;
                        if (!dom.getDomain().isAnonymous()) {
                            unionClassAndSupersWithThing(dom.getDomain().asOWLClass());
                        }
                    }
                } else if (ax instanceof OWLObjectPropertyRangeAxiom) {
                    OWLObjectPropertyRangeAxiom rng = (OWLObjectPropertyRangeAxiom) ax;
                    if (rng.getProperty().isOWLTopObjectProperty()) {
                        canEntailTop = true;
                        if (!rng.getRange().isAnonymous()) {
                            unionClassAndSupersWithThing(rng.getRange().asOWLClass());
                        }
                    }
                } else if (ax instanceof OWLDataPropertyDomainAxiom) {
                    OWLDataPropertyDomainAxiom dom = (OWLDataPropertyDomainAxiom) ax;
                    if (dom.getProperty().isOWLTopDataProperty()) {
                        canEntailTop = true;
                        if (!dom.getDomain().isAnonymous()) {
                            unionClassAndSupersWithThing(dom.getDomain().asOWLClass());
                        }
                    }
                }
            }
        }
        if (!reflexiveProps.isEmpty()) {
            boolean changed = true;
            while (changed) {
                changed = false;
                for (OWLOntology o : closure) {
                    for (OWLAxiom ax : o.getLogicalAxioms()) {
                        if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                            OWLSubObjectPropertyOfAxiom s = (OWLSubObjectPropertyOfAxiom) ax;
                            if (reflexiveProps.contains(s.getSubProperty().getNamedProperty())
                                    && reflexiveProps.add(s.getSuperProperty().getNamedProperty())) {
                                changed = true;
                            }
                        } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom
                                || ax instanceof OWLInverseObjectPropertiesAxiom) {
                            Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                            boolean any = false;
                            for (OWLObjectProperty p : sig) {
                                if (reflexiveProps.contains(p)) { any = true; break; }
                            }
                            if (any && reflexiveProps.addAll(sig)) changed = true;
                        }
                    }
                }
            }
            for (OWLOntology o : closure) {
                for (OWLAxiom ax : o.getLogicalAxioms()) {
                    if (ax instanceof OWLObjectPropertyDomainAxiom) {
                        OWLObjectPropertyDomainAxiom dom = (OWLObjectPropertyDomainAxiom) ax;
                        if (reflexiveProps.contains(dom.getProperty().getNamedProperty())
                                && !dom.getDomain().isAnonymous()) {
                            unionClassAndSupersWithThing(dom.getDomain().asOWLClass());
                        }
                    } else if (ax instanceof OWLObjectPropertyRangeAxiom) {
                        OWLObjectPropertyRangeAxiom rng = (OWLObjectPropertyRangeAxiom) ax;
                        if (reflexiveProps.contains(rng.getProperty().getNamedProperty())
                                && !rng.getRange().isAnonymous()) {
                            unionClassAndSupersWithThing(rng.getRange().asOWLClass());
                        }
                    }
                }
            }
        }
        if (!canEntailTop) return;
        boolean hasUniversalCandidate = false;
        for (int c = 0; c < n; c++) {
            if (findId(c) == findId(thingId) || findId(c) == findId(nothingId)) continue;
            if (classById[c].getIRI().toString().startsWith("urn:km:indproxy:")) continue;
            boolean aboveAll = true;
            for (int x = 0; x < n; x++) {
                if (x == c || findId(x) == findId(thingId) || findId(x) == findId(nothingId)) continue;
                if (classById[x].getIRI().toString().startsWith("urn:km:indproxy:")) continue;
                if (Arrays.binarySearch(rawSup[x], c) < 0) {
                    aboveAll = false;
                    break;
                }
            }
            if (aboveAll) {
                hasUniversalCandidate = true;
                break;
            }
        }
        if (!hasUniversalCandidate) return;
        try {
            Collection<String> topIris = Classifier.topClasses(sessionSource, process -> {
                realizeProcess = process;
                if (process != null && (interruptRequested || timedOut)) {
                    NativeProcessTree.terminateAndWait(process);
                }
            });
            for (String iri : topIris) {
                Integer id = idByIri.get(normalizeIri(iri));
                if (id != null && findId(id) != findId(nothingId)) {
                    unionId(id, thingId);
                    for (int sup : rawSup[id]) {
                        if (findId(sup) != findId(nothingId)) unionId(sup, thingId);
                    }
                }
            }
        } catch (Exception ignored) {
            // Keep syntactic top equivalences if the auxiliary --top probe fails.
        }
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

    @Override public synchronized Node<OWLClass> getEquivalentClasses(OWLClassExpression ce) {
        checkPreConditions();
        if (ce.isAnonymous()) return equivalentsOfExpression(ce);
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
        if (ce.isAnonymous()) return supersOfExpression(ce, direct);
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
        if (ce.isAnonymous()) return subsOfExpression(ce, direct);
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
        // An anonymous expression: CE is unsatisfiable iff the fresh Q ≡ CE is.
        if (ce.isAnonymous()) return !classAnswer(ce, false).unsat;
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
        // checkPreConditions has classified. Individual inferences, property
        // hierarchies and object property assertions run lazily on first query
        // of each kind so precomputation never blocks class-hierarchy queries.
        Set<InferenceType> supported = getPrecomputableInferenceTypes();
        for (InferenceType type : types) {
            if (supported.contains(type)) {
                precomputedTypes.add(type);
                if (type == InferenceType.CLASS_ASSERTIONS || type == InferenceType.SAME_INDIVIDUAL) {
                    precomputedTypes.add(InferenceType.CLASS_ASSERTIONS);
                    precomputedTypes.add(InferenceType.SAME_INDIVIDUAL);
                }
            }
        }
    }
    /**
     * True for a type whose answer is held now or scheduled for lazy
     * on-demand computation on a consistent revision.
     * Not synchronized: Protege may ask while a classification runs on another thread.
     */
    private boolean hasAnyIndividuals() {
        if (!getRootOntology().getIndividualsInSignature(Imports.INCLUDED).isEmpty()) {
            return true;
        }
        for (OWLOntology o : getRootOntology().getImportsClosure()) {
            for (OWLAxiom ax : o.getLogicalAxioms()) {
                if (ax instanceof OWLIndividualAxiom) return true;
            }
        }
        return false;
    }

    @Override public boolean isPrecomputed(InferenceType inferenceType) {
        if (!consistent) return false;
        if (inferenceType == InferenceType.CLASS_HIERARCHY) return classified;
        if (inferenceType == InferenceType.CLASS_ASSERTIONS
                || inferenceType == InferenceType.SAME_INDIVIDUAL) {
            Realized r = realized;
            if (r != null) return !r.componentOf.isEmpty() || hasAnyIndividuals();
            return precomputedTypes.contains(inferenceType) && realizeFailure == null
                    && hasAnyIndividuals();
        }
        if (inferenceType == InferenceType.OBJECT_PROPERTY_HIERARCHY) {
            return propertyModel != null
                || (precomputedTypes.contains(InferenceType.OBJECT_PROPERTY_HIERARCHY) && propertiesFailure == null);
        }
        if (inferenceType == InferenceType.DATA_PROPERTY_HIERARCHY) {
            return dataModel != null
                || (precomputedTypes.contains(InferenceType.DATA_PROPERTY_HIERARCHY) && dataFailure == null);
        }
        if (inferenceType == InferenceType.OBJECT_PROPERTY_ASSERTIONS) {
            if (!hasAnyIndividuals()) return false;
            return allObjectValues != null
                || (precomputedTypes.contains(InferenceType.OBJECT_PROPERTY_ASSERTIONS) && valuesFailure == null);
        }
        return false;
    }
    /**
     * The types this reasoner computes, matching HermiT's six precomputable
     * inference types.
     */
    @Override public Set<InferenceType> getPrecomputableInferenceTypes() {
        Set<InferenceType> types = new HashSet<>(Arrays.asList(
                InferenceType.CLASS_HIERARCHY,
                InferenceType.OBJECT_PROPERTY_HIERARCHY,
                InferenceType.DATA_PROPERTY_HIERARCHY,
                InferenceType.CLASS_ASSERTIONS,
                InferenceType.SAME_INDIVIDUAL));
        if (objectValuesPrecomputable()) {
            types.add(InferenceType.OBJECT_PROPERTY_ASSERTIONS);
        }
        return types;
    }

    private boolean objectValuesPrecomputable() {
        for (OWLOntology o : getRootOntology().getImportsClosure()) {
            if (!o.getAxioms(AxiomType.DISJOINT_OBJECT_PROPERTIES).isEmpty()) return false;
        }
        return true;
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
        if (!entailmentSupported(axiom.getAxiomType())) throw new UnsupportedEntailmentTypeException(axiom);
        OWLAxiom plain = axiom.getAxiomWithoutAnnotations();
        // An axiom of the committed revision is entailed, also when it mentions
        // anonymous individuals (which the reductions below refuse).
        if (querySnapshot().containsAxiom(plain, Imports.EXCLUDED,
                org.semanticweb.owlapi.model.parameters.AxiomAnnotations.IGNORE_AXIOM_ANNOTATIONS)) {
            return true;
        }
        // First the axioms that the held answers decide (taxonomy, realization,
        // property hierarchy), then the reductions to a km run on an extension.
        if (plain instanceof OWLClassAssertionAxiom
                && !((OWLClassAssertionAxiom) plain).getClassExpression().isAnonymous()) {
            return isEntailedClassAssertion((OWLClassAssertionAxiom) plain);
        }
        if (plain instanceof OWLSameIndividualAxiom) return isEntailedSameIndividual((OWLSameIndividualAxiom) plain);
        if (plain instanceof OWLSubObjectPropertyOfAxiom
                || plain instanceof OWLEquivalentObjectPropertiesAxiom
                || plain instanceof OWLInverseObjectPropertiesAxiom
                || plain instanceof OWLSymmetricObjectPropertyAxiom
                || (plain instanceof OWLObjectPropertyDomainAxiom
                        && !((OWLObjectPropertyDomainAxiom) plain).getDomain().isAnonymous())
                || (plain instanceof OWLObjectPropertyRangeAxiom
                        && !((OWLObjectPropertyRangeAxiom) plain).getRange().isAnonymous())) {
            return isEntailedObjectPropertyAxiom(plain);
        }
        if (plain instanceof OWLSubClassOfAxiom
                && !((OWLSubClassOfAxiom) plain).getSubClass().isAnonymous()
                && !((OWLSubClassOfAxiom) plain).getSuperClass().isAnonymous()) {
            OWLSubClassOfAxiom subClassOf = (OWLSubClassOfAxiom) plain;
            return namedSubsumption(subClassOf.getSubClass().asOWLClass(), subClassOf.getSuperClass().asOWLClass());
        }
        if (plain instanceof OWLEquivalentClassesAxiom) {
            List<OWLClassExpression> ops = new ArrayList<>(((OWLEquivalentClassesAxiom) plain).getClassExpressions());
            boolean allNamed = true;
            for (OWLClassExpression ce : ops) {
                if (ce.isAnonymous()) { allNamed = false; break; }
            }
            if (allNamed) {
                for (int i = 1; i < ops.size(); i++) {
                    OWLClass a = ops.get(0).asOWLClass(), b = ops.get(i).asOWLClass();
                    if (!namedSubsumption(a, b) || !namedSubsumption(b, a)) return false;
                }
                return true;
            }
        }
        if (plain instanceof OWLDisjointUnionAxiom) {
            OWLDisjointUnionAxiom du = (OWLDisjointUnionAxiom) plain;
            OWLClass target = du.getOWLClass();
            for (OWLClassExpression op : du.getClassExpressions()) {
                if (!op.isAnonymous() && !namedSubsumption(op.asOWLClass(), target)) {
                    return false;
                }
            }
        }
        if (plain instanceof OWLDataPropertyDomainAxiom
                && !((OWLDataPropertyDomainAxiom) plain).getDomain().isAnonymous()) {
            OWLDataPropertyDomainAxiom dpd = (OWLDataPropertyDomainAxiom) plain;
            if (isBottom(dpd.getProperty()) || dpd.getDomain().isOWLThing()) return true;
            if (!dpd.getProperty().isOWLTopDataProperty()) {
                OWLClass dom = dpd.getDomain().asOWLClass();
                return getDataPropertyDomains(dpd.getProperty().asOWLDataProperty(), false).containsEntity(dom)
                        || getTopClassNode().contains(dom);
            }
        }
        return this.<Boolean>reduce(Arrays.asList("entailed", plain), CHECKING_ENTAILMENT,
                () -> entailedByReduction(plain));
    }

    private boolean namedSubsumption(OWLClass sub, OWLClass sup) {
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
        return entailmentSupported(axiomType);
    }

    /**
     * Every OWL 2 axiom type is supported for entailment checking (matching
     * HermiT); an individual axiom whose fragment the engine cannot decide
     * throws {@link UnsupportedEntailmentTypeException} at check time.
     */
    private boolean entailmentSupported(AxiomType<?> axiomType) {
        return axiomType != null;
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
        long t0 = System.nanoTime();
        try {
            runTask(ReasonerProgressMonitor.REALIZING, () -> out[0] = realizeNow());
        } catch (RuntimeException failure) {
            if (cacheableWholeRevision(failure, (System.nanoTime() - t0) / 1_000_000L)) {
                realizeFailure = failure;
            }
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
            Classifier.Realization result = null;
            if (individuals.isEmpty()) {
                // A TBox needs no native run.
                result = new Classifier.Realization();
            } else if (activeRollup != null && incrementalSession != null) {
                result = activeRollup.buildRealization(incrementalSession.rows());
            } else {
                result = Classifier.realize(querySource(),
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
        if (!consistent && hasAnyIndividuals()) {
            throw new InconsistentOntologyException();
        }
        if (ce.isAnonymous()) return instancesOfExpression(ce, direct);
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
        long t0 = System.nanoTime();
        try {
            runTask(CLASSIFYING_OBJECT_PROPERTIES, () -> out[0] = propertiesNow());
        } catch (RuntimeException failure) {
            if (cacheableWholeRevision(failure, (System.nanoTime() - t0) / 1_000_000L)) {
                propertiesFailure = failure;
            }
            throw failure;
        }
        return out[0];
    }

    /**
     * HermiT only puts inverse roles into its role hierarchy when the
     * normalised ontology uses them (DLOntology.hasInverseRoles, set by
     * OWLAxiomsExpressivity). Those are the ontologies that mention
     * ObjectInverseOf, or that have an InverseObjectProperties, an
     * InverseFunctionalObjectProperty or a SymmetricObjectProperty axiom,
     * which HermiT's normalisation rewrites with an inverse. The test reads
     * the functional syntax of the revision.
     */
    private static final java.util.regex.Pattern USES_INVERSE = java.util.regex.Pattern.compile(
            "ObjectInverseOf\\(|InverseObjectProperties\\(|(?<![A-Za-z])(Symmetric|InverseFunctional)ObjectProperty\\(");

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
                String source = querySource();
                boolean hasInverses = USES_INVERSE.matcher(
                        FlattenedOntology.functionalSyntaxOfSnapshot(snapshot)).find();
                Classifier.Properties fastRows =
                        ForestABoxRollup.tryBuildPositiveRBoxProperties(snapshot, unsatisfiable.isEmpty());
                if (fastRows != null) {
                    built = new ObjectPropertyModel(df, signature, fastRows, hasInverses);
                } else if (!snapshot.getAxioms(AxiomType.SWRL_RULE).isEmpty()
                        && hasObjectOneOf(snapshot)
                        && snapshot.getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY).isEmpty()) {
                    built = propertiesByExistentialProbes(snapshot, signature, hasInverses);
                } else {
                    propertyRuns++;
                    try {
                        String propSource = canUseTBoxQuerySource(Collections.emptyList())
                                ? tboxQuerySource() : source;
                        Classifier.Properties rows = Classifier.properties(propSource,
                                process -> {
                                    realizeProcess = process;
                                    if (process != null && (interruptRequested || timedOut)) {
                                        NativeProcessTree.terminateAndWait(process);
                                    }
                                });
                        built = rows.consistent
                                ? new ObjectPropertyModel(df, signature, rows, hasInverses)
                                : new ObjectPropertyModel(df, Collections.<OWLObjectProperty>emptySet(), null, false);
                    } catch (UnsupportedOperationException declined) {
                        if (snapshot.getAxioms(AxiomType.SWRL_RULE).isEmpty()) throw declined;
                        built = propertiesByExistentialProbes(snapshot, signature, hasInverses);
                    }
                }
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
     * Exact object-property hierarchy, domains and ranges via nominal-free
     * existential probes ({@code P_e ≡ ∃e.B}, {@code Dom_p ≡ ∃p.⊤},
     * {@code Rng_p ≡ ∃p⁻.⊤}) for ontologies with DL-safe rules where
     * {@code km classify --properties} declines due to its internal nominal
     * top-property probe.
     */
    private ObjectPropertyModel propertiesByExistentialProbes(
            OWLOntology snapshot, Set<OWLObjectProperty> signature, boolean hasInverses) {
        recordReduction("R08_object_properties_existential_probes");
        List<OWLObjectProperty> props = new ArrayList<>(signature);
        props.sort(Comparator.comparing(p -> p.getIRI().toString()));
        int n = props.size();
        Map<OWLObjectProperty, Integer> idx = new HashMap<>();
        for (int i = 0; i < n; i++) idx.put(props.get(i), i);
        boolean[] universal = new boolean[n];
        BitSet[] told = new BitSet[n];
        for (int i = 0; i < n; i++) {
            told[i] = new BitSet(n);
            told[i].set(i);
        }
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                OWLSubObjectPropertyOfAxiom a = (OWLSubObjectPropertyOfAxiom) ax;
                OWLObjectProperty sub = a.getSubProperty().getNamedProperty();
                OWLObjectProperty sup = a.getSuperProperty().getNamedProperty();
                if (sub.isOWLTopObjectProperty() && idx.containsKey(sup)) {
                    universal[idx.get(sup)] = true;
                } else {
                    Integer u = idx.get(sub), v = idx.get(sup);
                    if (u != null && v != null) told[u].set(v);
                }
            } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom) {
                Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                boolean hasTop = sig.contains(df.getOWLTopObjectProperty());
                for (OWLObjectProperty p : sig) {
                    Integer u = idx.get(p);
                    if (u == null) continue;
                    if (hasTop) universal[u] = true;
                    for (OWLObjectProperty q : sig) {
                        Integer v = idx.get(q);
                        if (v != null) told[u].set(v);
                    }
                }
            } else if (ax instanceof OWLInverseObjectPropertiesAxiom) {
                Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                for (OWLObjectProperty p : sig) {
                    Integer u = idx.get(p);
                    if (u == null) continue;
                    for (OWLObjectProperty q : sig) {
                        Integer v = idx.get(q);
                        if (v != null) told[u].set(v);
                    }
                }
            }
        }
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                if (told[i].get(k)) told[i].or(told[k]);
            }
        }
        for (int i = 0; i < n; i++) {
            if (universal[i]) {
                for (int j = told[i].nextSetBit(0); j >= 0; j = told[i].nextSetBit(j + 1)) {
                    universal[j] = true;
                }
            }
        }
        List<OWLAxiom> defs = new ArrayList<>();
        OWLClass bCls = df.getOWLClass(fresh().next("OPB"));
        defs.add(df.getOWLDeclarationAxiom(bCls));
        String[] probeIri = new String[2 * n];
        Map<String, Integer> probeIdx = new HashMap<>();
        String[] domIri = new String[n];
        String[] rngIri = new String[n];
        for (int i = 0; i < n; i++) {
            OWLObjectProperty p = props.get(i);
            OWLClass pr = df.getOWLClass(fresh().next("OPProbe"));
            defs.add(df.getOWLEquivalentClassesAxiom(pr, df.getOWLObjectSomeValuesFrom(p, bCls)));
            probeIri[i] = pr.getIRI().toString();
            probeIdx.put(probeIri[i], i);

            OWLClass prInv = df.getOWLClass(fresh().next("OPInvProbe"));
            defs.add(df.getOWLEquivalentClassesAxiom(prInv,
                    df.getOWLObjectSomeValuesFrom(p.getInverseProperty(), bCls)));
            probeIri[i + n] = prInv.getIRI().toString();
            probeIdx.put(probeIri[i + n], i + n);

            OWLClass dom = df.getOWLClass(fresh().next("OPDom"));
            defs.add(df.getOWLEquivalentClassesAxiom(dom, df.getOWLObjectSomeValuesFrom(p, owlThing)));
            domIri[i] = dom.getIRI().toString();

            OWLClass rng = df.getOWLClass(fresh().next("OPRng"));
            defs.add(df.getOWLEquivalentClassesAxiom(rng,
                    df.getOWLObjectSomeValuesFrom(p.getInverseProperty(), owlThing)));
            rngIri[i] = rng.getIRI().toString();
        }
        ExtendedRun.Answer answer = extendedRun("object property hierarchy", defs, false, false);
        requireConsistent(answer, "object property hierarchy");
        Classifier.Properties rows = new Classifier.Properties();
        rows.consistent = true;
        boolean[] isBot = new boolean[n];
        for (int i = 0; i < n; i++) {
            if (answer.unsat.contains(probeIri[i]) || answer.unsat.contains(domIri[i])) {
                isBot[i] = true;
                rows.bottom.add(props.get(i).getIRI().toString());
            }
        }
        for (int i = 0; i < n; i++) {
            if (isBot[i]) continue;
            String pIri = props.get(i).getIRI().toString();
            if (universal[i]) rows.top.add(pIri);
            for (String sup : answer.supersOf(probeIri[i])) {
                Integer code = probeIdx.get(sup);
                if (code == null || code == i) continue;
                int base = code < n ? code : code - n;
                if (isBot[base]) continue;
                String supStr = code < n
                        ? props.get(base).getIRI().toString()
                        : "ObjectInverseOf(<" + props.get(base).getIRI().toString() + ">)";
                rows.subproperties.add(new String[]{pIri, supStr});
            }
            for (String sup : answer.supersOf(domIri[i])) {
                if (idByIri.containsKey(sup)) {
                    rows.domains.add(new String[]{pIri, sup});
                }
            }
            for (String sup : answer.supersOf(rngIri[i])) {
                if (idByIri.containsKey(sup)) {
                    rows.ranges.add(new String[]{pIri, sup});
                }
            }
        }
        return new ObjectPropertyModel(df, signature, rows, hasInverses);
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
        if (ce.isAnonymous()) return disjointClassesOf(ce);
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
        return disjointClassesOf(ce);
    }

    @Override public synchronized NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty pe, boolean direct) {
        checkPreConditions();
        DataPropertyModel model = ensureDataProperties();
        if (model.isEmpty(pe)) {
            // No pair: every class is a domain, and the direct domain is the bottom node.
            return classNodeSet(nonBottomRepsWithBottom(), direct, true);
        }
        Set<Integer> reps = new TreeSet<>();
        reps.add(repId[thingId]);
        if (model.hasSyntacticDomains()) {
            int lowest = model.domainRep(pe);
            if (lowest >= 0) {
                reps.add(lowest);
                int[] sups = supersByRep[lowest];
                if (sups != null) for (int sup : sups) reps.add(sup);
            }
        } else {
            for (String iri : model.domainIris(pe)) {
                Integer id = idByIri.get(normalizeIri(iri));
                if (id == null) continue;
                int r = repId[id];
                reps.add(r);
                int[] sups = supersByRep[r];
                if (sups != null) for (int s : sups) reps.add(s);
            }
        }
        return classNodeSet(toArray(reps), direct, false);
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
        return disjointObjectProperties(model, pe);
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
        return computeObjectPropertyValues(ind, pe);
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
        return disjointDataProperties(model, named);
    }
    @Override public synchronized Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual ind, OWLDataProperty pe) {
        checkPreConditions();
        return computeDataPropertyValues(ind, pe);
    }

    @Override public synchronized NodeSet<OWLNamedIndividual> getDifferentIndividuals(OWLNamedIndividual ind) {
        checkPreConditions();
        return computeDifferentIndividuals(ind);
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

    private static final String CLASSIFYING_DATA_PROPERTIES = "Classifying data properties";

    /**
     * The data property model of the committed revision: built from the stated
     * axioms and the taxonomy inside {@link DataPropertyModel}'s syntactic
     * fragment, and from {@code km classify --lines --data-properties} (or a
     * pair-free probe classification when the signature has more than 40 data
     * properties) outside it.
     */
    private DataPropertyModel ensureDataProperties() {
        ensureClassified();
        DataPropertyModel model = dataModel;
        if (model != null) return model;
        if (dataFailure != null) throw dataFailure;
        OWLOntology snapshot = getCommittedOntologySnapshot();
        try {
            model = DataPropertyModel.build(df, snapshot, taxonomy);
            recordReduction("R09_syntactic_data_property_model");
            dataModel = model;
            return model;
        } catch (UnsupportedOperationException outsideSyntacticFragment) {
            // Fall through to native --data-properties or pair-free probe classification.
        }
        DataPropertyModel[] out = new DataPropertyModel[1];
        long t0 = System.nanoTime();
        try {
            runTask(CLASSIFYING_DATA_PROPERTIES, () -> out[0] = dataPropertiesNow(snapshot));
        } catch (RuntimeException failure) {
            if (cacheableWholeRevision(failure, (System.nanoTime() - t0) / 1_000_000L)) {
                dataFailure = failure;
            }
            throw failure;
        }
        dataModel = out[0];
        return out[0];
    }

    private DataPropertyModel dataPropertiesNow(OWLOntology snapshot) {
        if (!consistent) {
            return DataPropertyModel.fromRows(df, Collections.<OWLDataProperty>emptySet(), null);
        }
        try {
            Set<OWLDataProperty> signature = new LinkedHashSet<>(snapshot.getDataPropertiesInSignature());
            signature.remove(df.getOWLTopDataProperty());
            signature.remove(df.getOWLBottomDataProperty());
            if (signature.isEmpty()) {
                return DataPropertyModel.fromRows(df, signature, null);
            }
            if (mayEntailNonToldDataSubProperty(snapshot) && !needsLiteralDataPropertyProbes(snapshot)) {
                try {
                    String dpSource = canUseTBoxQuerySource(Collections.emptyList())
                            ? tboxQuerySource() : querySource();
                    Classifier.DataProperties rows = Classifier.dataProperties(dpSource,
                            process -> {
                                realizeProcess = process;
                                if (process != null && (interruptRequested || timedOut)) {
                                    NativeProcessTree.terminateAndWait(process);
                                }
                            });
                    return rows.consistent
                            ? DataPropertyModel.fromRows(df, signature, rows)
                            : DataPropertyModel.fromRows(df, Collections.<OWLDataProperty>emptySet(), null);
                } catch (UnsupportedOperationException declined) {
                    // Fall through to rdfs:Literal existential probes.
                }
            }
            return dataPropertiesByLiteralProbes(snapshot, signature);
        } catch (RuntimeException error) {
            throw error;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
    }

    /**
     * Under OWL 2 Direct Semantics, two satisfiable non-universal data
     * properties {@code p, q} can entail {@code p ⊑ q} outside the reflexive-
     * transitive closure of told {@code SubDataPropertyOf} and
     * {@code EquivalentDataProperties} axioms only when the ontology contains a
     * construct that can collapse their extensions on a finite domain or value
     * space (a functional or max/exact-cardinality data restriction or
     * {@code DataHasValue} combined with nominals or {@code DataOneOf}, or a
     * {@code SWRLRule}).
     */
    private static boolean mayEntailNonToldDataSubProperty(OWLOntology snapshot) {
        boolean hasFuncData = false;
        boolean hasValuePin = false;
        boolean hasNominalOrDataOneOf = false;
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule) return true;
            if (ax instanceof OWLFunctionalDataPropertyAxiom) hasFuncData = true;
            if (ax instanceof OWLDataPropertyAssertionAxiom) hasValuePin = true;
            if (ax instanceof OWLDataPropertyRangeAxiom
                    && ((OWLDataPropertyRangeAxiom) ax).getRange() instanceof OWLDataOneOf) {
                hasNominalOrDataOneOf = true;
                hasFuncData = true;
                hasValuePin = true;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf || ce instanceof OWLObjectHasValue) {
                    hasNominalOrDataOneOf = true;
                }
                if (ce instanceof OWLDataHasValue) {
                    hasFuncData = true;
                    hasValuePin = true;
                }
                if (ce instanceof OWLDataMaxCardinality || ce instanceof OWLDataExactCardinality) {
                    hasFuncData = true;
                }
                if (ce instanceof OWLDataSomeValuesFrom
                        && ((OWLDataSomeValuesFrom) ce).getFiller() instanceof OWLDataOneOf) {
                    hasNominalOrDataOneOf = true;
                    hasFuncData = true;
                    hasValuePin = true;
                }
                if (ce instanceof OWLDataAllValuesFrom
                        && ((OWLDataAllValuesFrom) ce).getFiller() instanceof OWLDataOneOf) {
                    hasNominalOrDataOneOf = true;
                    hasFuncData = true;
                    hasValuePin = true;
                }
            }
        }
        return hasFuncData && hasValuePin && hasNominalOrDataOneOf;
    }

    /**
     * Whether the ontology uses constructs (SWRL rules, cardinality
     * restrictions, datatype facet restrictions or floating-point datatypes)
     * that {@code konclude_ht} handles only when all datatype symbols stay in
     * its built-in atomic map, so {@code DataSomeValuesFrom(p, rdfs:Literal)}
     * probes should be used instead of {@code --unknown-datatypes=free}.
     */
    private static boolean needsLiteralDataPropertyProbes(OWLOntology snapshot) {
        for (OWLDatatype dt : snapshot.getDatatypesInSignature()) {
            String iri = dt.getIRI().toString();
            if (iri.endsWith("#double") || iri.endsWith("#float")) return true;
        }
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule) return true;
            if (ax instanceof OWLDataPropertyRangeAxiom
                    && ((OWLDataPropertyRangeAxiom) ax).getRange() instanceof OWLDatatypeRestriction) {
                return true;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectCardinalityRestriction
                        || ce instanceof OWLDataCardinalityRestriction) {
                    return true;
                }
                if (ce instanceof OWLDataSomeValuesFrom
                        && ((OWLDataSomeValuesFrom) ce).getFiller() instanceof OWLDatatypeRestriction) {
                    return true;
                }
                if (ce instanceof OWLDataAllValuesFrom
                        && ((OWLDataAllValuesFrom) ce).getFiller() instanceof OWLDatatypeRestriction) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean hasLocalDataValueDisjointness(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule) return true;
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLDataAllValuesFrom
                        || ce instanceof OWLDataMaxCardinality
                        || ce instanceof OWLDataExactCardinality) {
                    return true;
                }
                if (ce instanceof OWLDataSomeValuesFrom
                        && ((OWLDataSomeValuesFrom) ce).getFiller() instanceof OWLDataComplementOf) {
                    return true;
                }
            }
        }
        return false;
    }

    private DataPropertyModel dataPropertiesByLiteralProbes(OWLOntology snapshot, Set<OWLDataProperty> signature) {
        recordReduction("R10_data_properties_literal_probes");
        List<OWLDataProperty> props = new ArrayList<>(signature);
        props.sort(Comparator.comparing(p -> p.getIRI().toString()));
        int n = props.size();
        Map<OWLDataProperty, Integer> idx = new HashMap<>();
        for (int i = 0; i < n; i++) idx.put(props.get(i), i);
        BitSet[] told = new BitSet[n];
        BitSet[] statedDisjoint = new BitSet[n];
        boolean[] universal = new boolean[n];
        List<Set<IRI>> ranges = new ArrayList<>();
        List<Set<Object>> oneOfs = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            told[i] = new BitSet(n);
            told[i].set(i);
            statedDisjoint[i] = new BitSet(n);
            ranges.add(new TreeSet<>());
            oneOfs.add(null);
        }
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSubDataPropertyOfAxiom) {
                OWLSubDataPropertyOfAxiom a = (OWLSubDataPropertyOfAxiom) ax;
                OWLDataProperty sub = a.getSubProperty().asOWLDataProperty();
                OWLDataProperty sup = a.getSuperProperty().asOWLDataProperty();
                if (sub.isOWLTopDataProperty() && idx.containsKey(sup)) {
                    universal[idx.get(sup)] = true;
                } else {
                    Integer u = idx.get(sub), v = idx.get(sup);
                    if (u != null && v != null) told[u].set(v);
                }
            } else if (ax instanceof OWLEquivalentDataPropertiesAxiom) {
                List<OWLDataPropertyExpression> eq = new ArrayList<>(
                        ((OWLEquivalentDataPropertiesAxiom) ax).getProperties());
                boolean hasTop = false;
                for (OWLDataPropertyExpression pe : eq) {
                    if (pe.isOWLTopDataProperty()) hasTop = true;
                }
                for (int i = 0; i < eq.size(); i++) {
                    OWLDataProperty pi = eq.get(i).asOWLDataProperty();
                    OWLDataProperty pj = eq.get((i + 1) % eq.size()).asOWLDataProperty();
                    if (hasTop && idx.containsKey(pi)) universal[idx.get(pi)] = true;
                    Integer u = idx.get(pi), v = idx.get(pj);
                    if (u != null && v != null) {
                        told[u].set(v);
                        told[v].set(u);
                    }
                }
            } else if (ax instanceof OWLDisjointDataPropertiesAxiom) {
                List<OWLDataPropertyExpression> dpList = new ArrayList<>(
                        ((OWLDisjointDataPropertiesAxiom) ax).getProperties());
                for (int i = 0; i < dpList.size(); i++) {
                    for (int j = i + 1; j < dpList.size(); j++) {
                        Integer u = idx.get(dpList.get(i).asOWLDataProperty());
                        Integer v = idx.get(dpList.get(j).asOWLDataProperty());
                        if (u != null && v != null) {
                            statedDisjoint[u].set(v);
                            statedDisjoint[v].set(u);
                        }
                    }
                }
            } else if (ax instanceof OWLDataPropertyRangeAxiom) {
                OWLDataPropertyRangeAxiom a = (OWLDataPropertyRangeAxiom) ax;
                Integer u = idx.get(a.getProperty().asOWLDataProperty());
                if (u != null) {
                    OWLDataRange range = a.getRange();
                    if (range instanceof OWLDatatype && !range.isTopDatatype()) {
                        ranges.get(u).add(((OWLDatatype) range).getIRI());
                    } else if (range instanceof OWLDataOneOf) {
                        Set<Object> vals = new HashSet<>();
                        for (OWLLiteral l : ((OWLDataOneOf) range).getValues()) {
                            vals.add(DataValues.valueKey(l));
                            ranges.get(u).add(l.getDatatype().getIRI());
                        }
                        if (oneOfs.get(u) == null) oneOfs.set(u, vals);
                        else oneOfs.get(u).retainAll(vals);
                    }
                }
            }
        }
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                if (told[i].get(k)) told[i].or(told[k]);
            }
        }
        for (int i = 0; i < n; i++) {
            if (universal[i]) {
                for (int j = told[i].nextSetBit(0); j >= 0; j = told[i].nextSetBit(j + 1)) {
                    universal[j] = true;
                }
            }
        }
        List<OWLAxiom> defs = new ArrayList<>();
        List<OWLClass> someClasses = new ArrayList<>();
        List<String> someIris = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            OWLClass some = df.getOWLClass(fresh().next("DPSome"));
            someClasses.add(some);
            defs.add(df.getOWLEquivalentClassesAxiom(some,
                    df.getOWLDataSomeValuesFrom(props.get(i), df.getTopDatatype())));
            someIris.add(some.getIRI().toString());
        }
        boolean includePairs = n <= 64;
        String[][] pairIri = includePairs ? new String[n][n] : null;
        if (includePairs) {
            for (int i = 0; i < n; i++) {
                for (int j = i + 1; j < n; j++) {
                    OWLClass pr = df.getOWLClass(fresh().next("DPPair"));
                    defs.add(df.getOWLSubClassOfAxiom(pr,
                            and(someClasses.get(i), someClasses.get(j))));
                    pairIri[i][j] = pr.getIRI().toString();
                }
            }
        }
        ExtendedRun.Answer answer = extendedRun("data property hierarchy", defs, false, false);
        requireConsistent(answer, "data property hierarchy");
        Classifier.DataProperties rows = new Classifier.DataProperties();
        rows.consistent = true;
        rows.disjointComputed = includePairs;
        boolean[] isBot = new boolean[n];
        for (int i = 0; i < n; i++) {
            Set<IRI> ownRanges = new TreeSet<>();
            Set<Object> ownOneOf = null;
            for (int r = told[i].nextSetBit(0); r >= 0; r = told[i].nextSetBit(r + 1)) {
                ownRanges.addAll(ranges.get(r));
                if (oneOfs.get(r) != null) {
                    if (ownOneOf == null) ownOneOf = new HashSet<>(oneOfs.get(r));
                    else ownOneOf.retainAll(oneOfs.get(r));
                }
            }
            if (answer.unsat.contains(someIris.get(i))
                    || !DataPropertyModel.rangesCompatible(ownRanges)
                    || (ownOneOf != null && ownOneOf.isEmpty())) {
                isBot[i] = true;
                rows.bottom.add(props.get(i).getIRI().toString());
            }
        }
        for (int i = 0; i < n; i++) {
            if (isBot[i]) continue;
            String propIri = props.get(i).getIRI().toString();
            if (universal[i]) rows.top.add(propIri);
            for (int j = told[i].nextSetBit(0); j >= 0; j = told[i].nextSetBit(j + 1)) {
                if (j != i && !isBot[j]) {
                    rows.subproperties.add(new String[]{propIri, props.get(j).getIRI().toString()});
                }
            }
            for (String sup : answer.supersOf(someIris.get(i))) {
                if (idByIri.containsKey(sup)) {
                    rows.domains.add(new String[]{propIri, sup});
                }
            }
            Set<String> entailedSubs = new HashSet<>();
            String sIri = someIris.get(i);
            if (answer.top.contains(sIri)) {
                entailedSubs.add(owlThing.getIRI().toString());
            }
            for (Map.Entry<String, Set<String>> row : answer.supers.entrySet()) {
                if (row.getValue().contains(sIri)) {
                    entailedSubs.add(row.getKey());
                }
            }
            classesWithDataSome.put(props.get(i), entailedSubs);
        }
        if (includePairs) {
            for (int i = 0; i < n; i++) {
                if (isBot[i]) continue;
                for (int j = i + 1; j < n; j++) {
                    if (isBot[j]) continue;
                    boolean disj = answer.unsat.contains(pairIri[i][j]);
                    if (!disj) {
                        for (int u = told[i].nextSetBit(0); u >= 0 && !disj; u = told[i].nextSetBit(u + 1)) {
                            for (int v = told[j].nextSetBit(0); v >= 0; v = told[j].nextSetBit(v + 1)) {
                                if (statedDisjoint[u].get(v)) {
                                    disj = true;
                                    break;
                                }
                            }
                        }
                    }
                    if (!disj) {
                        Set<IRI> jr = new TreeSet<>();
                        Set<Object> jo = null;
                        for (int r = told[i].nextSetBit(0); r >= 0; r = told[i].nextSetBit(r + 1)) {
                            jr.addAll(ranges.get(r));
                            if (oneOfs.get(r) != null) {
                                if (jo == null) jo = new HashSet<>(oneOfs.get(r));
                                else jo.retainAll(oneOfs.get(r));
                            }
                        }
                        for (int r = told[j].nextSetBit(0); r >= 0; r = told[j].nextSetBit(r + 1)) {
                            jr.addAll(ranges.get(r));
                            if (oneOfs.get(r) != null) {
                                if (jo == null) jo = new HashSet<>(oneOfs.get(r));
                                else jo.retainAll(oneOfs.get(r));
                            }
                        }
                        if (!DataPropertyModel.rangesCompatible(jr) || (jo != null && jo.isEmpty())) {
                            disj = true;
                        }
                    }
                    if (disj) {
                        String pi = props.get(i).getIRI().toString();
                        String pj = props.get(j).getIRI().toString();
                        rows.disjoint.add(new String[]{pi, pj});
                        rows.disjoint.add(new String[]{pj, pi});
                    }
                }
            }
        }
        return DataPropertyModel.fromRows(df, signature, rows);
    }

    // ---- fresh-definition reductions (W5a) -----------------------------------
    //
    // Each query below is an entailment question about the committed ontology O.
    // It is answered by one km run on O extended with fresh axioms over fresh
    // names (ExtendedRun), and the answer is read from that run's rows. Two kinds:
    //  - definitional: Q ≡ CE for a fresh class Q. O ∪ {Q ≡ CE} is a conservative
    //    extension of O (every model of O expands to one by setting Q to CE), so
    //    the rows about O's own names are O's, and Q's rows answer CE.
    //  - refutation: O ⊨ α iff O ∪ {¬α} is inconsistent, with ¬α written as
    //    assertions about fresh individuals (the existential witnesses of ¬α).
    //    These additions are not conservative on purpose; the run only reports
    //    consistency.
    // Answers and failures are cached per committed revision (cleared on commit,
    // failures also on flush). A run that km declines throws; nothing is guessed.

    private static final String CHECKING_ENTAILMENT = "Checking entailment";
    private static final String CLASSIFYING_EXPRESSION = "Classifying a class expression";
    private static final String COMPUTING_VALUES = "Computing property values";

    /** Answers (or remembered failures) of reduction runs on the committed revision. */
    private final Map<Object, Object> reductions = new HashMap<>();
    private final Map<OWLDataProperty, Set<String>> classesWithDataSome = new HashMap<>();
    private OWLOntology querySnapshot;
    private String querySource;
    private ExtendedRun.Fresh freshNames;
    private int reductionRuns;

    /** Native reduction runs made so far (for tests). */
    synchronized int reductionRunCount() { return reductionRuns; }

    private String rawQuerySource;
    private String tboxQuerySource;
    private Boolean aboxConservativeForTBox;

    private void clearReductions() {
        reductions.clear();
        classesWithDataSome.clear();
        querySnapshot = null;
        querySource = null;
        rawQuerySource = null;
        tboxQuerySource = null;
        aboxConservativeForTBox = null;
        freshNames = null;
    }

    private boolean isABoxConservativeForTBox() {
        if (aboxConservativeForTBox != null) return aboxConservativeForTBox;
        OWLOntology snap = querySnapshot();
        if (snap.getIndividualsInSignature().isEmpty()) {
            aboxConservativeForTBox = false;
            return false;
        }
        for (OWLAxiom ax : snap.getLogicalAxioms()) {
            if (ax instanceof OWLHasKeyAxiom || ax instanceof SWRLRule) {
                aboxConservativeForTBox = false;
                return false;
            }
            for (OWLObjectProperty op : ax.getObjectPropertiesInSignature()) {
                if (op.isOWLTopObjectProperty()) {
                    aboxConservativeForTBox = false;
                    return false;
                }
            }
            for (OWLDataProperty dp : ax.getDataPropertiesInSignature()) {
                if (dp.isOWLTopDataProperty()) {
                    aboxConservativeForTBox = false;
                    return false;
                }
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf || ce instanceof OWLObjectHasValue) {
                    aboxConservativeForTBox = false;
                    return false;
                }
            }
        }
        aboxConservativeForTBox = true;
        return true;
    }

    private boolean canUseTBoxQuerySource(Collection<? extends OWLAxiom> extra) {
        if (!consistent || activeRollup != null || !isABoxConservativeForTBox()) return false;
        if (extra == null || extra.isEmpty()) return true;
        Set<OWLNamedIndividual> sigInds = signatureIndividuals();
        for (OWLAxiom ax : extra) {
            for (OWLNamedIndividual ind : ax.getIndividualsInSignature()) {
                if (sigInds.contains(ind)) return false;
            }
            for (OWLObjectProperty op : ax.getObjectPropertiesInSignature()) {
                if (op.isOWLTopObjectProperty()) return false;
            }
            for (OWLDataProperty dp : ax.getDataPropertiesInSignature()) {
                if (dp.isOWLTopDataProperty()) return false;
            }
        }
        return true;
    }

    private String tboxQuerySource() {
        recordReduction("R20_tbox_conservativity_projection");
        if (tboxQuerySource == null) {
            try {
                OWLOntology snap = querySnapshot();
                OWLOntologyManager mgr = org.semanticweb.owlapi.apibinding.OWLManager.createOWLOntologyManager();
                OWLOntology copy = mgr.createOntology();
                for (OWLAxiom ax : snap.getAxioms()) {
                    if (ax instanceof OWLIndividualAxiom) continue;
                    if (ax instanceof OWLDeclarationAxiom
                            && ((OWLDeclarationAxiom) ax).getEntity().isOWLNamedIndividual()) {
                        continue;
                    }
                    mgr.addAxiom(copy, ax);
                }
                tboxQuerySource = FlattenedOntology.functionalSyntaxOfSnapshot(copy);
            } catch (RuntimeException e) {
                throw e;
            } catch (Exception e) {
                throw new ReasonerInternalException(e);
            }
        }
        return tboxQuerySource;
    }

    private OWLOntology querySnapshot() {
        if (querySnapshot == null) {
            querySnapshot = getCommittedOntologySnapshot();
        }
        return querySnapshot;
    }

    private String rawQuerySource() {
        if (rawQuerySource == null) {
            if (activeRollup != null) {
                rawQuerySource = activeRollup.rolledSource;
            } else {
                try {
                    rawQuerySource = FlattenedOntology.functionalSyntaxOfSnapshot(querySnapshot());
                } catch (RuntimeException e) {
                    throw e;
                } catch (Exception e) {
                    throw new ReasonerInternalException(e);
                }
            }
        }
        return rawQuerySource;
    }

    private String querySource() {
        if (querySource == null) {
            if (activeRollup != null) {
                querySource = activeRollup.rolledSource;
            } else {
                String pregrounded = ForestABoxRollup.tryPregroundRules(querySnapshot(), df);
                querySource = pregrounded != null ? pregrounded : rawQuerySource();
            }
        }
        return querySource;
    }

    private boolean introducesFreshIndividuals(Collection<? extends OWLAxiom> extra) {
        if (extra == null || extra.isEmpty()) return false;
        Set<OWLNamedIndividual> sigInds = signatureIndividuals();
        for (OWLAxiom ax : extra) {
            for (OWLNamedIndividual ind : ax.getIndividualsInSignature()) {
                if (!sigInds.contains(ind)) return true;
            }
        }
        return false;
    }

    private ExtendedRun.Fresh fresh() {
        if (freshNames == null) freshNames = new ExtendedRun.Fresh(querySnapshot());
        return freshNames;
    }

    private Object peek(Object key) {
        Object held = reductions.get(key);
        return held instanceof RuntimeException ? null : held;
    }

    /** The cached answer for {@code key}, or one computed now as a monitored task. */
    @SuppressWarnings("unchecked")
    private <T> T reduce(Object key, String title, java.util.function.Supplier<T> compute) {
        Object held = reductions.get(key);
        if (held instanceof RuntimeException) throw (RuntimeException) held;
        if (held != null) return (T) held;
        Object[] out = new Object[1];
        try {
            runTask(title, () -> out[0] = compute.get());
        } catch (RuntimeException failure) {
            if (cacheable(failure)) reductions.put(key, failure);
            throw failure;
        }
        reductions.put(key, out[0]);
        return (T) out[0];
    }

    /** One km run on the committed source plus {@code extra}. */
    private ExtendedRun.Answer extendedRun(String label, Collection<? extends OWLAxiom> extra,
                                           boolean realize, boolean top) {
        return extendedRun(label, extra, realize, top, false);
    }

    private ExtendedRun.Answer extendedRun(String label, Collection<? extends OWLAxiom> extra,
                                           boolean realize, boolean top, boolean freeUnknownDatatypes) {
        reductionRuns++;
        String baseSource;
        if (!realize && canUseTBoxQuerySource(extra)) {
            baseSource = tboxQuerySource();
        } else if (!querySnapshot().getAxioms(AxiomType.SWRL_RULE).isEmpty()
                && introducesFreshIndividuals(extra)) {
            baseSource = rawQuerySource();
        } else {
            baseSource = querySource();
        }
        try {
            return ExtendedRun.run(baseSource, df, extra, realize, top, freeUnknownDatatypes, label, process -> {
                realizeProcess = process;
                if (process != null && (interruptRequested || timedOut)) {
                    NativeProcessTree.terminateAndWait(process);
                }
            });
        } catch (RuntimeException error) {
            throw error;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
    }

    /** A definitional extension is consistent whenever O is; anything else is an engine fault. */
    private static void requireConsistent(ExtendedRun.Answer answer, String label) {
        if (!answer.consistent) {
            throw new ReasonerInternalException("Kobayashi-MaRust found the " + label
                    + " extension inconsistent although the ontology is consistent and the"
                    + " extension only defines fresh names; refusing the answer");
        }
    }

    private Set<OWLNamedIndividual> signatureIndividuals() {
        return new LinkedHashSet<>(querySnapshot().getIndividualsInSignature());
    }

    // ---- class expressions -------------------------------------------------------

    /** What one run with {@code Q ≡ CE} says about Q, in representatives of O's taxonomy. */
    private static final class ClassAnswer {
        boolean unsat;
        boolean top;
        /** Reps of the named classes above Q (owl:Thing and Q's equivalents included). */
        int[] supers = EMPTY_INTS;
        /** Reps of the satisfiable named classes below Q (Q's equivalents included). */
        int[] subs = EMPTY_INTS;
        int[] equivalents = EMPTY_INTS;
        /** Named individuals of the signature in Q; null when the run did not realize. */
        Set<OWLNamedIndividual> instances;
    }

    /**
     * The answer for a class expression. Exact: {@code Q ≡ CE} with fresh {@code Q}
     * is a conservative extension, so {@code O ⊨ Q ⊑ D} iff {@code O ⊨ CE ⊑ D}, and
     * likewise for subclasses, unsatisfiability and instances.
     */
    private ClassAnswer classAnswer(OWLClassExpression ce, boolean instances) {
        Object realized = peek(Arrays.asList("class", ce, true));
        if (realized != null) return (ClassAnswer) realized;
        if (activeRollup != null) {
            return reduce(Arrays.asList("class", ce, true), CLASSIFYING_EXPRESSION,
                    () -> {
                        recordReduction("R02_rollup_class_expression");
                        return classAnswerOnRollup(ce);
                    });
        }
        boolean eagerRealize = !instances
                && !signatureIndividuals().isEmpty()
                && (this.realized != null
                        || precomputedTypes.contains(InferenceType.CLASS_ASSERTIONS)
                        || !querySnapshot().getAxioms(AxiomType.SWRL_RULE).isEmpty())
                && querySnapshot().getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY).isEmpty();
        boolean runWithInstances = instances || eagerRealize;
        if (ce instanceof OWLObjectComplementOf) {
            OWLClassExpression inner = ((OWLObjectComplementOf) ce).getOperand();
            if (isNegativeHornSubClass(inner) && isHornOntology(querySnapshot())) {
                recordReduction("R17_horn_complement_probes");
                return hornComplementClassAnswer(ce, inner, runWithInstances);
            }
        }
        if (ce instanceof OWLObjectMinCardinality
                && ((OWLObjectMinCardinality) ce).getCardinality() >= 2
                && !querySnapshot().getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY).isEmpty()
                && querySnapshot().getAxioms(AxiomType.SWRL_RULE).isEmpty()) {
            recordReduction("R18_min_cardinality_witness_probes");
            return classAnswerForMinCardinality((OWLObjectMinCardinality) ce, runWithInstances);
        }
        return reduce(Arrays.asList("class", ce, runWithInstances), CLASSIFYING_EXPRESSION, () -> {
            recordReduction("R16_class_expression_extension");
            OWLClass q = df.getOWLClass(fresh().next("Q"));
            String label = runWithInstances ? "class expression query with instances" : "class expression query";
            ExtendedRun.Answer answer = extendedRun(label,
                    Collections.singletonList(df.getOWLEquivalentClassesAxiom(q, ce)), runWithInstances, true);
            requireConsistent(answer, label);
            return classAnswerOf(answer, ce, q.getIRI().toString(), runWithInstances);
        });
    }

    /**
     * Exact Horn-preserving positive-polarity probe reduction for
     * {@code ObjectComplementOf(inner)} on Horn ontologies. By the Direct
     * Product Theorem for Horn theories (Chang and Keisler 1990, Theorem 4.1.6),
     * models of a Horn ontology {@code O} are closed under binary direct
     * products, so {@code O ⊨ ¬inner ⊑ B} iff {@code O ⊨ ⊤ ⊑ inner} or
     * {@code O ⊨ ⊤ ⊑ B}. Subclasses {@code C_r ⊑ ¬inner} and instances
     * {@code (¬inner)(a)} hold iff {@code C_r ⊓ inner ⊑ ⊥} and
     * {@code {a} ⊓ inner ⊑ ⊥}, which are tested in positive polarity by the
     * engine without introducing a universal root disjunction.
     */
    private ClassAnswer hornComplementClassAnswer(
            OWLClassExpression ce, OWLClassExpression inner, boolean runWithInstances) {
        return reduce(Arrays.asList("class", ce, runWithInstances), CLASSIFYING_EXPRESSION, () -> {
            int bottom = repId[nothingId];
            int thingRep = repId[thingId];
            if (!inner.isAnonymous() && !isFresh(inner)
                    && (!runWithInstances || signatureIndividuals().isEmpty())) {
                Object cachedDisj = peek(Arrays.asList("disjoint-classes", inner));
                if (cachedDisj != null) {
                    @SuppressWarnings("unchecked")
                    List<Integer> disjReps = (List<Integer>) cachedDisj;
                    int innerRep = repIdOf(inner);
                    ClassAnswer out = new ClassAnswer();
                    out.unsat = innerRep == thingRep;
                    if (!out.unsat) {
                        Set<Integer> sub = new TreeSet<>(disjReps);
                        out.top = innerRep == bottom;
                        if (out.top) {
                            for (int r : nonBottomReps()) sub.add(r);
                        }
                        out.supers = new int[]{thingRep};
                        out.subs = toArray(sub);
                        out.equivalents = out.top ? new int[]{thingRep} : EMPTY_INTS;
                    }
                    if (runWithInstances) out.instances = Collections.emptySet();
                    return out;
                }
            }
            List<OWLAxiom> defs = new ArrayList<>();
            OWLClass pSup = df.getOWLClass(fresh().next("PSup"));
            defs.add(df.getOWLSubClassOfAxiom(inner, pSup));
            String pSupIri = pSup.getIRI().toString();
            OWLClass pSub = df.getOWLClass(fresh().next("PSub"));
            defs.add(df.getOWLSubClassOfAxiom(pSub, inner));
            String pSubIri = pSub.getIRI().toString();
            Map<String, Integer> byProbe = new LinkedHashMap<>();
            int[] candidates = nonBottomReps();
            for (int r : candidates) {
                if (r == thingRep) continue;
                OWLClass x = df.getOWLClass(fresh().next("X"));
                defs.add(df.getOWLSubClassOfAxiom(x, and(classById[r], pSub)));
                byProbe.put(x.getIRI().toString(), r);
            }
            Map<String, OWLNamedIndividual> indProbes = new LinkedHashMap<>();
            if (runWithInstances) {
                OWLOntology snap = querySnapshot();
                boolean pureClassABox = hasPureClassAssertionABox(snap);
                Map<OWLNamedIndividual, List<OWLClassExpression>> assertedByInd = new HashMap<>();
                if (pureClassABox) {
                    for (OWLClassAssertionAxiom ca : snap.getAxioms(AxiomType.CLASS_ASSERTION)) {
                        if (ca.getIndividual().isNamed()) {
                            assertedByInd.computeIfAbsent(
                                    ca.getIndividual().asOWLNamedIndividual(), k -> new ArrayList<>())
                                    .add(ca.getClassExpression());
                        }
                    }
                }
                for (OWLNamedIndividual ind : signatureIndividuals()) {
                    OWLClass y = df.getOWLClass(fresh().next("Y"));
                    OWLClassExpression indExpr;
                    if (pureClassABox) {
                        List<OWLClassExpression> list = assertedByInd.get(ind);
                        if (list == null || list.isEmpty()) {
                            indExpr = owlThing;
                        } else if (list.size() == 1) {
                            indExpr = list.get(0);
                        } else {
                            indExpr = df.getOWLObjectIntersectionOf(new LinkedHashSet<>(list));
                        }
                    } else {
                        indExpr = df.getOWLObjectOneOf(ind);
                    }
                    defs.add(df.getOWLSubClassOfAxiom(y, and(indExpr, pSub)));
                    indProbes.put(y.getIRI().toString(), ind);
                }
            }
            String label = runWithInstances ? "class expression query with instances" : "class expression query";
            ExtendedRun.Answer answer = extendedRun(label, defs, false, true);
            requireConsistent(answer, label);
            ClassAnswer out = new ClassAnswer();
            out.unsat = answer.top.contains(pSupIri)
                    || (!inner.isAnonymous() && !isFresh(inner) && repIdOf(inner) == thingRep);
            if (!out.unsat) {
                Set<Integer> sub = new TreeSet<>();
                List<Integer> disjList = new ArrayList<>();
                out.top = answer.unsat.contains(pSubIri)
                        || (!inner.isAnonymous() && !isFresh(inner) && repIdOf(inner) == bottom);
                if (out.top) {
                    for (int r : candidates) {
                        sub.add(r);
                        disjList.add(r);
                    }
                } else {
                    for (Map.Entry<String, Integer> e : byProbe.entrySet()) {
                        if (answer.unsat.contains(e.getKey())) {
                            sub.add(e.getValue());
                            disjList.add(e.getValue());
                        }
                    }
                }
                reductions.putIfAbsent(Arrays.asList("disjoint-classes", inner), disjList);
                out.supers = new int[]{thingRep};
                out.subs = toArray(sub);
                out.equivalents = out.top ? new int[]{thingRep} : EMPTY_INTS;
            }
            if (runWithInstances) {
                out.instances = new LinkedHashSet<>();
                if (!out.unsat) {
                    if (out.top) {
                        out.instances.addAll(signatureIndividuals());
                    } else {
                        for (Map.Entry<String, OWLNamedIndividual> e : indProbes.entrySet()) {
                            if (answer.unsat.contains(e.getKey())) {
                                out.instances.add(e.getValue());
                            }
                        }
                    }
                }
            }
            return out;
        });
    }

    private static boolean isHornOntology(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof OWLDisjointUnionAxiom
                    || ax instanceof OWLFunctionalObjectPropertyAxiom
                    || ax instanceof OWLInverseFunctionalObjectPropertyAxiom
                    || ax instanceof OWLFunctionalDataPropertyAxiom) {
                return false;
            }
            if (ax instanceof OWLSubClassOfAxiom) {
                OWLSubClassOfAxiom sca = (OWLSubClassOfAxiom) ax;
                if (!isNegativeHornSubClass(sca.getSubClass())
                        || !isPositiveHornSuperClass(sca.getSuperClass())) {
                    return false;
                }
            } else if (ax instanceof OWLEquivalentClassesAxiom) {
                for (OWLClassExpression ce : ((OWLEquivalentClassesAxiom) ax).getClassExpressions()) {
                    if (!isNegativeHornSubClass(ce) || !isPositiveHornSuperClass(ce)) return false;
                }
            } else if (ax instanceof OWLDisjointClassesAxiom) {
                for (OWLClassExpression ce : ((OWLDisjointClassesAxiom) ax).getClassExpressions()) {
                    if (!isNegativeHornSubClass(ce)) return false;
                }
            } else if (ax instanceof OWLObjectPropertyDomainAxiom) {
                if (!isPositiveHornSuperClass(((OWLObjectPropertyDomainAxiom) ax).getDomain())) return false;
            } else if (ax instanceof OWLObjectPropertyRangeAxiom) {
                if (!isPositiveHornSuperClass(((OWLObjectPropertyRangeAxiom) ax).getRange())) return false;
            } else if (ax instanceof OWLDataPropertyDomainAxiom) {
                if (!isPositiveHornSuperClass(((OWLDataPropertyDomainAxiom) ax).getDomain())) return false;
            } else if (ax instanceof OWLDataPropertyRangeAxiom) {
                if (!(((OWLDataPropertyRangeAxiom) ax).getRange() instanceof OWLDatatype)) return false;
            } else if (ax instanceof OWLClassAssertionAxiom) {
                if (!isPositiveHornSuperClass(((OWLClassAssertionAxiom) ax).getClassExpression())) return false;
            } else if (ax instanceof OWLDatatypeDefinitionAxiom) {
                return false;
            }
        }
        return true;
    }

    private static boolean hasPureClassAssertionABox(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLObjectPropertyAssertionAxiom
                    || ax instanceof OWLNegativeObjectPropertyAssertionAxiom
                    || ax instanceof OWLDataPropertyAssertionAxiom
                    || ax instanceof OWLNegativeDataPropertyAssertionAxiom
                    || ax instanceof OWLSameIndividualAxiom
                    || ax instanceof OWLDifferentIndividualsAxiom
                    || ax instanceof OWLReflexiveObjectPropertyAxiom
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof SWRLRule) {
                return false;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf || ce instanceof OWLObjectHasValue) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean isNegativeHornSubClass(OWLClassExpression ce) {
        if (!ce.isAnonymous()) return true;
        if (ce instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression op : ((OWLObjectIntersectionOf) ce).getOperands()) {
                if (!isNegativeHornSubClass(op)) return false;
            }
            return true;
        }
        if (ce instanceof OWLObjectSomeValuesFrom) {
            return isNegativeHornSubClass(((OWLObjectSomeValuesFrom) ce).getFiller());
        }
        if (ce instanceof OWLObjectHasValue || ce instanceof OWLObjectHasSelf || ce instanceof OWLDataHasValue) {
            return true;
        }
        if (ce instanceof OWLDataSomeValuesFrom) {
            return ((OWLDataSomeValuesFrom) ce).getFiller() instanceof OWLDatatype;
        }
        return false;
    }

    private static boolean isPositiveHornSuperClass(OWLClassExpression ce) {
        if (!ce.isAnonymous()) return true;
        if (ce instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression op : ((OWLObjectIntersectionOf) ce).getOperands()) {
                if (!isPositiveHornSuperClass(op)) return false;
            }
            return true;
        }
        if (ce instanceof OWLObjectSomeValuesFrom) {
            return isPositiveHornSuperClass(((OWLObjectSomeValuesFrom) ce).getFiller());
        }
        if (ce instanceof OWLObjectAllValuesFrom) {
            return isPositiveHornSuperClass(((OWLObjectAllValuesFrom) ce).getFiller());
        }
        if (ce instanceof OWLObjectComplementOf) {
            return isNegativeHornSubClass(((OWLObjectComplementOf) ce).getOperand());
        }
        if (ce instanceof OWLObjectHasValue || ce instanceof OWLObjectHasSelf || ce instanceof OWLDataHasValue) {
            return true;
        }
        if (ce instanceof OWLDataSomeValuesFrom) {
            return ((OWLDataSomeValuesFrom) ce).getFiller() instanceof OWLDatatype;
        }
        if (ce instanceof OWLDataAllValuesFrom) {
            return ((OWLDataAllValuesFrom) ce).getFiller() instanceof OWLDatatype;
        }
        return false;
    }

    /**
     * Exact guarded reduction for {@code ≥n r.C} ({@code n ≥ 2}) on ontologies with
     * {@code ReflexiveObjectProperty}. Since {@code ≥n r.C ⊑ ∃r.C}, every satisfiable
     * named subclass and every named instance of {@code ≥n r.C} is already a subclass
     * or instance of {@code ∃r.C}. Placing {@code ≥n r.C} only on the right of
     * {@code Q ⊑ ≥n r.C} determines satisfiability and superclasses of {@code ≥n r.C},
     * while guarded probes {@code P_A ⊑ A ⊓ ≤(n−1) r.C} and
     * {@code P_a ⊑ {a} ⊓ ≤(n−1) r.C} test each candidate subclass {@code A} and
     * candidate instance {@code a} of {@code ∃r.C} without introducing an unguarded
     * root equality disjunction across all ABox individuals.
     */
    private ClassAnswer classAnswerForMinCardinality(OWLObjectMinCardinality omc, boolean runWithInstances) {
        OWLClassExpression existCe = df.getOWLObjectSomeValuesFrom(omc.getProperty(), omc.getFiller());
        ClassAnswer someAns = classAnswer(existCe, runWithInstances);
        return reduce(Arrays.asList("class", omc, runWithInstances), CLASSIFYING_EXPRESSION, () -> {
            if (someAns.unsat) {
                ClassAnswer empty = new ClassAnswer();
                empty.unsat = true;
                if (runWithInstances) empty.instances = Collections.emptySet();
                return empty;
            }
            OWLClassExpression negCe = df.getOWLObjectMaxCardinality(
                    omc.getCardinality() - 1, omc.getProperty(), omc.getFiller());
            List<OWLAxiom> defs = new ArrayList<>();
            OWLClass q = df.getOWLClass(fresh().next("Q"));
            String qIri = q.getIRI().toString();
            defs.add(df.getOWLSubClassOfAxiom(q, omc));
            Map<String, Integer> subProbes = new LinkedHashMap<>();
            for (int rep : someAns.subs) {
                OWLClass p = df.getOWLClass(fresh().next("PSub"));
                defs.add(df.getOWLSubClassOfAxiom(p, and(classById[rep], negCe)));
                subProbes.put(p.getIRI().toString(), rep);
            }
            Map<String, OWLNamedIndividual> indProbes = new LinkedHashMap<>();
            if (runWithInstances && someAns.instances != null) {
                for (OWLNamedIndividual ind : someAns.instances) {
                    OWLClass p = df.getOWLClass(fresh().next("PInd"));
                    defs.add(df.getOWLSubClassOfAxiom(p, and(df.getOWLObjectOneOf(ind), negCe)));
                    indProbes.put(p.getIRI().toString(), ind);
                }
            }
            String label = runWithInstances ? "class expression query with instances" : "class expression query";
            ExtendedRun.Answer answer = extendedRun(label, defs, false, false);
            requireConsistent(answer, label);
            ClassAnswer out = new ClassAnswer();
            out.unsat = answer.unsat.contains(qIri);
            int bottom = repId[nothingId];
            if (!out.unsat) {
                Set<Integer> sub = new TreeSet<>();
                for (Map.Entry<String, Integer> e : subProbes.entrySet()) {
                    if (answer.unsat.contains(e.getKey()) && e.getValue() != bottom) {
                        sub.add(e.getValue());
                    }
                }
                out.top = sub.contains(repId[thingId]);
                if (out.top) {
                    for (int c = 0; c < repId.length; c++) {
                        if (repId[c] != bottom) sub.add(repId[c]);
                    }
                }
                Set<Integer> sup = new TreeSet<>();
                sup.add(repId[thingId]);
                for (String iri : answer.supersOf(qIri)) {
                    Integer id = idByIri.get(iri);
                    if (id == null) continue;
                    int r = repId[id];
                    sup.add(r);
                    int[] sups = supersByRep[r];
                    if (sups != null) for (int s : sups) sup.add(s);
                }
                sup.remove(bottom);
                Set<Integer> eq = new TreeSet<>(sup);
                eq.retainAll(sub);
                if (eq.size() > 1) {
                    throw new ReasonerInternalException("Kobayashi-MaRust put a class expression next to "
                            + eq.size() + " different nodes of the class hierarchy; refusing the answer");
                }
                out.supers = toArray(sup);
                out.subs = toArray(sub);
                out.equivalents = toArray(eq);
            }
            if (runWithInstances) {
                out.instances = new LinkedHashSet<>();
                if (!out.unsat) {
                    if (out.top) {
                        out.instances.addAll(signatureIndividuals());
                    } else {
                        for (Map.Entry<String, OWLNamedIndividual> e : indProbes.entrySet()) {
                            if (answer.unsat.contains(e.getKey())) {
                                out.instances.add(e.getValue());
                            }
                        }
                    }
                }
            }
            return out;
        });
    }

    private ClassAnswer classAnswerOnRollup(OWLClassExpression ce) {
        if (ce instanceof OWLObjectOneOf) {
            Set<OWLIndividual> ops = ((OWLObjectOneOf) ce).getIndividuals();
            if (ops.size() == 1 && ops.iterator().next().isNamed()) {
                OWLNamedIndividual target = ops.iterator().next().asOWLNamedIndividual();
                Realized data = ensureRealized();
                ClassAnswer out = new ClassAnswer();
                out.unsat = false;
                out.top = false;
                Integer comp = data.componentOf.get(target);
                out.supers = comp != null ? data.allTypes.get(comp) : new int[]{repId[thingId]};
                out.subs = EMPTY_INTS;
                out.equivalents = EMPTY_INTS;
                out.instances = new LinkedHashSet<>();
                if (signatureIndividuals().contains(target)) out.instances.add(target);
                return out;
            }
        }
        if (ce instanceof OWLObjectHasValue) {
            OWLObjectHasValue ohv = (OWLObjectHasValue) ce;
            if (ohv.getFiller().isNamed()) {
                OWLNamedIndividual target = ohv.getFiller().asOWLNamedIndividual();
                OWLClass eff = activeRollup.effectiveClassOf(target, df);
                OWLClassExpression proxyCe = df.getOWLObjectSomeValuesFrom(
                        ohv.getProperty(), eff != null ? eff : owlThing);
                OWLClass q = df.getOWLClass(fresh().next("Q"));
                ExtendedRun.Answer answer = extendedRun("class expression query",
                        Collections.singletonList(df.getOWLEquivalentClassesAxiom(q, proxyCe)), false, true);
                requireConsistent(answer, "class expression query");
                ClassAnswer out = classAnswerOf(answer, proxyCe, q.getIRI().toString(), false);
                ObjectPropertyModel pm = ensureProperties();
                if (!pm.isUniversal(pm.code(ohv.getProperty()))) {
                    out.top = false;
                    out.subs = EMPTY_INTS;
                    out.equivalents = EMPTY_INTS;
                }
                out.instances = new LinkedHashSet<>();
                if (!out.unsat && signatureIndividuals().contains(target)) {
                    for (OWLNamedIndividual ind : signatureIndividuals()) {
                        if (computeObjectPropertyValues(ind, ohv.getProperty()).containsEntity(target)) {
                            out.instances.add(ind);
                        }
                    }
                }
                return out;
            }
        }
        OWLClass q = df.getOWLClass(fresh().next("Q"));
        ExtendedRun.Answer answer = extendedRun("class expression query",
                Collections.singletonList(df.getOWLEquivalentClassesAxiom(q, ce)), false, true);
        requireConsistent(answer, "class expression query");
        return classAnswerOf(answer, ce, q.getIRI().toString(), true);
    }

    private ClassAnswer classAnswerOf(ExtendedRun.Answer answer, OWLClassExpression ce, String q, boolean instances) {
        ClassAnswer out = new ClassAnswer();
        out.unsat = answer.unsat.contains(q);
        int bottom = repId[nothingId];
        if (!out.unsat) {
            out.top = answer.top.contains(q);
            Set<Integer> sup = new TreeSet<>();
            sup.add(repId[thingId]);
            List<String> above = new ArrayList<>(answer.supersOf(q));
            above.addAll(answer.top);
            for (String iri : above) {
                Integer id = idByIri.get(iri);
                if (id == null) continue;
                int r = repId[id];
                sup.add(r);
                int[] sups = supersByRep[r];
                if (sups != null) for (int s : sups) sup.add(s);
            }
            sup.remove(bottom);
            Set<Integer> sub = new TreeSet<>();
            if (out.top) {
                for (int c = 0; c < repId.length; c++) if (repId[c] != bottom) sub.add(repId[c]);
            } else {
                for (Map.Entry<String, Set<String>> row : answer.supers.entrySet()) {
                    if (!row.getValue().contains(q)) continue;
                    Integer id = idByIri.get(row.getKey());
                    if (id != null && repId[id] != bottom) sub.add(repId[id]);
                }
            }
            Set<Integer> eq = new TreeSet<>(sup);
            eq.retainAll(sub);
            if (eq.size() > 1) {
                throw new ReasonerInternalException("Kobayashi-MaRust put a class expression next to "
                        + eq.size() + " different nodes of the class hierarchy; refusing the answer");
            }
            out.supers = toArray(sup);
            out.subs = toArray(sub);
            out.equivalents = toArray(eq);
        }
        if (instances) {
            out.instances = new LinkedHashSet<>();
            if (!out.unsat) {
                for (OWLNamedIndividual ind : signatureIndividuals()) {
                    if (activeRollup != null) {
                        if (activeRollup.isInstance(ind, ce, q, answer, out.top)) {
                            out.instances.add(ind);
                        }
                    } else if (out.top || answer.hasType(ind.getIRI().toString(), q)) {
                        out.instances.add(ind);
                    }
                }
            }
        }
        return out;
    }

    private static int[] toArray(Collection<Integer> set) {
        int[] out = new int[set.size()];
        int k = 0;
        for (int v : set) out[k++] = v;
        return out;
    }

    private static int[] minus(int[] set, int[] remove) {
        int[] buf = new int[set.length];
        int count = 0;
        for (int v : set) {
            boolean drop = false;
            for (int w : remove) if (v == w) { drop = true; break; }
            if (!drop) buf[count++] = v;
        }
        return Arrays.copyOf(buf, count);
    }

    private Node<OWLClass> equivalentsOfExpression(OWLClassExpression ce) {
        ClassAnswer a = classAnswer(ce, false);
        if (a.unsat) return nodeOfId(repId[nothingId]);
        // HermiT answers an empty node when no named class is equivalent.
        if (a.equivalents.length == 0) return new OWLClassNode();
        return nodeOfId(a.equivalents[0]);
    }

    private NodeSet<OWLClass> supersOfExpression(OWLClassExpression ce, boolean direct) {
        ClassAnswer a = classAnswer(ce, false);
        // An unsatisfiable expression sits where owl:Nothing does.
        if (a.unsat) return getSuperClasses(owlNothing, direct);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        int[] strict = minus(a.supers, a.equivalents);
        for (int r : direct ? minimalIds(strict) : strict) ns.addNode(nodeOfId(r));
        return ns;
    }

    private NodeSet<OWLClass> subsOfExpression(OWLClassExpression ce, boolean direct) {
        ClassAnswer a = classAnswer(ce, false);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (a.unsat) return ns;
        Node<OWLClass> bottom = nodeOfId(repId[nothingId]);
        int[] strict = minus(a.subs, a.equivalents);
        if (strict.length == 0) {
            ns.addNode(bottom);
        } else if (!direct) {
            for (int r : strict) ns.addNode(nodeOfId(r));
            ns.addNode(bottom);
        } else {
            for (int r : maximalIds(strict, ensureSubsByRep())) ns.addNode(nodeOfId(r));
        }
        return ns;
    }

    /**
     * The instances of an anonymous expression. Direct instances are those with
     * no type strictly below the expression (the OWL API definition; HermiT
     * agrees on the test ontologies).
     */
    private NodeSet<OWLNamedIndividual> instancesOfExpression(OWLClassExpression ce, boolean direct) {
        ClassAnswer a = classAnswer(ce, true);
        List<OWLNamedIndividual> members = new ArrayList<>(a.instances);
        if (direct && !members.isEmpty()) {
            Realized data = ensureRealized();
            int[] strict = minus(a.subs, a.equivalents);
            Iterator<OWLNamedIndividual> it = members.iterator();
            while (it.hasNext()) {
                Integer c = data.componentOf.get(it.next());
                if (c == null) continue;
                boolean below = false;
                for (int t : data.allTypes.get(c)) {
                    for (int s : strict) if (s == t) { below = true; break; }
                    if (below) break;
                }
                if (below) it.remove();
            }
        }
        return individualNodes(members);
    }

    /** Nodes of individuals under the configured policy (as getInstances of a named class). */
    private NodeSet<OWLNamedIndividual> individualNodes(Collection<OWLNamedIndividual> individuals) {
        OWLNamedIndividualNodeSet ns = new OWLNamedIndividualNodeSet();
        if (individuals.isEmpty()) return ns;
        if (getIndividualNodeSetPolicy() == IndividualNodeSetPolicy.BY_SAME_AS) {
            Realized data = ensureRealized();
            Set<Integer> seen = new HashSet<>();
            for (OWLNamedIndividual ind : individuals) {
                Integer c = data.componentOf.get(ind);
                if (c == null) {
                    ns.addNode(new OWLNamedIndividualNode(ind));
                } else if (seen.add(c)) {
                    ns.addNode(new OWLNamedIndividualNode(data.members.get(c)));
                }
            }
        } else {
            for (OWLNamedIndividual ind : individuals) ns.addNode(new OWLNamedIndividualNode(ind));
        }
        return ns;
    }

    /**
     * Classes disjoint with CE. When CE is {@code ¬A} for a named class {@code A}
     * in the signature, {@code D ⊓ ¬A} is unsatisfiable iff {@code D ⊑ A}, which
     * the taxonomy answers directly without a native run. Otherwise, one run
     * defines {@code Q ⊑ CE} and {@code X_r ⊑ C_r ⊓ Q} for each non-bottom class
     * representative {@code r}, keeping {@code CE} in positive polarity so
     * existential fillers and nominal unions do not introduce unguarded root
     * disjunctions.
     */
    private NodeSet<OWLClass> disjointClassesOf(OWLClassExpression ce) {
        recordReduction("R19_disjoint_classes_probes");
        Node<OWLClass> bottom = nodeOfId(repId[nothingId]);
        if (ce instanceof OWLObjectComplementOf) {
            OWLClassExpression inner = ((OWLObjectComplementOf) ce).getOperand();
            if (!inner.isAnonymous() && !isFresh(inner)) {
                OWLClassNodeSet ns = new OWLClassNodeSet();
                int r = repIdOf(inner);
                if (r == repId[nothingId]) {
                    ns.addNode(bottom);
                    return ns;
                }
                ns.addNode(nodeOfId(r));
                for (Node<OWLClass> sub : getSubClasses(inner, false).getNodes()) {
                    ns.addNode(sub);
                }
                return ns;
            }
        }
        Object known = peek(Arrays.asList("class", ce, true));
        if (known == null) known = peek(Arrays.asList("class", ce, false));
        if (known != null) {
            ClassAnswer a = (ClassAnswer) known;
            if (a.unsat) {
                OWLClassNodeSet ns = new OWLClassNodeSet();
                for (int s : nonBottomReps()) ns.addNode(nodeOfId(s));
                ns.addNode(bottom);
                return ns;
            }
            if (a.top) {
                OWLClassNodeSet ns = new OWLClassNodeSet();
                ns.addNode(bottom);
                return ns;
            }
        }
        List<Integer> reps = reduce(Arrays.asList("disjoint-classes", ce), CLASSIFYING_EXPRESSION, () -> {
            List<OWLAxiom> defs = new ArrayList<>();
            OWLClass q = df.getOWLClass(fresh().next("Q"));
            defs.add(df.getOWLSubClassOfAxiom(q, ce));
            String qIri = q.getIRI().toString();
            Map<String, Integer> byProbe = new HashMap<>();
            int thingRep = repId[thingId];
            int[] candidates = nonBottomReps();
            for (int r : candidates) {
                if (r == thingRep) continue;
                OWLClass x = df.getOWLClass(fresh().next("X"));
                defs.add(df.getOWLSubClassOfAxiom(x, and(classById[r], q)));
                byProbe.put(x.getIRI().toString(), r);
            }
            ExtendedRun.Answer answer = extendedRun("disjoint classes query", defs, false, false);
            requireConsistent(answer, "disjoint classes query");
            List<Integer> found = new ArrayList<>();
            if (answer.unsat.contains(qIri)) {
                for (int r : candidates) found.add(r);
                return found;
            }
            for (Map.Entry<String, Integer> e : byProbe.entrySet()) {
                if (answer.unsat.contains(e.getKey())) found.add(e.getValue());
            }
            return found;
        });
        OWLClassNodeSet ns = new OWLClassNodeSet();
        for (int r : reps) ns.addNode(nodeOfId(r));
        ns.addNode(bottom);
        return ns;
    }

    // ---- entailment ----------------------------------------------------------------

    private OWLClassExpression not(OWLClassExpression ce) { return df.getOWLObjectComplementOf(ce); }

    private OWLClassExpression and(OWLClassExpression a, OWLClassExpression b) {
        return df.getOWLObjectIntersectionOf(a, b);
    }

    /**
     * Whether every expression is unsatisfiable, from one run that defines a fresh
     * {@code Q_i ⊑ CE_i} for each expression not yet known. Exact: {@code Q_i} is
     * fresh, so {@code O ∪ {Q_i ⊑ CE_i} ⊨ Q_i ⊑ ⊥} iff {@code O ⊨ CE_i ⊑ ⊥}.
     */
    private boolean allUnsatisfiable(List<OWLClassExpression> ces) {
        List<OWLClassExpression> missing = new ArrayList<>();
        boolean all = true;
        for (OWLClassExpression ce : ces) {
            Object known = peek(Arrays.asList("class", ce, true));
            if (known == null) known = peek(Arrays.asList("class", ce, false));
            if (known != null) {
                if (!((ClassAnswer) known).unsat) all = false;
                continue;
            }
            Object held = reductions.get(Arrays.asList("unsat", ce));
            if (held instanceof RuntimeException) throw (RuntimeException) held;
            if (held != null) {
                if (!(Boolean) held) all = false;
                continue;
            }
            if (!missing.contains(ce)) missing.add(ce);
        }
        if (missing.isEmpty()) return all;
        try {
            runTask(CHECKING_ENTAILMENT, () -> {
                List<OWLAxiom> defs = new ArrayList<>();
                List<String> names = new ArrayList<>();
                for (OWLClassExpression ce : missing) {
                    OWLClass q = df.getOWLClass(fresh().next("Q"));
                    defs.add(df.getOWLSubClassOfAxiom(q, ce));
                    names.add(q.getIRI().toString());
                }
                ExtendedRun.Answer answer = extendedRun("satisfiability check", defs, false, false);
                requireConsistent(answer, "satisfiability check");
                for (int i = 0; i < missing.size(); i++) {
                    reductions.put(Arrays.asList("unsat", missing.get(i)), answer.unsat.contains(names.get(i)));
                }
            });
        } catch (RuntimeException failure) {
            if (cacheable(failure)) {
                for (OWLClassExpression ce : missing) reductions.put(Arrays.asList("unsat", ce), failure);
            }
            throw failure;
        }
        for (OWLClassExpression ce : missing) {
            if (!(Boolean) reductions.get(Arrays.asList("unsat", ce))) all = false;
        }
        return all;
    }

    private boolean unsatisfiable(OWLClassExpression ce) {
        return allUnsatisfiable(Collections.singletonList(ce));
    }

    /** Whether O ∪ {@code extra} is consistent (one run; the caller caches by axiom). */
    private boolean consistentWith(List<OWLAxiom> extra) {
        if (extra.isEmpty()) return true; // O itself is consistent (checked before)
        return extendedRun("consistency check", extra, false, false).consistent;
    }

    private OWLNamedIndividual freshIndividual() {
        return df.getOWLNamedIndividual(fresh().next("x"));
    }

    private static boolean isTop(OWLPropertyExpression pe) {
        return pe.isOWLTopObjectProperty() || pe.isOWLTopDataProperty();
    }

    private static boolean isBottom(OWLPropertyExpression pe) {
        return pe.isOWLBottomObjectProperty() || pe.isOWLBottomDataProperty();
    }

    /**
     * {@code pe(s, o)} as an assertion or negative assertion on a named property
     * (an inverse swaps the arguments).
     */
    private OWLAxiom assertion(OWLObjectPropertyExpression pe, OWLIndividual s, OWLIndividual o, boolean negative) {
        OWLObjectPropertyExpression simple = pe.getSimplified();
        if (simple.isAnonymous()) {
            OWLIndividual t = s; s = o; o = t;
            simple = simple.getNamedProperty();
        }
        return negative
                ? df.getOWLNegativeObjectPropertyAssertionAxiom(simple, s, o)
                : df.getOWLObjectPropertyAssertionAxiom(simple, s, o);
    }

    private static void requireNamed(OWLIndividual ind, OWLAxiom axiom) {
        if (ind.isAnonymous()) throw new UnsupportedEntailmentTypeException(axiom);
    }

    private boolean preferTBoxPropertyReductions() {
        return activeRollup != null
                || signatureIndividuals().isEmpty()
                || !querySnapshot().getAxioms(AxiomType.SWRL_RULE).isEmpty();
    }

    private boolean preferTBoxChainReduction() {
        return activeRollup != null
                || signatureIndividuals().isEmpty()
                || !querySnapshot().getAxioms(AxiomType.SWRL_RULE).isEmpty();
    }

    /**
     * Whether {@code q} is unsatisfiable in O ∪ {@code defs} (one classification
     * run without introducing named individuals).
     */
    private boolean unsatisfiableWithDefs(String task, OWLClass q, List<OWLAxiom> defs) {
        ExtendedRun.Answer answer = extendedRun(task, defs, false, false);
        requireConsistent(answer, task);
        return answer.unsat.contains(q.getIRI().toString());
    }

    /**
     * {@code r1 ∘ ... ∘ rn ⊑ s} iff {@code ∃r1.(...∃rn.A) ⊓ ¬∃s.A} is
     * unsatisfiable for a fresh class A (or O ∪ {r1(x0,x1), ..., ¬s(x0,xn)}
     * is inconsistent for fresh x0..xn when {@code owl:topObjectProperty} occurs).
     */
    private boolean chainEntailed(List<OWLObjectPropertyExpression> chain, OWLObjectPropertyExpression sup) {
        if (isTop(sup)) return true;
        for (OWLObjectPropertyExpression r : chain) if (isBottom(r)) return true;
        if (chain.size() == 1) return ensureProperties().entails(chain.get(0), sup);
        boolean hasTop = false;
        for (OWLObjectPropertyExpression r : chain) if (isTop(r)) hasTop = true;
        if (!hasTop && !isBottom(sup) && preferTBoxChainReduction()) {
            OWLClass a = df.getOWLClass(fresh().next("A"));
            OWLClassExpression lhs = a;
            for (int i = chain.size() - 1; i >= 0; i--) {
                lhs = df.getOWLObjectSomeValuesFrom(chain.get(i), lhs);
            }
            OWLClass q = df.getOWLClass(fresh().next("Q"));
            return unsatisfiableWithDefs("chain entailment check", q, Arrays.asList(
                    df.getOWLDeclarationAxiom(a),
                    df.getOWLDeclarationAxiom(q),
                    df.getOWLSubClassOfAxiom(q, and(lhs, not(df.getOWLObjectSomeValuesFrom(sup, a))))));
        }
        List<OWLNamedIndividual> xs = new ArrayList<>();
        for (int i = 0; i <= chain.size(); i++) xs.add(freshIndividual());
        List<OWLAxiom> extra = new ArrayList<>();
        for (int i = 0; i < chain.size(); i++) {
            if (!isTop(chain.get(i))) extra.add(assertion(chain.get(i), xs.get(i), xs.get(i + 1), false));
        }
        if (!isBottom(sup)) extra.add(assertion(sup, xs.get(0), xs.get(chain.size()), true));
        return !consistentWith(extra);
    }

    /**
     * Whether O ∪ {@code assertions} entails {@code ce(x)}: one realization with
     * the fresh {@code V ≡ ce}. An inconsistent extension entails everything.
     */
    private boolean typeEntailed(List<OWLAxiom> assertions, OWLNamedIndividual x, OWLClassExpression ce) {
        OWLClass v = df.getOWLClass(fresh().next("V"));
        List<OWLAxiom> extra = new ArrayList<>(assertions);
        extra.add(df.getOWLDeclarationAxiom(x));
        extra.add(df.getOWLEquivalentClassesAxiom(v, ce));
        ExtendedRun.Answer answer = extendedRun("entailment check", extra, true, false);
        return !answer.consistent || answer.hasType(x.getIRI().toString(), v.getIRI().toString());
    }

    /**
     * r and s are disjoint iff {@code ∃pf.⊤} is unsatisfiable under fresh
     * {@code pf ⊑ r, pf ⊑ s} (or O ∪ {r(x,y), s(x,y)} is inconsistent for fresh x, y).
     */
    private boolean propertiesDisjoint(OWLObjectPropertyExpression r, OWLObjectPropertyExpression s) {
        if (isBottom(r) || isBottom(s)) return true;
        ObjectPropertyModel pm = propertyModel;
        if (pm != null) {
            int cr = pm.code(r), cs = pm.code(s);
            if (pm.isEmpty(cr) || pm.isEmpty(cs)) return true;
            if (pm.entails(r, s) || pm.entails(s, r)) return false;
            if (areDomainsOrRangesStatedDisjoint(pm, cr, cs)) return true;
        }
        if (!isTop(r) && !isTop(s) && preferTBoxPropertyReductions()) {
            OWLObjectProperty pf = df.getOWLObjectProperty(fresh().next("pf"));
            OWLClass q = df.getOWLClass(fresh().next("Q"));
            return unsatisfiableWithDefs("disjoint properties check", q, Arrays.asList(
                    df.getOWLDeclarationAxiom(pf),
                    df.getOWLDeclarationAxiom(q),
                    df.getOWLSubObjectPropertyOfAxiom(pf, r),
                    df.getOWLSubObjectPropertyOfAxiom(pf, s),
                    df.getOWLSubClassOfAxiom(q, df.getOWLObjectSomeValuesFrom(pf, owlThing))));
        }
        OWLNamedIndividual x = freshIndividual(), y = freshIndividual();
        List<OWLAxiom> extra = new ArrayList<>();
        if (!isTop(r)) extra.add(assertion(r, x, y, false));
        if (!isTop(s)) extra.add(assertion(s, x, y, false));
        return !consistentWith(extra);
    }

    private boolean areStatedDisjointReps(int repA, int repB) {
        if (repA < 0 || repB < 0) return false;
        int bottom = repId[nothingId];
        if (repA == bottom || repB == bottom) return true;
        if (repA == repB) return false;
        Set<Integer> supsA = new HashSet<>();
        supsA.add(repA);
        if (supersByRep[repA] != null) for (int s : supersByRep[repA]) supsA.add(s);
        Set<Integer> supsB = new HashSet<>();
        supsB.add(repB);
        if (supersByRep[repB] != null) for (int s : supersByRep[repB]) supsB.add(s);
        for (OWLAxiom ax : querySnapshot().getAxioms(AxiomType.DISJOINT_CLASSES)) {
            List<OWLClassExpression> ops = new ArrayList<>(((OWLDisjointClassesAxiom) ax).getClassExpressions());
            for (int i = 0; i < ops.size(); i++) {
                if (ops.get(i).isAnonymous()) continue;
                int ri = repIdOf(ops.get(i));
                if (ri < 0) continue;
                for (int j = i + 1; j < ops.size(); j++) {
                    if (ops.get(j).isAnonymous()) continue;
                    int rj = repIdOf(ops.get(j));
                    if (rj < 0) continue;
                    if ((supsA.contains(ri) && supsB.contains(rj))
                            || (supsA.contains(rj) && supsB.contains(ri))) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private boolean haveSatisfiableCommonSubRep(int repA, int repB) {
        if (repA < 0 || repB < 0) return false;
        int bottom = repId[nothingId];
        if (repA == bottom || repB == bottom) return false;
        if (repA == repB) return true;
        if (supersByRep[repA] != null && Arrays.binarySearch(supersByRep[repA], repB) >= 0) return true;
        if (supersByRep[repB] != null && Arrays.binarySearch(supersByRep[repB], repA) >= 0) return true;
        int[][] subs = ensureSubsByRep();
        int[] sa = subs[repA], sb = subs[repB];
        if (sa == null || sb == null || sa.length == 0 || sb.length == 0) return false;
        for (int x : sa) {
            if (x != bottom && Arrays.binarySearch(sb, x) >= 0) return true;
        }
        return false;
    }

    private boolean areDomainsOrRangesStatedDisjoint(ObjectPropertyModel pm, int codeA, int codeB) {
        int[] domA = domainReps(pm, codeA);
        int[] domB = domainReps(pm, codeB);
        for (int a : domA) {
            for (int b : domB) {
                if (areStatedDisjointReps(a, b)) return true;
            }
        }
        int[] rngA = domainReps(pm, ObjectPropertyModel.inverse(codeA));
        int[] rngB = domainReps(pm, ObjectPropertyModel.inverse(codeB));
        for (int a : rngA) {
            for (int b : rngB) {
                if (areStatedDisjointReps(a, b)) return true;
            }
        }
        return false;
    }

    /**
     * The reduction of each logical axiom type (protege/README.md, table
     * "isEntailed"). Unsatisfiability checks use fresh definitions; the
     * assertion and property-characteristic checks refute the axiom with
     * fresh individuals. Universal and empty properties are decided from their
     * fixed semantics.
     */
    private boolean entailedByReduction(OWLAxiom ax) {
        if (ax instanceof OWLSubClassOfAxiom
                || ax instanceof OWLEquivalentClassesAxiom
                || ax instanceof OWLDisjointClassesAxiom
                || ax instanceof OWLDisjointUnionAxiom) {
            recordReduction("R21_entailment_subsumption_disjointness");
        } else if (ax instanceof OWLObjectPropertyDomainAxiom
                || ax instanceof OWLObjectPropertyRangeAxiom
                || ax instanceof OWLDataPropertyDomainAxiom
                || ax instanceof OWLDataPropertyRangeAxiom) {
            recordReduction("R22_entailment_property_domain_range");
        } else if (ax instanceof OWLObjectPropertyCharacteristicAxiom
                || ax instanceof OWLSubObjectPropertyOfAxiom
                || ax instanceof OWLEquivalentObjectPropertiesAxiom
                || ax instanceof OWLInverseObjectPropertiesAxiom
                || ax instanceof OWLDisjointObjectPropertiesAxiom
                || ax instanceof OWLSubPropertyChainOfAxiom
                || ax instanceof OWLFunctionalDataPropertyAxiom
                || ax instanceof OWLSubDataPropertyOfAxiom
                || ax instanceof OWLEquivalentDataPropertiesAxiom
                || ax instanceof OWLDisjointDataPropertiesAxiom) {
            recordReduction("R23_entailment_rbox_characteristics");
        } else if (ax instanceof OWLIndividualAxiom) {
            recordReduction("R24_entailment_abox_assertions");
        } else if (ax instanceof OWLHasKeyAxiom
                || ax instanceof SWRLRule
                || ax instanceof OWLDatatypeDefinitionAxiom) {
            recordReduction("R25_entailment_haskey_swrl");
        }
        if (ax instanceof OWLSubClassOfAxiom) {
            // C ⊑ D iff C ⊓ ¬D is unsatisfiable.
            OWLSubClassOfAxiom a = (OWLSubClassOfAxiom) ax;
            return unsatisfiable(and(a.getSubClass(), not(a.getSuperClass())));
        }
        if (ax instanceof OWLEquivalentClassesAxiom) {
            // Every operand below and above the first one.
            List<OWLClassExpression> ops = new ArrayList<>(((OWLEquivalentClassesAxiom) ax).getClassExpressions());
            List<OWLClassExpression> checks = new ArrayList<>();
            for (int i = 1; i < ops.size(); i++) {
                checks.add(and(ops.get(0), not(ops.get(i))));
                checks.add(and(ops.get(i), not(ops.get(0))));
            }
            return allUnsatisfiable(checks);
        }
        if (ax instanceof OWLDisjointClassesAxiom) {
            // Pairwise: C ⊓ D is unsatisfiable.
            List<OWLClassExpression> ops = new ArrayList<>(((OWLDisjointClassesAxiom) ax).getClassExpressions());
            List<OWLClassExpression> checks = new ArrayList<>();
            for (int i = 0; i < ops.size(); i++) {
                for (int j = i + 1; j < ops.size(); j++) {
                    OWLClassExpression ci = ops.get(i), cj = ops.get(j);
                    if (!ci.isAnonymous() && !cj.isAnonymous()) {
                        int ri = repIdOf(ci), rj = repIdOf(cj);
                        if (ri == repId[nothingId] || rj == repId[nothingId]) continue;
                        if (ri < 0 || rj < 0) return false;
                        if (haveSatisfiableCommonSubRep(ri, rj)) return false;
                        if (areStatedDisjointReps(ri, rj)) continue;
                    }
                    checks.add(and(ci, cj));
                }
            }
            return checks.isEmpty() || allUnsatisfiable(checks);
        }
        if (ax instanceof OWLDisjointUnionAxiom) {
            OWLDisjointUnionAxiom a = (OWLDisjointUnionAxiom) ax;
            return entailedByReduction(a.getOWLDisjointClassesAxiom())
                    && entailedByReduction(a.getOWLEquivalentClassesAxiom());
        }
        if (ax instanceof OWLClassAssertionAxiom) {
            // C(a) iff a is an instance of the fresh Q ≡ C (the class expression query).
            OWLClassAssertionAxiom a = (OWLClassAssertionAxiom) ax;
            requireNamed(a.getIndividual(), ax);
            OWLNamedIndividual ind = a.getIndividual().asOWLNamedIndividual();
            if (signatureIndividuals().contains(ind)) {
                return classAnswer(a.getClassExpression(), true).instances.contains(ind);
            }
            return typeEntailed(Collections.<OWLAxiom>emptyList(), ind, a.getClassExpression());
        }
        if (ax instanceof OWLObjectPropertyAssertionAxiom || ax instanceof OWLNegativeObjectPropertyAssertionAxiom) {
            // r(a,b) iff a is an instance of ∃r.{b} (the property value query);
            // ¬r(a,b) iff O ∪ {r(a,b)} is inconsistent.
            boolean negative = ax instanceof OWLNegativeObjectPropertyAssertionAxiom;
            OWLPropertyAssertionAxiom<?, ?> a = (OWLPropertyAssertionAxiom<?, ?>) ax;
            OWLObjectPropertyExpression r = (OWLObjectPropertyExpression) a.getProperty();
            requireNamed(a.getSubject(), ax);
            requireNamed((OWLIndividual) a.getObject(), ax);
            if (isTop(r)) return !negative;
            if (isBottom(r)) return negative;
            OWLNamedIndividual s = a.getSubject().asOWLNamedIndividual();
            OWLNamedIndividual o = ((OWLIndividual) a.getObject()).asOWLNamedIndividual();
            Set<OWLNamedIndividual> inds = signatureIndividuals();
            if (negative) {
                if (inds.contains(s) && inds.contains(o)
                        && querySnapshot().containsObjectPropertyInSignature(r.getNamedProperty().getIRI())
                        && computeObjectPropertyValues(s, r).containsEntity(o)) {
                    return false;
                }
                if (activeRollup != null) {
                    ObjectPropertyModel pm = ensureProperties();
                    int code = pm.code(r);
                    if (pm.isEmpty(code)) return true;
                    if (pm.isUniversal(code)) return false;
                    OWLClass cs = activeRollup.effectiveClassOf(s, df);
                    OWLClass co = activeRollup.effectiveClassOf(o, df);
                    if (s.equals(o) || getSameIndividuals(s).contains(o)) {
                        if (areDomainsOrRangesStatedDisjoint(pm, code, ObjectPropertyModel.inverse(code))) {
                            return true;
                        }
                        OWLObjectProperty pf = df.getOWLObjectProperty(fresh().next("pf"));
                        OWLClass q = df.getOWLClass(fresh().next("Q"));
                        return unsatisfiableWithDefs("self negative assertion check", q, Arrays.asList(
                                df.getOWLDeclarationAxiom(pf),
                                df.getOWLDeclarationAxiom(q),
                                df.getOWLSubObjectPropertyOfAxiom(pf, r),
                                df.getOWLSubClassOfAxiom(q,
                                        and(cs != null ? cs : owlThing, df.getOWLObjectHasSelf(pf)))));
                    }
                    OWLClassExpression probe = and(cs != null ? cs : owlThing,
                            df.getOWLObjectSomeValuesFrom(r, co != null ? co : owlThing));
                    return unsatisfiable(probe);
                }
                return !consistentWith(Collections.singletonList(assertion(r, s, o, false)));
            }
            if (inds.contains(s) && inds.contains(o)
                    && querySnapshot().containsObjectPropertyInSignature(r.getNamedProperty().getIRI())) {
                return computeObjectPropertyValues(s, r).containsEntity(o);
            }
            return typeEntailed(Collections.<OWLAxiom>emptyList(), s, df.getOWLObjectHasValue(r, o));
        }
        if (ax instanceof OWLDataPropertyAssertionAxiom || ax instanceof OWLNegativeDataPropertyAssertionAxiom) {
            boolean negative = ax instanceof OWLNegativeDataPropertyAssertionAxiom;
            OWLPropertyAssertionAxiom<?, ?> a = (OWLPropertyAssertionAxiom<?, ?>) ax;
            OWLDataPropertyExpression p = (OWLDataPropertyExpression) a.getProperty();
            OWLLiteral value = (OWLLiteral) a.getObject();
            requireNamed(a.getSubject(), ax);
            if (isTop(p)) return !negative;
            if (isBottom(p)) return negative;
            for (OWLAxiom asserted : querySnapshot().getAxioms(AxiomType.DATA_PROPERTY_RANGE)) {
                OWLDataPropertyRangeAxiom rng = (OWLDataPropertyRangeAxiom) asserted;
                if (rng.getProperty().equals(p) && DataValues.definitelyOutside(value, rng.getRange())) {
                    return negative;
                }
            }
            if (!negative) {
                DataValues.Candidates candidates = reduce(Arrays.asList("literals"), COMPUTING_VALUES,
                        () -> DataValues.collect(querySnapshot(), df));
                if (candidates.outside == null && !candidates.byValue.containsKey(DataValues.valueKey(value))) {
                    return false;
                }
            }
            // p(a,l) iff a is an instance of DataHasValue(p l); ¬p(a,l) iff
            // O ∪ {p(a,l)} is inconsistent.
            if (negative) {
                if (activeRollup != null && a.getSubject().isNamed()) {
                    OWLNamedIndividual subj = a.getSubject().asOWLNamedIndividual();
                    OWLDataProperty dp = p.asOWLDataProperty();
                    Set<OWLLiteral> held = computeDataPropertyValues(subj, dp);
                    Object targetKey = DataValues.valueKey(value);
                    for (OWLLiteral l : held) {
                        if (targetKey.equals(DataValues.valueKey(l))) return false;
                    }
                    if (!held.isEmpty() && activeRollup.functionalDataProperties.contains(dp)) {
                        return true;
                    }
                    if (!activeRollup.tboxDataProperties.contains(dp)) {
                        return false;
                    }
                    OWLClass cs = activeRollup.effectiveClassOf(subj, df);
                    return unsatisfiable(and(cs != null ? cs : owlThing, df.getOWLDataHasValue(p, value)));
                }
                return !consistentWith(Collections.<OWLAxiom>singletonList(
                        df.getOWLDataPropertyAssertionAxiom(p, a.getSubject(), value)));
            }
            if (a.getSubject().isNamed() && !p.isAnonymous()
                    && signatureIndividuals().contains(a.getSubject().asOWLNamedIndividual())
                    && (activeRollup != null || peek(Collections.singletonList("all-data-values")) != null)) {
                Set<OWLLiteral> held = computeDataPropertyValues(
                        a.getSubject().asOWLNamedIndividual(), p.asOWLDataProperty());
                Object targetKey = DataValues.valueKey(value);
                for (OWLLiteral l : held) {
                    if (targetKey.equals(DataValues.valueKey(l))) return true;
                }
                return false;
            }
            return typeEntailed(Collections.<OWLAxiom>emptyList(), a.getSubject().asOWLNamedIndividual(),
                    df.getOWLDataHasValue(p, value));
        }
        if (ax instanceof OWLDifferentIndividualsAxiom) {
            // a ≠ b iff O ∪ {a = b} is inconsistent, pairwise.
            List<OWLIndividual> inds = new ArrayList<>(((OWLDifferentIndividualsAxiom) ax).getIndividuals());
            for (OWLIndividual i : inds) requireNamed(i, ax);
            if (activeRollup != null) {
                for (int i = 0; i < inds.size(); i++) {
                    OWLNamedIndividual ni = inds.get(i).asOWLNamedIndividual();
                    NodeSet<OWLNamedIndividual> diff = computeDifferentIndividuals(ni);
                    for (int j = i + 1; j < inds.size(); j++) {
                        if (!diff.containsEntity(inds.get(j).asOWLNamedIndividual())) return false;
                    }
                }
                return true;
            }
            for (int i = 0; i < inds.size(); i++) {
                OWLNamedIndividual ni = inds.get(i).asOWLNamedIndividual();
                Object cachedI = peek(Arrays.asList("different", ni));
                for (int j = i + 1; j < inds.size(); j++) {
                    OWLNamedIndividual nj = inds.get(j).asOWLNamedIndividual();
                    if (cachedI != null) {
                        @SuppressWarnings("unchecked")
                        List<OWLNamedIndividual> diffI = (List<OWLNamedIndividual>) cachedI;
                        if (!diffI.contains(nj)) return false;
                        continue;
                    }
                    Object cachedJ = peek(Arrays.asList("different", nj));
                    if (cachedJ != null) {
                        @SuppressWarnings("unchecked")
                        List<OWLNamedIndividual> diffJ = (List<OWLNamedIndividual>) cachedJ;
                        if (!diffJ.contains(ni)) return false;
                        continue;
                    }
                    if (consistentWith(Collections.<OWLAxiom>singletonList(
                            df.getOWLSameIndividualAxiom(ni, nj)))) return false;
                }
            }
            return true;
        }
        if (ax instanceof OWLSubPropertyChainOfAxiom) {
            OWLSubPropertyChainOfAxiom a = (OWLSubPropertyChainOfAxiom) ax;
            return chainEntailed(new ArrayList<>(a.getPropertyChain()), a.getSuperProperty());
        }
        if (ax instanceof OWLTransitiveObjectPropertyAxiom) {
            OWLObjectPropertyExpression r = ((OWLTransitiveObjectPropertyAxiom) ax).getProperty();
            return chainEntailed(Arrays.asList(r, r), r);
        }
        if (ax instanceof OWLDisjointObjectPropertiesAxiom) {
            List<OWLObjectPropertyExpression> ps = new ArrayList<>(((OWLDisjointObjectPropertiesAxiom) ax).getProperties());
            for (int i = 0; i < ps.size(); i++) {
                for (int j = i + 1; j < ps.size(); j++) {
                    if (!propertiesDisjoint(ps.get(i), ps.get(j))) return false;
                }
            }
            return true;
        }
        if (ax instanceof OWLObjectPropertyDomainAxiom) {
            // Domain C iff ∃r.⊤ ⊓ ¬C is unsatisfiable (∃U.⊤ is ⊤).
            OWLObjectPropertyDomainAxiom a = (OWLObjectPropertyDomainAxiom) ax;
            if (isBottom(a.getProperty())) return true;
            if (isTop(a.getProperty())) return unsatisfiable(not(a.getDomain()));
            return unsatisfiable(and(df.getOWLObjectSomeValuesFrom(a.getProperty(), owlThing), not(a.getDomain())));
        }
        if (ax instanceof OWLObjectPropertyRangeAxiom) {
            // Range C iff ∃r.¬C is unsatisfiable.
            OWLObjectPropertyRangeAxiom a = (OWLObjectPropertyRangeAxiom) ax;
            if (isBottom(a.getProperty())) return true;
            if (isTop(a.getProperty())) return unsatisfiable(not(a.getRange()));
            return unsatisfiable(df.getOWLObjectSomeValuesFrom(a.getProperty(), not(a.getRange())));
        }
        if (ax instanceof OWLFunctionalObjectPropertyAxiom || ax instanceof OWLInverseFunctionalObjectPropertyAxiom) {
            // Functional iff ≥2 pf.⊤ is unsatisfiable under fresh pf ⊑ r (or
            // O ∪ {r(x,y1), r(x,y2), y1 ≠ y2} is inconsistent for fresh x, y1, y2);
            // inverse functional uses r⁻.
            OWLObjectPropertyExpression r = ((OWLObjectPropertyCharacteristicAxiom) ax).getProperty();
            if (isBottom(r)) return true;
            if (isTop(r)) return universalFunctional();
            if (ax instanceof OWLInverseFunctionalObjectPropertyAxiom) r = r.getInverseProperty().getSimplified();
            if (preferTBoxPropertyReductions()) {
                OWLObjectProperty pf = df.getOWLObjectProperty(fresh().next("pf"));
                OWLClass q = df.getOWLClass(fresh().next("Q"));
                return unsatisfiableWithDefs("functional property check", q, Arrays.asList(
                        df.getOWLDeclarationAxiom(pf),
                        df.getOWLDeclarationAxiom(q),
                        df.getOWLSubObjectPropertyOfAxiom(pf, r),
                        df.getOWLSubClassOfAxiom(q, df.getOWLObjectMinCardinality(2, pf, owlThing))));
            }
            OWLNamedIndividual x = freshIndividual(), y1 = freshIndividual(), y2 = freshIndividual();
            return !consistentWith(Arrays.asList(assertion(r, x, y1, false), assertion(r, x, y2, false),
                    df.getOWLDifferentIndividualsAxiom(y1, y2)));
        }
        if (ax instanceof OWLAsymmetricObjectPropertyAxiom) {
            // Asymmetric iff r and r⁻ are disjoint (O ∪ {r(x,y), r(y,x)} is inconsistent).
            OWLObjectPropertyExpression r = ((OWLAsymmetricObjectPropertyAxiom) ax).getProperty();
            if (isBottom(r)) return true;
            if (isTop(r)) return false;
            if (propertyModel != null || preferTBoxPropertyReductions()) {
                return propertiesDisjoint(r, r.getInverseProperty().getSimplified());
            }
            OWLNamedIndividual x = freshIndividual(), y = freshIndividual();
            return !consistentWith(Arrays.asList(assertion(r, x, y, false), assertion(r, y, x, false)));
        }
        if (ax instanceof OWLReflexiveObjectPropertyAxiom) {
            // Reflexive iff ¬∃r.Self is unsatisfiable (for simple r) or O ∪ {¬r(x,x)}
            // is inconsistent for a fresh individual x.
            OWLObjectPropertyExpression r = ((OWLReflexiveObjectPropertyAxiom) ax).getProperty();
            if (isTop(r)) return true;
            if (isBottom(r)) return false;
            if (activeRollup != null) {
                ObjectPropertyModel pm = ensureProperties();
                int code = pm.code(r);
                if (pm.isEmpty(code)) return false;
                if (pm.isUniversal(code)) return true;
                for (OWLAxiom reflAx : querySnapshot().getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY)) {
                    OWLObjectPropertyExpression reflProp = ((OWLReflexiveObjectPropertyAxiom) reflAx).getProperty();
                    if (pm.entails(reflProp, r)) return true;
                }
                return false;
            }
            ObjectPropertyModel pm = propertyModel;
            if (pm != null) {
                int code = pm.code(r);
                if (pm.isEmpty(code)) return false;
                if (pm.isUniversal(code)) return true;
                for (int rep : domainReps(pm, code)) {
                    if (rep != repId[thingId]) return false;
                }
                for (int rep : domainReps(pm, ObjectPropertyModel.inverse(code))) {
                    if (rep != repId[thingId]) return false;
                }
            }
            if (preferTBoxPropertyReductions()) {
                try {
                    return unsatisfiable(not(df.getOWLObjectHasSelf(r)));
                } catch (RuntimeException nonSimple) {
                    // Fall back when r is non-simple.
                }
            }
            OWLNamedIndividual x = freshIndividual();
            return !consistentWith(Collections.singletonList(assertion(r, x, x, true)));
        }
        if (ax instanceof OWLIrreflexiveObjectPropertyAxiom) {
            // Irreflexive iff ∃pf.Self is unsatisfiable under fresh pf ⊑ r (or
            // O ∪ {r(x,x)} is inconsistent).
            OWLObjectPropertyExpression r = ((OWLIrreflexiveObjectPropertyAxiom) ax).getProperty();
            if (isBottom(r)) return true;
            if (isTop(r)) return false;
            ObjectPropertyModel pm = propertyModel;
            if (pm != null) {
                int code = pm.code(r);
                if (pm.isEmpty(code)) return true;
                if (pm.isUniversal(code)) return false;
                if (areDomainsOrRangesStatedDisjoint(pm, code, ObjectPropertyModel.inverse(code))) return true;
            }
            if (preferTBoxPropertyReductions()) {
                OWLObjectProperty pf = df.getOWLObjectProperty(fresh().next("pf"));
                OWLClass q = df.getOWLClass(fresh().next("Q"));
                return unsatisfiableWithDefs("irreflexive property check", q, Arrays.asList(
                        df.getOWLDeclarationAxiom(pf),
                        df.getOWLDeclarationAxiom(q),
                        df.getOWLSubObjectPropertyOfAxiom(pf, r),
                        df.getOWLSubClassOfAxiom(q, df.getOWLObjectHasSelf(pf))));
            }
            OWLNamedIndividual x = freshIndividual();
            return !consistentWith(Collections.singletonList(assertion(r, x, x, false)));
        }
        if (ax instanceof OWLSubDataPropertyOfAxiom) {
            OWLSubDataPropertyOfAxiom a = (OWLSubDataPropertyOfAxiom) ax;
            return dataSubProperty(a.getSubProperty(), a.getSuperProperty());
        }
        if (ax instanceof OWLEquivalentDataPropertiesAxiom) {
            List<OWLDataPropertyExpression> ps = new ArrayList<>(((OWLEquivalentDataPropertiesAxiom) ax).getProperties());
            for (int i = 1; i < ps.size(); i++) {
                if (!dataSubProperty(ps.get(0), ps.get(i)) || !dataSubProperty(ps.get(i), ps.get(0))) return false;
            }
            return true;
        }
        if (ax instanceof OWLDisjointDataPropertiesAxiom) {
            // Pairwise, from getDisjointDataProperties.
            List<OWLDataPropertyExpression> ps = new ArrayList<>(((OWLDisjointDataPropertiesAxiom) ax).getProperties());
            for (int i = 0; i < ps.size(); i++) {
                for (int j = i + 1; j < ps.size(); j++) {
                    OWLDataProperty a = ps.get(i).asOWLDataProperty(), b = ps.get(j).asOWLDataProperty();
                    if (!getDisjointDataProperties(a).containsEntity(b)) return false;
                }
            }
            return true;
        }
        if (ax instanceof OWLDataPropertyDomainAxiom) {
            // Domain C iff ∃p.rdfs:Literal ⊓ ¬C is unsatisfiable.
            OWLDataPropertyDomainAxiom a = (OWLDataPropertyDomainAxiom) ax;
            if (isBottom(a.getProperty())) return true;
            if (isTop(a.getProperty())) return unsatisfiable(not(a.getDomain()));
            return unsatisfiable(and(df.getOWLDataSomeValuesFrom(a.getProperty(), df.getTopDatatype()),
                    not(a.getDomain())));
        }
        if (ax instanceof OWLDataPropertyRangeAxiom) {
            // Range D iff ∃p.¬D is unsatisfiable. When O already asserts p(a, l)
            // with l outside D, or O ∪ {p(x, w)} is consistent for a fresh x and a
            // witness literal w outside a built-in datatype D, O does not entail
            // the range and no unguarded DataComplementOf(D) disjunction is needed.
            OWLDataPropertyRangeAxiom a = (OWLDataPropertyRangeAxiom) ax;
            if (isBottom(a.getProperty()) || a.getRange().isTopDatatype()) return true;
            if (isTop(a.getProperty())) {
                if (DataValues.witnessOutside(a.getRange(), df) != null) return false;
                throw new UnsupportedEntailmentTypeException(ax);
            }
            OWLDataProperty p = a.getProperty().asOWLDataProperty();
            for (OWLAxiom asserted : querySnapshot().getAxioms(AxiomType.DATA_PROPERTY_RANGE)) {
                OWLDataPropertyRangeAxiom rng = (OWLDataPropertyRangeAxiom) asserted;
                if (!rng.getProperty().equals(p)) continue;
                if (rng.getRange().equals(a.getRange())) return true;
                if (rng.getRange() instanceof OWLDatatype && a.getRange() instanceof OWLDatatype) {
                    IRI rIri = rng.getRange().asOWLDatatype().getIRI();
                    IRI dIri = a.getRange().asOWLDatatype().getIRI();
                    if (!DataPropertyModel.rangesCompatible(new HashSet<>(Arrays.asList(rIri, dIri)))) {
                        return getBottomDataPropertyNode().contains(p);
                    }
                }
            }
            for (OWLAxiom asserted : querySnapshot().getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {
                OWLDataPropertyAssertionAxiom dpa = (OWLDataPropertyAssertionAxiom) asserted;
                if (dpa.getProperty().equals(p) && DataValues.definitelyOutside(dpa.getObject(), a.getRange())) {
                    return false;
                }
            }
            OWLLiteral witness = DataValues.witnessOutside(a.getRange(), df);
            if (witness != null) {
                if (preferTBoxPropertyReductions()) {
                    if (!unsatisfiable(df.getOWLDataHasValue(p, witness))) return false;
                } else {
                    OWLNamedIndividual x = freshIndividual();
                    if (consistentWith(Collections.<OWLAxiom>singletonList(
                            df.getOWLDataPropertyAssertionAxiom(p, x, witness)))) {
                        return false;
                    }
                }
            }
            return unsatisfiable(df.getOWLDataSomeValuesFrom(a.getProperty(), df.getOWLDataComplementOf(a.getRange())));
        }
        if (ax instanceof OWLFunctionalDataPropertyAxiom) {
            // Functional iff ≥2 p.rdfs:Literal is unsatisfiable; the universal data
            // property relates every individual to every one of infinitely many values.
            OWLDataPropertyExpression p = ((OWLFunctionalDataPropertyAxiom) ax).getProperty();
            if (isBottom(p)) return true;
            if (isTop(p)) return false;
            return unsatisfiable(df.getOWLDataMinCardinality(2, p, df.getTopDatatype()));
        }
        if (ax instanceof OWLHasKeyAxiom) {
            return isEntailedHasKey((OWLHasKeyAxiom) ax);
        }
        if (ax instanceof OWLDatatypeDefinitionAxiom) {
            return isEntailedDatatypeDefinition((OWLDatatypeDefinitionAxiom) ax);
        }
        if (ax instanceof SWRLRule) {
            return isEntailedSWRLRule((SWRLRule) ax);
        }
        throw new UnsupportedEntailmentTypeException(ax);
    }

    /**
     * Refutation of {@code HasKey(CE (r1..rm) (p1..pn))} matching HermiT's
     * {@code EntailmentChecker.visit(OWLHasKeyAxiom)}: {@code O ⊨ HasKey} iff
     * {@code O ∪ {CE(a), CE(b), ri(a, zi), ri(b, zi), pj(a, cj), pj(b, cj), a ≠ b}}
     * is inconsistent for fresh named individuals {@code a, b, z1..zm} and
     * fresh free datatype constants {@code c1..cn}.
     */
    private boolean isEntailedHasKey(OWLHasKeyAxiom hk) {
        for (OWLPropertyExpression pe : hk.getPropertyExpressions()) {
            if (isBottom(pe)) return true;
        }
        OWLNamedIndividual a = freshIndividual(), b = freshIndividual();
        List<OWLAxiom> extra = new ArrayList<>();
        extra.add(df.getOWLDeclarationAxiom(a));
        extra.add(df.getOWLDeclarationAxiom(b));
        extra.add(df.getOWLClassAssertionAxiom(hk.getClassExpression(), a));
        extra.add(df.getOWLClassAssertionAxiom(hk.getClassExpression(), b));
        extra.add(df.getOWLDifferentIndividualsAxiom(a, b));
        for (OWLObjectPropertyExpression ope : hk.getObjectPropertyExpressions()) {
            OWLNamedIndividual z = freshIndividual();
            extra.add(df.getOWLDeclarationAxiom(z));
            if (!isTop(ope)) {
                extra.add(assertion(ope, a, z, false));
                extra.add(assertion(ope, b, z, false));
            }
        }
        boolean hasData = !hk.getDataPropertyExpressions().isEmpty();
        for (OWLDataPropertyExpression dpe : hk.getDataPropertyExpressions()) {
            OWLDatatype freeDt = df.getOWLDatatype(fresh().next("keydt"));
            OWLLiteral c = df.getOWLLiteral("v", freeDt);
            if (!isTop(dpe)) {
                extra.add(df.getOWLDataPropertyAssertionAxiom(dpe, a, c));
                extra.add(df.getOWLDataPropertyAssertionAxiom(dpe, b, c));
            }
        }
        try {
            return !extendedRun("has-key entailment check", extra, false, false, hasData).consistent;
        } catch (UnsupportedOperationException e) {
            throw new UnsupportedEntailmentTypeException(hk);
        }
    }

    /**
     * Entailment of {@code DatatypeDefinition(DT, DR)} via a fresh functional
     * data property {@code dp}: {@code O ⊨ DT ≡ DR} iff both
     * {@code Φ_dp(DT) ⊓ ¬Φ_dp(DR)} and {@code Φ_dp(DR) ⊓ ¬Φ_dp(DT)} are
     * unsatisfiable, where {@code Φ_dp} decomposes boolean data ranges into
     * boolean class expressions over top-level {@code DataSomeValuesFrom(dp, ·)}
     * so the frontend's datatype-definition inliner expands {@code DT}.
     */
    private boolean isEntailedDatatypeDefinition(OWLDatatypeDefinitionAxiom dtd) {
        OWLDatatype dt = dtd.getDatatype();
        OWLDataRange dr = dtd.getDataRange();
        if (dt.equals(dr)) return true;
        OWLDataProperty dp = df.getOWLDataProperty(fresh().next("dtp"));
        OWLClass q1 = df.getOWLClass(fresh().next("DTQ1"));
        OWLClass q2 = df.getOWLClass(fresh().next("DTQ2"));
        OWLClassExpression lhs = dataRangeProbe(dp, dt);
        OWLClassExpression rhs = dataRangeProbe(dp, dr);
        List<OWLAxiom> defs = Arrays.asList(
                df.getOWLDeclarationAxiom(dp),
                df.getOWLFunctionalDataPropertyAxiom(dp),
                df.getOWLDeclarationAxiom(q1),
                df.getOWLDeclarationAxiom(q2),
                df.getOWLSubClassOfAxiom(q1, and(lhs, not(rhs))),
                df.getOWLSubClassOfAxiom(q2, and(rhs, not(lhs))));
        try {
            ExtendedRun.Answer ans = extendedRun("datatype definition entailment check", defs, false, false, false);
            requireConsistent(ans, "datatype definition entailment check");
            return ans.unsat.contains(q1.getIRI().toString())
                    && ans.unsat.contains(q2.getIRI().toString());
        } catch (RuntimeException e) {
            if (e instanceof ReasonerInterruptedException || e instanceof TimeOutException) throw e;
            throw new UnsupportedEntailmentTypeException(dtd);
        }
    }

    private OWLClassExpression dataRangeProbe(OWLDataProperty dp, OWLDataRange dr) {
        if (dr instanceof OWLDataComplementOf) {
            OWLDataRange inner = ((OWLDataComplementOf) dr).getDataRange();
            return and(df.getOWLDataSomeValuesFrom(dp, df.getTopDatatype()),
                    not(dataRangeProbe(dp, inner)));
        }
        if (dr instanceof OWLDataIntersectionOf) {
            Set<OWLClassExpression> ops = new LinkedHashSet<>();
            for (OWLDataRange op : ((OWLDataIntersectionOf) dr).getOperands()) {
                ops.add(dataRangeProbe(dp, op));
            }
            return df.getOWLObjectIntersectionOf(ops);
        }
        if (dr instanceof OWLDataUnionOf) {
            Set<OWLClassExpression> ops = new LinkedHashSet<>();
            for (OWLDataRange op : ((OWLDataUnionOf) dr).getOperands()) {
                ops.add(dataRangeProbe(dp, op));
            }
            return df.getOWLObjectUnionOf(ops);
        }
        return df.getOWLDataSomeValuesFrom(dp, dr);
    }

    /**
     * Refutation of a DL-safe {@code SWRLRule(Body -> Head)} without built-in
     * atoms: ground every object variable to a fresh named individual and every
     * data variable to a fresh free constant, assert all body atoms, and check
     * that each head atom's negation makes {@code O ∪ Body} inconsistent. Rules
     * with {@code SWRLBuiltInAtom} (or outside the engine's rule fragment)
     * throw {@link UnsupportedEntailmentTypeException}.
     */
    private boolean isEntailedSWRLRule(SWRLRule rule) {
        for (SWRLAtom atom : rule.getBody()) {
            if (atom instanceof SWRLBuiltInAtom) throw new UnsupportedEntailmentTypeException(rule);
        }
        for (SWRLAtom atom : rule.getHead()) {
            if (atom instanceof SWRLBuiltInAtom) throw new UnsupportedEntailmentTypeException(rule);
        }
        Map<SWRLVariable, OWLNamedIndividual> iVars = new HashMap<>();
        Map<SWRLVariable, OWLLiteral> dVars = new HashMap<>();
        boolean hasDataVars = false;
        for (SWRLAtom atom : rule.getBody()) {
            hasDataVars |= bindSwrlAtomVars(atom, iVars, dVars);
        }
        for (SWRLAtom atom : rule.getHead()) {
            hasDataVars |= bindSwrlAtomVars(atom, iVars, dVars);
        }
        List<OWLAxiom> bodyAxioms = new ArrayList<>();
        for (OWLNamedIndividual ind : iVars.values()) {
            bodyAxioms.add(df.getOWLDeclarationAxiom(ind));
        }
        for (SWRLAtom atom : rule.getBody()) {
            bodyAxioms.addAll(groundSwrlAtomPositive(atom, iVars, dVars, rule));
        }
        try {
            if (rule.getHead().isEmpty()) {
                return !extendedRun("SWRL rule entailment check", bodyAxioms, false, false, hasDataVars).consistent;
            }
            for (SWRLAtom headAtom : rule.getHead()) {
                List<OWLAxiom> check = new ArrayList<>(bodyAxioms);
                check.addAll(groundSwrlAtomNegated(headAtom, iVars, dVars, rule));
                if (extendedRun("SWRL rule entailment check", check, false, false, hasDataVars).consistent) {
                    return false;
                }
            }
            return true;
        } catch (UnsupportedOperationException e) {
            throw new UnsupportedEntailmentTypeException(rule);
        }
    }

    private boolean bindSwrlAtomVars(
            SWRLAtom atom,
            Map<SWRLVariable, OWLNamedIndividual> iVars,
            Map<SWRLVariable, OWLLiteral> dVars) {
        boolean data = false;
        if (atom instanceof SWRLClassAtom) {
            bindSwrlIArg(((SWRLClassAtom) atom).getArgument(), iVars);
        } else if (atom instanceof SWRLObjectPropertyAtom) {
            SWRLObjectPropertyAtom opa = (SWRLObjectPropertyAtom) atom;
            bindSwrlIArg(opa.getFirstArgument(), iVars);
            bindSwrlIArg(opa.getSecondArgument(), iVars);
        } else if (atom instanceof SWRLSameIndividualAtom) {
            SWRLSameIndividualAtom sa = (SWRLSameIndividualAtom) atom;
            bindSwrlIArg(sa.getFirstArgument(), iVars);
            bindSwrlIArg(sa.getSecondArgument(), iVars);
        } else if (atom instanceof SWRLDifferentIndividualsAtom) {
            SWRLDifferentIndividualsAtom da = (SWRLDifferentIndividualsAtom) atom;
            bindSwrlIArg(da.getFirstArgument(), iVars);
            bindSwrlIArg(da.getSecondArgument(), iVars);
        } else if (atom instanceof SWRLDataPropertyAtom) {
            SWRLDataPropertyAtom dpa = (SWRLDataPropertyAtom) atom;
            bindSwrlIArg(dpa.getFirstArgument(), iVars);
            if (bindSwrlDArg(dpa.getSecondArgument(), dVars)) data = true;
        } else if (atom instanceof SWRLDataRangeAtom) {
            if (bindSwrlDArg(((SWRLDataRangeAtom) atom).getArgument(), dVars)) data = true;
        }
        return data;
    }

    private OWLNamedIndividual bindSwrlIArg(
            SWRLIArgument arg, Map<SWRLVariable, OWLNamedIndividual> iVars) {
        if (arg instanceof SWRLVariable) {
            return iVars.computeIfAbsent((SWRLVariable) arg, v -> freshIndividual());
        }
        OWLIndividual ind = ((SWRLIndividualArgument) arg).getIndividual();
        if (ind.isAnonymous()) return null;
        return ind.asOWLNamedIndividual();
    }

    private boolean bindSwrlDArg(
            SWRLDArgument arg, Map<SWRLVariable, OWLLiteral> dVars) {
        if (arg instanceof SWRLVariable) {
            dVars.computeIfAbsent((SWRLVariable) arg,
                    v -> df.getOWLLiteral("v", df.getOWLDatatype(fresh().next("swrldt"))));
            return true;
        }
        return false;
    }

    private OWLLiteral resolveSwrlDArg(
            SWRLDArgument arg, Map<SWRLVariable, OWLLiteral> dVars) {
        if (arg instanceof SWRLVariable) return dVars.get(arg);
        return ((SWRLLiteralArgument) arg).getLiteral();
    }

    private List<OWLAxiom> groundSwrlAtomPositive(
            SWRLAtom atom,
            Map<SWRLVariable, OWLNamedIndividual> iVars,
            Map<SWRLVariable, OWLLiteral> dVars,
            SWRLRule rule) {
        if (atom instanceof SWRLClassAtom) {
            SWRLClassAtom ca = (SWRLClassAtom) atom;
            OWLNamedIndividual ind = bindSwrlIArg(ca.getArgument(), iVars);
            if (ind == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLClassAssertionAxiom(ca.getPredicate(), ind));
        }
        if (atom instanceof SWRLObjectPropertyAtom) {
            SWRLObjectPropertyAtom opa = (SWRLObjectPropertyAtom) atom;
            OWLNamedIndividual s = bindSwrlIArg(opa.getFirstArgument(), iVars);
            OWLNamedIndividual o = bindSwrlIArg(opa.getSecondArgument(), iVars);
            if (s == null || o == null) throw new UnsupportedEntailmentTypeException(rule);
            if (isTop(opa.getPredicate())) return Collections.emptyList();
            return Collections.singletonList(assertion(opa.getPredicate(), s, o, false));
        }
        if (atom instanceof SWRLDataPropertyAtom) {
            SWRLDataPropertyAtom dpa = (SWRLDataPropertyAtom) atom;
            OWLNamedIndividual s = bindSwrlIArg(dpa.getFirstArgument(), iVars);
            OWLLiteral lit = resolveSwrlDArg(dpa.getSecondArgument(), dVars);
            if (s == null || lit == null) throw new UnsupportedEntailmentTypeException(rule);
            if (isTop(dpa.getPredicate())) return Collections.emptyList();
            return Collections.singletonList(df.getOWLDataPropertyAssertionAxiom(dpa.getPredicate(), s, lit));
        }
        if (atom instanceof SWRLSameIndividualAtom) {
            SWRLSameIndividualAtom sa = (SWRLSameIndividualAtom) atom;
            OWLNamedIndividual a = bindSwrlIArg(sa.getFirstArgument(), iVars);
            OWLNamedIndividual b = bindSwrlIArg(sa.getSecondArgument(), iVars);
            if (a == null || b == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLSameIndividualAxiom(a, b));
        }
        if (atom instanceof SWRLDifferentIndividualsAtom) {
            SWRLDifferentIndividualsAtom da = (SWRLDifferentIndividualsAtom) atom;
            OWLNamedIndividual a = bindSwrlIArg(da.getFirstArgument(), iVars);
            OWLNamedIndividual b = bindSwrlIArg(da.getSecondArgument(), iVars);
            if (a == null || b == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLDifferentIndividualsAxiom(a, b));
        }
        if (atom instanceof SWRLDataRangeAtom) {
            SWRLDataRangeAtom dra = (SWRLDataRangeAtom) atom;
            OWLLiteral lit = resolveSwrlDArg(dra.getArgument(), dVars);
            OWLNamedIndividual holder = freshIndividual();
            OWLDataProperty dp = df.getOWLDataProperty(fresh().next("swrldrp"));
            return Arrays.asList(
                    df.getOWLDeclarationAxiom(holder),
                    df.getOWLDeclarationAxiom(dp),
                    df.getOWLDataPropertyRangeAxiom(dp, dra.getPredicate()),
                    df.getOWLDataPropertyAssertionAxiom(dp, holder, lit));
        }
        throw new UnsupportedEntailmentTypeException(rule);
    }

    private List<OWLAxiom> groundSwrlAtomNegated(
            SWRLAtom atom,
            Map<SWRLVariable, OWLNamedIndividual> iVars,
            Map<SWRLVariable, OWLLiteral> dVars,
            SWRLRule rule) {
        if (atom instanceof SWRLClassAtom) {
            SWRLClassAtom ca = (SWRLClassAtom) atom;
            OWLNamedIndividual ind = bindSwrlIArg(ca.getArgument(), iVars);
            if (ind == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLClassAssertionAxiom(not(ca.getPredicate()), ind));
        }
        if (atom instanceof SWRLObjectPropertyAtom) {
            SWRLObjectPropertyAtom opa = (SWRLObjectPropertyAtom) atom;
            OWLNamedIndividual s = bindSwrlIArg(opa.getFirstArgument(), iVars);
            OWLNamedIndividual o = bindSwrlIArg(opa.getSecondArgument(), iVars);
            if (s == null || o == null) throw new UnsupportedEntailmentTypeException(rule);
            if (isTop(opa.getPredicate())) {
                return Collections.singletonList(df.getOWLClassAssertionAxiom(owlNothing, s));
            }
            return Collections.singletonList(assertion(opa.getPredicate(), s, o, true));
        }
        if (atom instanceof SWRLDataPropertyAtom) {
            SWRLDataPropertyAtom dpa = (SWRLDataPropertyAtom) atom;
            OWLNamedIndividual s = bindSwrlIArg(dpa.getFirstArgument(), iVars);
            OWLLiteral lit = resolveSwrlDArg(dpa.getSecondArgument(), dVars);
            if (s == null || lit == null) throw new UnsupportedEntailmentTypeException(rule);
            if (isTop(dpa.getPredicate())) {
                return Collections.singletonList(df.getOWLClassAssertionAxiom(owlNothing, s));
            }
            return Collections.singletonList(df.getOWLNegativeDataPropertyAssertionAxiom(dpa.getPredicate(), s, lit));
        }
        if (atom instanceof SWRLSameIndividualAtom) {
            SWRLSameIndividualAtom sa = (SWRLSameIndividualAtom) atom;
            OWLNamedIndividual a = bindSwrlIArg(sa.getFirstArgument(), iVars);
            OWLNamedIndividual b = bindSwrlIArg(sa.getSecondArgument(), iVars);
            if (a == null || b == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLDifferentIndividualsAxiom(a, b));
        }
        if (atom instanceof SWRLDifferentIndividualsAtom) {
            SWRLDifferentIndividualsAtom da = (SWRLDifferentIndividualsAtom) atom;
            OWLNamedIndividual a = bindSwrlIArg(da.getFirstArgument(), iVars);
            OWLNamedIndividual b = bindSwrlIArg(da.getSecondArgument(), iVars);
            if (a == null || b == null) throw new UnsupportedEntailmentTypeException(rule);
            return Collections.singletonList(df.getOWLSameIndividualAxiom(a, b));
        }
        if (atom instanceof SWRLDataRangeAtom) {
            SWRLDataRangeAtom dra = (SWRLDataRangeAtom) atom;
            OWLLiteral lit = resolveSwrlDArg(dra.getArgument(), dVars);
            OWLNamedIndividual holder = freshIndividual();
            OWLDataProperty dp = df.getOWLDataProperty(fresh().next("swrldrp"));
            return Arrays.asList(
                    df.getOWLDeclarationAxiom(holder),
                    df.getOWLDeclarationAxiom(dp),
                    df.getOWLDataPropertyRangeAxiom(dp, df.getOWLDataComplementOf(dra.getPredicate())),
                    df.getOWLDataPropertyAssertionAxiom(dp, holder, lit));
        }
        throw new UnsupportedEntailmentTypeException(rule);
    }

    private List<OWLClassExpression> pairwiseIntersections(List<OWLClassExpression> ops) {
        List<OWLClassExpression> checks = new ArrayList<>();
        for (int i = 0; i < ops.size(); i++) {
            for (int j = i + 1; j < ops.size(); j++) checks.add(and(ops.get(i), ops.get(j)));
        }
        return checks;
    }

    /**
     * The universal property is functional iff every model has one element:
     * {@code ¬{x}} is unsatisfiable for a fresh individual x.
     */
    private boolean universalFunctional() {
        return unsatisfiable(not(df.getOWLObjectOneOf(freshIndividual())));
    }

    /** Data sub-property from the data property hierarchy. */
    private boolean dataSubProperty(OWLDataPropertyExpression subExpr, OWLDataPropertyExpression supExpr) {
        OWLDataProperty sub = subExpr.asOWLDataProperty(), sup = supExpr.asOWLDataProperty();
        if (sub.equals(sup) || sub.isOWLBottomDataProperty() || sup.isOWLTopDataProperty()) return true;
        DataPropertyModel model = ensureDataProperties();
        if (model.isEmpty(sub)) return true;
        return model.equivalents(sub).contains(sup) || model.supers(sub, false).containsEntity(sup);
    }

    // ---- individuals: values and differences ----------------------------------------

    private Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> ensureAllObjectValues() {
        ensureClassified();
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> held = allObjectValues;
        if (held != null) return held;
        if (valuesFailure != null) throw valuesFailure;
        @SuppressWarnings("unchecked")
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>>[] out = new Map[1];
        long t0 = System.nanoTime();
        try {
            runTask(COMPUTING_VALUES, () -> out[0] = allObjectValuesNow());
        } catch (RuntimeException failure) {
            if (cacheableWholeRevision(failure, (System.nanoTime() - t0) / 1_000_000L)) {
                valuesFailure = failure;
            }
            throw failure;
        }
        return out[0];
    }

    private Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> allObjectValuesNow() {
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> built = new HashMap<>();
        if (!consistent) {
            allObjectValues = built;
            return built;
        }
        try {
            OWLOntology snapshot = querySnapshot();
            Set<OWLNamedIndividual> inds = signatureIndividuals();
            Set<OWLObjectProperty> ops = new LinkedHashSet<>(snapshot.getObjectPropertiesInSignature());
            ops.remove(df.getOWLTopObjectProperty());
            ops.remove(df.getOWLBottomObjectProperty());
            for (OWLObjectProperty r : ops) built.put(r, new HashMap<>());
            if (!inds.isEmpty() && !ops.isEmpty()) {
                if (activeRollup != null) {
                    built = activeRollup.buildObjectPropertyValues(
                            snapshot, incrementalSession != null ? incrementalSession.rows() : null);
                } else {
                    Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> fast =
                            ForestABoxRollup.tryComputePositiveRBoxValues(
                                    snapshot,
                                    unsatisfiable.isEmpty(),
                                    (ind, cls) -> isEntailedClassAssertion(df.getOWLClassAssertionAxiom(cls, ind)));
                    if (fast != null) {
                        built = fast;
                    } else {
                        List<OWLObjectProperty> active = activeObjectProperties(snapshot);
                        List<OWLNamedIndividual> targets = activeTargetIndividuals(snapshot);
                        if (!active.isEmpty() && !targets.isEmpty()) {
                            if (active.size() == ops.size() && targets.size() == inds.size()) {
                                Classifier.Values rows = Classifier.values(querySource(), process -> {
                                    realizeProcess = process;
                                    if (process != null && (interruptRequested || timedOut)) {
                                        NativeProcessTree.terminateAndWait(process);
                                    }
                                });
                                if (rows.consistent) {
                                    for (String[] t : rows.values) {
                                        OWLObjectProperty r = df.getOWLObjectProperty(IRI.create(normalizeIri(t[0])));
                                        OWLNamedIndividual s = df.getOWLNamedIndividual(IRI.create(normalizeIri(t[1])));
                                        OWLNamedIndividual o = df.getOWLNamedIndividual(IRI.create(normalizeIri(t[2])));
                                        built.computeIfAbsent(r, k -> new HashMap<>())
                                                .computeIfAbsent(s, k -> new LinkedHashSet<>()).add(o);
                                    }
                                }
                            } else {
                                Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> activeVals =
                                        objectValuesNow(active, targets);
                                built.putAll(activeVals);
                            }
                        }
                    }
                }
            }
            for (Map.Entry<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> e : built.entrySet()) {
                reductions.put(Arrays.asList("values", e.getKey()), e.getValue());
            }
            allObjectValues = built;
            return built;
        } catch (RuntimeException error) {
            throw error;
        } catch (Exception error) {
            throw new ReasonerInternalException(error);
        }
    }

    /**
     * Named individuals that can appear as the target (or source) of an
     * entailed non-universal object-property assertion between named
     * individuals. When the ontology contains no {@code ObjectOneOf},
     * {@code ObjectHasValue}, {@code ObjectHasSelf},
     * {@code ReflexiveObjectProperty}, {@code HasKey}, {@code SWRLRule},
     * {@code SameIndividual} or {@code owl:topObjectProperty}, any named
     * individual that does not occur in any {@code ObjectPropertyAssertion}
     * can be interpreted in a disconnected component of the canonical model
     * with no role edges to or from any named individual.
     */
    private List<OWLNamedIndividual> activeTargetIndividuals(OWLOntology snapshot) {
        List<OWLNamedIndividual> all = new ArrayList<>(signatureIndividuals());
        if (all.isEmpty()) return all;
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLReflexiveObjectPropertyAxiom
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof SWRLRule
                    || ax instanceof OWLSameIndividualAxiom) {
                return all;
            }
            for (OWLObjectProperty p : ax.getObjectPropertiesInSignature()) {
                if (p.isOWLTopObjectProperty()) return all;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf
                        || ce instanceof OWLObjectHasValue
                        || ce instanceof OWLObjectHasSelf) {
                    return all;
                }
            }
        }
        Set<OWLNamedIndividual> active = new LinkedHashSet<>();
        for (OWLObjectPropertyAssertionAxiom opa : snapshot.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
            if (opa.getSubject().isNamed()) active.add(opa.getSubject().asOWLNamedIndividual());
            if (opa.getObject().isNamed()) active.add(opa.getObject().asOWLNamedIndividual());
        }
        List<OWLNamedIndividual> sorted = new ArrayList<>(active);
        sorted.sort(Comparator.comparing(a -> a.getIRI().toString()));
        return sorted;
    }

    /**
     * Object properties that can be forced to relate named individuals by the
     * ontology's axioms. When the ontology has no {@code ObjectOneOf}, anonymous
     * existential fillers can always be satisfied by fresh unnamed witnesses, so
     * only {@code ObjectPropertyAssertion}, {@code ReflexiveObjectProperty},
     * {@code ObjectHasSelf}, {@code ObjectHasValue}, {@code HasKey}, {@code SWRLRule}
     * and {@code owl:topObjectProperty} can introduce named-individual pairs,
     * closed upwards under sub-property, property chain, equivalence and inverse.
     */
    private static boolean hasObjectOneOf(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf) return true;
            }
        }
        return false;
    }

    private List<OWLObjectProperty> activeObjectProperties(OWLOntology snapshot) {
        boolean hasObjectOneOf = hasObjectOneOf(snapshot);
        Set<OWLObjectProperty> active = new LinkedHashSet<>();
        active.add(df.getOWLTopObjectProperty());
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (hasObjectOneOf || ce instanceof OWLObjectHasValue || ce instanceof OWLObjectHasSelf) {
                    active.addAll(ce.getObjectPropertiesInSignature());
                }
            }
            if (ax instanceof OWLObjectPropertyAssertionAxiom
                    || ax instanceof OWLReflexiveObjectPropertyAxiom
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof SWRLRule) {
                active.addAll(ax.getObjectPropertiesInSignature());
            }
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
                if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                    OWLSubObjectPropertyOfAxiom a = (OWLSubObjectPropertyOfAxiom) ax;
                    if (active.contains(a.getSubProperty().getNamedProperty())
                            && active.add(a.getSuperProperty().getNamedProperty())) {
                        changed = true;
                    }
                } else if (ax instanceof OWLSubPropertyChainOfAxiom) {
                    OWLSubPropertyChainOfAxiom a = (OWLSubPropertyChainOfAxiom) ax;
                    boolean any = false;
                    for (OWLObjectPropertyExpression pe : a.getPropertyChain()) {
                        if (active.contains(pe.getNamedProperty())) {
                            any = true;
                            break;
                        }
                    }
                    if (any && active.add(a.getSuperProperty().getNamedProperty())) {
                        changed = true;
                    }
                } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom
                        || ax instanceof OWLInverseObjectPropertiesAxiom) {
                    Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                    boolean any = false;
                    for (OWLObjectProperty p : sig) {
                        if (active.contains(p)) {
                            any = true;
                            break;
                        }
                    }
                    if (any && active.addAll(sig)) {
                        changed = true;
                    }
                }
            }
        }
        active.remove(df.getOWLTopObjectProperty());
        active.remove(df.getOWLBottomObjectProperty());
        List<OWLObjectProperty> sorted = new ArrayList<>(active);
        sorted.sort(Comparator.comparing(p -> p.getIRI().toString()));
        return sorted;
    }

    /**
     * Object property values of every individual for one named property r:
     * {@code b ∈ values(a, r)} iff {@code a} is an instance of the fresh
     * {@code V_b ≡ ObjectHasValue(r b)} (exact: {@code r(a,b)} holds in a model
     * iff {@code a ∈ ∃r.{b}} there). One realization answers every subject and,
     * read backwards, the inverse expression.
     */
    private Map<OWLNamedIndividual, Set<OWLNamedIndividual>> objectValues(OWLObjectProperty r) {
        if (activeRollup != null) {
            return ensureAllObjectValues().getOrDefault(r, Collections.emptyMap());
        }
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> pre = allObjectValues;
        if (pre != null && pre.containsKey(r)) return pre.get(r);
        return reduce(Arrays.asList("values", r), COMPUTING_VALUES, () -> {
            OWLOntology snapshot = querySnapshot();
            Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> fast =
                    ForestABoxRollup.tryComputePositiveRBoxValues(
                            snapshot,
                            unsatisfiable.isEmpty(),
                            (ind, cls) -> isEntailedClassAssertion(df.getOWLClassAssertionAxiom(cls, ind)));
            if (fast != null) {
                allObjectValues = fast;
                return fast.getOrDefault(r, Collections.emptyMap());
            }
            if (!activeObjectProperties(snapshot).contains(r)) {
                return Collections.emptyMap();
            }
            List<OWLNamedIndividual> targets = activeTargetIndividuals(snapshot);
            if (targets.isEmpty()) return Collections.emptyMap();
            return objectValuesNow(Collections.singletonList(r), targets).get(r);
        });
    }

    private Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> objectValuesNow(
            List<OWLObjectProperty> properties, List<OWLNamedIndividual> targets) {
        recordReduction("R13_object_property_values_probes");
        List<OWLNamedIndividual> individuals = new ArrayList<>(signatureIndividuals());
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> out = new HashMap<>();
        for (OWLObjectProperty r : properties) out.put(r, new HashMap<>());
        if (individuals.isEmpty() || targets.isEmpty()) return out;
        List<OWLAxiom> defs = new ArrayList<>();
        Map<String, Object[]> meaning = new HashMap<>();
        for (OWLObjectProperty r : properties) {
            for (OWLNamedIndividual b : targets) {
                OWLClass v = df.getOWLClass(fresh().next("V"));
                defs.add(df.getOWLEquivalentClassesAxiom(v, df.getOWLObjectHasValue(r, b)));
                meaning.put(v.getIRI().toString(), new Object[]{r, b});
            }
        }
        ExtendedRun.Answer answer = extendedRun("property value query", defs, true, false);
        requireConsistent(answer, "property value query");
        Map<String, OWLNamedIndividual> byIri = new HashMap<>();
        for (OWLNamedIndividual a : individuals) byIri.put(a.getIRI().toString(), a);
        for (Map.Entry<String, Set<String>> row : answer.types.entrySet()) {
            OWLNamedIndividual a = byIri.get(row.getKey());
            if (a == null) continue;
            for (String cls : row.getValue()) {
                Object[] m = meaning.get(cls);
                if (m == null) continue;
                out.get((OWLObjectProperty) m[0]).computeIfAbsent(a, k -> new LinkedHashSet<>())
                        .add((OWLNamedIndividual) m[1]);
            }
        }
        return out;
    }

    private boolean mentionsTopOrBottomObjectProperty(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            for (OWLObjectProperty p : ax.getObjectPropertiesInSignature()) {
                if (p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty()) return true;
            }
        }
        return false;
    }

    private boolean mentionsTopOrBottomDataProperty(OWLOntology snapshot) {
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            for (OWLDataProperty p : ax.getDataPropertiesInSignature()) {
                if (p.isOWLTopDataProperty() || p.isOWLBottomDataProperty()) return true;
            }
        }
        return false;
    }

    private NodeSet<OWLNamedIndividual> computeObjectPropertyValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) {
        OWLObjectPropertyExpression simple = pe.getSimplified();
        Set<OWLNamedIndividual> individuals = signatureIndividuals();
        if (isTop(simple)) return individualNodes(individuals); // U relates every pair
        if (isBottom(simple)) return individualNodes(Collections.<OWLNamedIndividual>emptyList());
        OWLObjectProperty r = simple.getNamedProperty();
        // A property outside the signature is unconstrained: it can be empty.
        if (!querySnapshot().containsObjectPropertyInSignature(r.getIRI())) {
            return individualNodes(Collections.<OWLNamedIndividual>emptyList());
        }
        ObjectPropertyModel pm = propertyModel;
        if (pm == null && mentionsTopOrBottomObjectProperty(querySnapshot())) {
            try {
                pm = ensureProperties();
            } catch (RuntimeException ignored) {
                // Fall back to direct value query if property classification fails.
            }
        }
        if (pm != null) {
            int code = pm.code(simple);
            if (pm.isUniversal(code)) return individualNodes(individuals);
            if (pm.isEmpty(code)) return individualNodes(Collections.<OWLNamedIndividual>emptyList());
        }
        if (!individuals.contains(ind)) return freshSubjectValues(ind, simple);
        if (precomputedTypes.contains(InferenceType.OBJECT_PROPERTY_ASSERTIONS)
                && allObjectValues == null && valuesFailure == null && objectValuesPrecomputable()
                && (activeRollup != null || !hasObjectOneOf(querySnapshot()))) {
            try {
                ensureAllObjectValues();
            } catch (UnsupportedOperationException ignored) {
                // Fall back to per-property evaluation.
            }
        }
        Map<OWLNamedIndividual, Set<OWLNamedIndividual>> values = objectValues(r);
        List<OWLNamedIndividual> out = new ArrayList<>();
        if (simple.isAnonymous()) {
            for (Map.Entry<OWLNamedIndividual, Set<OWLNamedIndividual>> e : values.entrySet()) {
                if (e.getValue().contains(ind)) out.add(e.getKey());
            }
        } else {
            Set<OWLNamedIndividual> v = values.get(ind);
            if (v != null) out.addAll(v);
        }
        return individualNodes(out);
    }

    /**
     * Values of an individual outside the signature. It is not the interpretation
     * of any name of O, but an axiom such as {@code ⊤ ⊑ ∃r.{b}} still gives it
     * values, so the same reduction runs with the individual declared.
     */
    private NodeSet<OWLNamedIndividual> freshSubjectValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) {
        List<OWLNamedIndividual> out = reduce(Arrays.asList("fresh-values", ind, pe), COMPUTING_VALUES, () -> {
            List<OWLNamedIndividual> found = new ArrayList<>();
            List<OWLAxiom> defs = new ArrayList<>();
            Map<String, OWLNamedIndividual> meaning = new HashMap<>();
            defs.add(df.getOWLDeclarationAxiom(ind));
            for (OWLNamedIndividual b : signatureIndividuals()) {
                OWLClass v = df.getOWLClass(fresh().next("V"));
                defs.add(df.getOWLEquivalentClassesAxiom(v, df.getOWLObjectHasValue(pe, b)));
                meaning.put(v.getIRI().toString(), b);
            }
            if (meaning.isEmpty()) return found;
            ExtendedRun.Answer answer = extendedRun("property value query", defs, true, false);
            requireConsistent(answer, "property value query");
            Set<String> types = answer.types.get(ind.getIRI().toString());
            if (types != null) {
                for (String cls : types) {
                    OWLNamedIndividual b = meaning.get(cls);
                    if (b != null) found.add(b);
                }
            }
            return found;
        });
        return individualNodes(out);
    }

    /**
     * Data property values among the literals of the ontology: {@code l} is a
     * value of {@code a} iff {@code a} is an instance of the fresh
     * {@code V_{p,l} ≡ DataHasValue(p l)}. {@link DataValues} gives the fragment
     * in which no value outside these literals can be entailed; outside it the
     * query throws. All signature data properties are batched into a single
     * engine run per ontology revision.
     */
    private Set<OWLLiteral> computeDataPropertyValues(OWLNamedIndividual ind, OWLDataProperty p) {
        DataValues.Candidates candidates = reduce(Arrays.asList("literals"), COMPUTING_VALUES,
                () -> DataValues.collect(querySnapshot(), df));
        if (p.isOWLBottomDataProperty()) return new HashSet<>();
        if (p.isOWLTopDataProperty()) {
            if (candidates.outside != null) {
                throw unsupported("getDataPropertyValues", "this ontology (" + candidates.outside
                        + "): a value no literal of the ontology denotes could be entailed");
            }
            return new LinkedHashSet<>(candidates.literals);
        }
        if (!querySnapshot().containsDataPropertyInSignature(p.getIRI())) {
            return new HashSet<>();
        }
        DataPropertyModel dm = dataModel;
        if (dm == null) {
            try {
                dm = ensureDataProperties();
            } catch (RuntimeException ignored) {
                // Fall back to direct value query.
            }
        }
        if (dm != null) {
            if (dm.isEmpty(p)) return new HashSet<>();
            if (dm.isUniversal(p)) {
                if (candidates.outside != null) {
                    throw unsupported("getDataPropertyValues", "this ontology (" + candidates.outside
                            + "): a value no literal of the ontology denotes could be entailed");
                }
                return new LinkedHashSet<>(candidates.literals);
            }
        }
        boolean freshSubject = !signatureIndividuals().contains(ind);
        if (!freshSubject && dm != null) {
            Set<OWLDataProperty> subPropsAndSelf = subDataPropertiesAndSelf(dm, p);
            if (candidates.isPurelyAsserted(subPropsAndSelf)) {
                recordReduction("R04_rollup_data_property_values");
                Set<OWLNamedIndividual> same = getSameIndividuals(ind).getEntities();
                Set<OWLLiteral> resolved = new LinkedHashSet<>();
                for (OWLDataProperty subProp : subPropsAndSelf) {
                    for (OWLNamedIndividual member : same) {
                        Map<Object, OWLLiteral> m = candidates.byIndProp.get(Arrays.asList(member, subProp));
                        if (m != null) {
                            for (OWLLiteral lit : m.values()) {
                                resolved.add(candidates.resolve(same, p, lit));
                            }
                        }
                    }
                }
                return resolved;
            }
            if (activeRollup != null) {
                recordReduction("R04_rollup_data_property_values");
                Set<String> subs = classesWithDataSome.get(p);
                if (subs != null) {
                    OWLClass eff = activeRollup.effectiveClassOf(ind, df);
                    String effIri = eff != null ? eff.getIRI().toString() : owlThing.getIRI().toString();
                    if (!subs.contains(owlThing.getIRI().toString()) && !subs.contains(effIri)) {
                        return new HashSet<>();
                    }
                }
            }
        }
        if (candidates.outside != null) {
            throw unsupported("getDataPropertyValues", "this ontology (" + candidates.outside
                    + "): a value no literal of the ontology denotes could be entailed");
        }
        if (candidates.literals.isEmpty()) {
            return new HashSet<>();
        }
        Map<OWLNamedIndividual, Set<OWLLiteral>> values;
        if (!freshSubject && activeRollup == null) {
            final DataPropertyModel finalDm = dm;
            Map<OWLDataProperty, Map<OWLNamedIndividual, Set<OWLLiteral>>> allDataValues = reduce(
                    Collections.singletonList("all-data-values"), COMPUTING_VALUES, () -> {
                recordReduction("R12_data_property_values_batch");
                OWLOntology snapshot = querySnapshot();
                Map<OWLDataProperty, List<OWLDataRange>> statedRanges = new HashMap<>();
                for (OWLDataPropertyRangeAxiom ax : snapshot.getAxioms(AxiomType.DATA_PROPERTY_RANGE)) {
                    if (!ax.getProperty().isAnonymous()) {
                        statedRanges.computeIfAbsent(
                                ax.getProperty().asOWLDataProperty(), k -> new ArrayList<>()).add(ax.getRange());
                    }
                }
                List<OWLDataProperty> allProps = new ArrayList<>(snapshot.getDataPropertiesInSignature());
                allProps.remove(df.getOWLTopDataProperty());
                allProps.remove(df.getOWLBottomDataProperty());
                allProps.sort(Comparator.comparing(q -> q.getIRI().toString()));
                List<OWLAxiom> defs = new ArrayList<>();
                Map<String, Object[]> meaning = new HashMap<>();
                Map<OWLDataProperty, Map<OWLNamedIndividual, Set<OWLLiteral>>> found = new HashMap<>();
                for (OWLDataProperty q : allProps) {
                    found.put(q, new HashMap<>());
                    if (finalDm != null && (finalDm.isEmpty(q) || finalDm.isUniversal(q))) continue;
                    Set<OWLDataProperty> subProps = finalDm != null ? subDataPropertiesAndSelf(finalDm, q) : null;
                    if (subProps != null && candidates.isPurelyAsserted(subProps)) continue;
                    Set<OWLDataProperty> supProps = finalDm != null ? superDataPropertiesAndSelf(finalDm, q)
                            : Collections.singleton(q);
                    List<OWLDataRange> qRanges = new ArrayList<>();
                    for (OWLDataProperty sup : supProps) {
                        List<OWLDataRange> sr = statedRanges.get(sup);
                        if (sr != null) qRanges.addAll(sr);
                    }
                    for (OWLLiteral l : candidates.candidatesForProperty(subProps, qRanges)) {
                        OWLClass v = df.getOWLClass(fresh().next("V"));
                        defs.add(df.getOWLEquivalentClassesAxiom(v, df.getOWLDataHasValue(q, l)));
                        meaning.put(v.getIRI().toString(), new Object[]{q, l});
                    }
                }
                if (defs.isEmpty()) return found;
                ExtendedRun.Answer answer = extendedRun("data property value query", defs, true, false);
                requireConsistent(answer, "data property value query");
                for (Map.Entry<String, Set<String>> row : answer.types.entrySet()) {
                    if (fresh().isFresh(row.getKey())) continue;
                    OWLNamedIndividual a = df.getOWLNamedIndividual(IRI.create(row.getKey()));
                    for (String cls : row.getValue()) {
                        Object[] m = meaning.get(cls);
                        if (m != null) {
                            found.get((OWLDataProperty) m[0])
                                    .computeIfAbsent(a, k -> new LinkedHashSet<>()).add((OWLLiteral) m[1]);
                        }
                    }
                }
                return found;
            });
            values = allDataValues.getOrDefault(p, Collections.emptyMap());
        } else {
            values = reduce(
                    Arrays.asList("data-values", p, freshSubject ? ind : null), COMPUTING_VALUES, () -> {
                List<OWLAxiom> defs = new ArrayList<>();
                if (freshSubject) defs.add(df.getOWLDeclarationAxiom(ind));
                Map<String, OWLLiteral> meaning = new HashMap<>();
                for (OWLLiteral l : candidates.literals) {
                    OWLClass v = df.getOWLClass(fresh().next("V"));
                    defs.add(df.getOWLEquivalentClassesAxiom(v, df.getOWLDataHasValue(p, l)));
                    meaning.put(v.getIRI().toString(), l);
                }
                ExtendedRun.Answer answer = extendedRun("data property value query", defs, true, false);
                requireConsistent(answer, "data property value query");
                Map<OWLNamedIndividual, Set<OWLLiteral>> found = new HashMap<>();
                for (Map.Entry<String, Set<String>> row : answer.types.entrySet()) {
                    if (fresh().isFresh(row.getKey()) ) continue;
                    OWLNamedIndividual a = df.getOWLNamedIndividual(IRI.create(row.getKey()));
                    for (String cls : row.getValue()) {
                        OWLLiteral l = meaning.get(cls);
                        if (l != null) found.computeIfAbsent(a, k -> new LinkedHashSet<>()).add(l);
                    }
                }
                return found;
            });
        }
        Set<OWLLiteral> v = values.get(ind);
        if (v == null || v.isEmpty()) return new HashSet<>();
        Set<OWLNamedIndividual> same = getSameIndividuals(ind).getEntities();
        Set<OWLLiteral> resolved = new LinkedHashSet<>();
        for (OWLLiteral l : v) resolved.add(candidates.resolve(same, p, l));
        return resolved;
    }

    private Set<OWLDataProperty> subDataPropertiesAndSelf(DataPropertyModel dm, OWLDataProperty p) {
        Set<OWLDataProperty> subPropsAndSelf = new LinkedHashSet<>(dm.equivalents(p).getEntities());
        for (Node<OWLDataProperty> n : dm.subs(p, false).getNodes()) {
            subPropsAndSelf.addAll(n.getEntities());
        }
        subPropsAndSelf.remove(df.getOWLBottomDataProperty());
        return subPropsAndSelf;
    }

    private Set<OWLDataProperty> superDataPropertiesAndSelf(DataPropertyModel dm, OWLDataProperty p) {
        Set<OWLDataProperty> supPropsAndSelf = new LinkedHashSet<>(dm.equivalents(p).getEntities());
        for (Node<OWLDataProperty> n : dm.supers(p, false).getNodes()) {
            supPropsAndSelf.addAll(n.getEntities());
        }
        supPropsAndSelf.remove(df.getOWLTopDataProperty());
        return supPropsAndSelf;
    }

    /**
     * Individuals entailed to differ from {@code a}: those {@code b} for which the
     * fresh {@code X_b ⊑ {a} ⊓ {b}} is unsatisfiable, all in one classification
     * run (exact: {@code {a} ⊓ {b}} is empty in a model iff {@code a ≠ b} there).
     * The instance form {@code ¬{a}} needs a realization, which km finishes far
     * more slowly on the same inputs.
     */
    private NodeSet<OWLNamedIndividual> computeDifferentIndividuals(OWLNamedIndividual ind) {
        if (activeRollup != null) {
            List<OWLNamedIndividual> diff = reduce(Arrays.asList("different", ind), CHECKING_ENTAILMENT, () -> {
                List<OWLNamedIndividual> found = new ArrayList<>();
                if (!activeRollup.allIndividuals.contains(ind)) return found;
                Set<OWLNamedIndividual> same = getSameIndividuals(ind).getEntities();
                OWLClass cA = activeRollup.effectiveClassOf(ind, df);
                List<OWLAxiom> defs = new ArrayList<>();
                Map<String, OWLNamedIndividual> meaning = new LinkedHashMap<>();
                for (OWLNamedIndividual b : activeRollup.allIndividuals) {
                    if (b.equals(ind) || same.contains(b)) continue;
                    if (activeRollup.hasFunctionalDataConflict(ind, b)) {
                        found.add(b);
                        continue;
                    }
                    OWLClass cB = activeRollup.effectiveClassOf(b, df);
                    if (cA != null && cB != null) {
                        OWLClass x = df.getOWLClass(fresh().next("X"));
                        defs.add(df.getOWLSubClassOfAxiom(x, and(cA, cB)));
                        meaning.put(x.getIRI().toString(), b);
                    }
                }
                if (!defs.isEmpty()) {
                    ExtendedRun.Answer answer = extendedRun("different individuals query", defs, false, false);
                    requireConsistent(answer, "different individuals query");
                    for (Map.Entry<String, OWLNamedIndividual> e : meaning.entrySet()) {
                        if (answer.unsat.contains(e.getKey())) {
                            found.add(e.getValue());
                        }
                    }
                }
                return found;
            });
            return individualNodes(diff);
        }
        List<OWLNamedIndividual> different = reduce(Arrays.asList("different", ind), CHECKING_ENTAILMENT, () -> {
            recordReduction("R14_different_individuals_nominal_probes");
            List<OWLAxiom> defs = new ArrayList<>();
            Map<String, OWLNamedIndividual> meaning = new HashMap<>();
            for (OWLNamedIndividual b : signatureIndividuals()) {
                if (b.equals(ind)) continue;
                OWLClass x = df.getOWLClass(fresh().next("X"));
                defs.add(df.getOWLSubClassOfAxiom(x,
                        and(df.getOWLObjectOneOf(ind), df.getOWLObjectOneOf(b))));
                meaning.put(x.getIRI().toString(), b);
            }
            List<OWLNamedIndividual> found = new ArrayList<>();
            if (defs.isEmpty()) return found;
            ExtendedRun.Answer answer = extendedRun("different individuals query", defs, false, false);
            requireConsistent(answer, "different individuals query");
            for (Map.Entry<String, OWLNamedIndividual> e : meaning.entrySet()) {
                if (answer.unsat.contains(e.getKey())) {
                    found.add(e.getValue());
                }
            }
            return found;
        });
        return individualNodes(different);
    }

    /**
     * Object properties disjoint with {@code pe}: for each node of the hierarchy
     * other than top and bottom, with member {@code s}, introduce a fresh
     * subproperty {@code pf_s ⊑ pe, pf_s ⊑ s} and fresh probe class
     * {@code X_s ⊑ ∃pf_s.⊤}, all in one nominal-free classification run.
     * Exact: {@code pe ∩ s} is non-empty in some model of {@code O} iff
     * {@code ∃pf_s.⊤} is satisfiable in {@code O ∪ {pf_s ⊑ pe, pf_s ⊑ s}}.
     */
    private NodeSet<OWLObjectPropertyExpression> disjointObjectProperties(ObjectPropertyModel model,
                                                                          OWLObjectPropertyExpression pe) {
        List<Integer> disjoint = reduce(Arrays.asList("disjoint-properties", pe.getSimplified()),
                CHECKING_ENTAILMENT, () -> {
            recordReduction("R15_disjoint_object_properties_probes");
            int codePe = model.code(pe);
            List<OWLAxiom> defs = new ArrayList<>();
            Map<String, Integer> nodeOfClass = new HashMap<>();
            List<Integer> found = new ArrayList<>();
            for (int c = 2; c < model.nodeCount(); c++) {
                OWLObjectPropertyExpression s = model.representative(c);
                if (s == null) continue;
                if (model.entails(pe, s) || model.entails(s, pe)) continue;
                int codeS = model.code(s);
                if (areDomainsOrRangesStatedDisjoint(model, codePe, codeS)) {
                    found.add(c);
                    continue;
                }
                OWLObjectProperty pf = df.getOWLObjectProperty(fresh().next("pf"));
                OWLClass x = df.getOWLClass(fresh().next("X"));
                defs.add(df.getOWLDeclarationAxiom(pf));
                defs.add(df.getOWLDeclarationAxiom(x));
                defs.add(df.getOWLSubObjectPropertyOfAxiom(pf, pe));
                defs.add(df.getOWLSubObjectPropertyOfAxiom(pf, s));
                defs.add(df.getOWLSubClassOfAxiom(x, df.getOWLObjectSomeValuesFrom(pf, owlThing)));
                nodeOfClass.put(x.getIRI().toString(), c);
            }
            if (defs.isEmpty()) return found;
            ExtendedRun.Answer answer = extendedRun("disjoint property query", defs, false, false);
            requireConsistent(answer, "disjoint property query");
            for (Map.Entry<String, Integer> e : nodeOfClass.entrySet()) {
                if (answer.unsat.contains(e.getKey())) found.add(e.getValue());
            }
            return found;
        });
        OWLObjectPropertyNodeSet ns = new OWLObjectPropertyNodeSet();
        for (int c : disjoint) ns.addNode(model.nodeAt(c));
        ns.addNode(model.bottomNode());
        return ns;
    }

    /**
     * Data properties disjoint with a satisfiable, non-universal {@code p}:
     * read directly from {@code model} when {@code --data-properties} computed
     * pairwise disjointness; inside {@link DataPropertyModel}'s syntactic
     * fragment with compatible ranges, decided from the conjunction of stated
     * domains; otherwise decided by one probe run with a fresh free literal
     * testing {@code DataHasValue(p, v) ⊓ DataHasValue(q, v)} per candidate node.
     */
    private NodeSet<OWLDataProperty> disjointDataProperties(DataPropertyModel model, OWLDataProperty p) {
        if (model.hasDisjoint()) return model.disjointNodes(p);
        List<Integer> nodes = reduce(Arrays.asList("disjoint-data", p), CHECKING_ENTAILMENT, () -> {
            recordReduction("R11_disjoint_data_properties");
            List<Integer> domainCandidates = new ArrayList<>();
            List<OWLClassExpression> domainChecks = new ArrayList<>();
            List<Integer> probeCandidates = new ArrayList<>();
            int selfNode = model.nodeIndexOf(p);
            for (int c = 2; c < model.nodeCount(); c++) {
                if (c == selfNode) continue;
                OWLDataProperty q = model.representative(c);
                if (q == null) continue;
                if (model.hasSyntacticDomains() && model.jointRanges(p, q).size() <= 1) {
                    Set<OWLClassExpression> domains = new LinkedHashSet<>(model.jointDomains(p, q));
                    if (domains.isEmpty()) continue; // only owl:Thing: some element takes the pair
                    domainCandidates.add(c);
                    domainChecks.add(domains.size() == 1
                            ? domains.iterator().next()
                            : df.getOWLObjectIntersectionOf(domains));
                } else {
                    probeCandidates.add(c);
                }
            }
            List<Integer> found = new ArrayList<>();
            if (!domainChecks.isEmpty()) allUnsatisfiable(domainChecks);
            for (int i = 0; i < domainChecks.size(); i++) {
                if (unsatisfiable(domainChecks.get(i))) found.add(domainCandidates.get(i));
            }
            if (!probeCandidates.isEmpty()) {
                OWLDatatype freeDt = df.getOWLDatatype(fresh().next("free"));
                OWLLiteral lit = df.getOWLLiteral("v", freeDt);
                OWLClassExpression pEdge = df.getOWLDataHasValue(p, lit);
                List<OWLAxiom> defs = new ArrayList<>();
                Map<String, Integer> nodeOfClass = new HashMap<>();
                for (int c : probeCandidates) {
                    OWLDataProperty q = model.representative(c);
                    OWLClass x = df.getOWLClass(fresh().next("DPPair"));
                    defs.add(df.getOWLSubClassOfAxiom(x, and(pEdge, df.getOWLDataHasValue(q, lit))));
                    nodeOfClass.put(x.getIRI().toString(), c);
                }
                ExtendedRun.Answer answer = extendedRun("disjoint data property query", defs, false, false, true);
                requireConsistent(answer, "disjoint data property query");
                for (Map.Entry<String, Integer> e : nodeOfClass.entrySet()) {
                    if (answer.unsat.contains(e.getKey())) found.add(e.getValue());
                }
            }
            return found;
        });
        OWLDataPropertyNodeSet ns = new OWLDataPropertyNodeSet();
        for (int c : nodes) ns.addNode(model.nodeAt(c));
        ns.addNode(model.bottomNode());
        return ns;
    }

    private int[] nonBottomRepsWithBottom() {
        Set<Integer> reps = new TreeSet<>();
        for (int c = 0; c < repId.length; c++) reps.add(repId[c]);
        return toArray(reps);
    }
}
