package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNode;
import org.semanticweb.owlapi.reasoner.impl.OWLClassNodeSet;
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
 * It is a <em>TBox classifier</em>: it computes the named-class hierarchy and
 * unsatisfiable classes. Property/individual inferences are not provided
 * (empty results), which is the honest scope of the engine.
 */
public class KMReasoner extends org.semanticweb.owlapi.reasoner.impl.OWLReasonerBase {

    private final OWLDataFactory df;
    private final OWLClass owlThing;
    private final OWLClass owlNothing;

    private static final int[] EMPTY_INTS = new int[0];

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
    private Set<OWLOntology> committedImports = Collections.emptySet();
    private boolean lastPreparationUsedDelta;
    private boolean hierarchyBuilt;
    private Set<OWLClass> lastPreparedClasses;
    private Set<OWLClass> lastClasses;
    private FlushContext flushContext;

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
        classify();
    }

    // ---- classification -------------------------------------------------

    private synchronized void classify() { classify(null, null); }

    private void classify(Set<OWLAxiom> added, Set<OWLAxiom> removed) {
        try {
            classifySource(added, removed);
            sourceSynchronized = true;
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
                incrementalSession = new Classifier.Session(candidateSource);
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
                if (rc != rd) buf[count++] = rd;
            }
            Arrays.sort(buf, 0, count);
            int u = 0;
            for (int i = 0; i < count; i++) {
                if (i == 0 || buf[i] != buf[i - 1]) buf[u++] = buf[i];
            }
            supersByRep[rc] = u == 0 ? EMPTY_INTS : (u == buf.length ? buf : Arrays.copyOf(buf, u));
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

    @Override public synchronized Node<OWLClass> getTopClassNode() { return nodeOfId(repId[thingId]); }
    @Override public synchronized Node<OWLClass> getBottomClassNode() { return nodeOfId(repId[nothingId]); }

    @Override public synchronized Node<OWLClass> getEquivalentClasses(OWLClassExpression ce) {
        int r = repIdOf(ce);
        return r >= 0 ? nodeOfId(r) : new OWLClassNode();
    }

    @Override public synchronized NodeSet<OWLClass> getSuperClasses(OWLClassExpression ce, boolean direct) {
        int r = repIdOf(ce);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (r < 0) return ns;
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
        int r = repIdOf(ce);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (r < 0) return ns;
        int[][] subs = ensureSubsByRep();
        int[] all = subs[r];
        if (all == null || all.length == 0) return ns;
        if (!direct) {
            for (int s : all) ns.addNode(nodeOfId(s));
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

    @Override public synchronized Node<OWLClass> getUnsatisfiableClasses() { return nodeOfId(repId[nothingId]); }

    @Override public synchronized boolean isConsistent() { return consistent; }

    @Override public synchronized boolean isSatisfiable(OWLClassExpression ce) {
        if (!consistent) return false;
        if (ce.isOWLNothing()) return false;
        int r = repIdOf(ce);
        if (r < 0) return true; // unknown complex expression: not refuted
        return r != repId[nothingId];
    }

    /** convenience for tests: dropped-clause count from the last classification. */
    public synchronized int getDroppedClauseCount() { return dropped; }

    /** Last native transaction receipt; null for the initial revision. */
    public synchronized Classifier.IncrementalReceipt getLastIncrementalReceipt() {
        return incrementalSession == null ? null : incrementalSession.receipt();
    }

    /** A detached copy of the source snapshot backing the current answers. */
    public synchronized OWLOntology getCommittedOntologySnapshot() {
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
    @Override public Version getReasonerVersion() { return new Version(1, 5, 2, 0); }

    @Override public void precomputeInferences(InferenceType... types) { /* eager in ctor */ }
    @Override public boolean isPrecomputed(InferenceType inferenceType) { return true; }
    @Override public Set<InferenceType> getPrecomputableInferenceTypes() {
        return new HashSet<>(Arrays.asList(InferenceType.CLASS_HIERARCHY));
    }

    @Override public synchronized void flush() {
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
        if (context != null && context.allowDelta) classify(addAxioms, removeAxioms);
        else classify();
    }

    @Override public void interrupt() {
        Classifier.Session session = incrementalSession;
        if (session != null) {
            session.interrupt();
            if (incrementalSession == session) incrementalSession = null;
        }
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
        // Classical OWL semantics: inconsistency entails every supported
        // query; bottom and an unsatisfiable named class entail every class.
        if (!consistent || sub.isOWLNothing() || sup.isOWLThing() || sub.equals(sup)) {
            return true;
        }
        int subRep = repIdOf(sub);
        if (subRep >= 0 && subRep == repId[nothingId]) return true;
        int supRep = repIdOf(sup);
        if (subRep < 0 || supRep < 0) return false;
        if (subRep == supRep) return true;
        int[] sups = supersByRep[subRep];
        return sups != null && Arrays.binarySearch(sups, supRep) >= 0;
    }

    @Override public synchronized boolean isEntailed(Set<? extends OWLAxiom> axioms) {
        for (OWLAxiom a : axioms) if (!isEntailed(a)) return false;
        return true;
    }

    @Override public boolean isEntailmentCheckingSupported(AxiomType<?> axiomType) {
        return AxiomType.SUBCLASS_OF.equals(axiomType);
    }

    // ---- unsupported (TBox-only reasoner): empty / trivial results ------

    private static final NodeSet<OWLClass> EMPTY_C = new OWLClassNodeSet();
    private static final NodeSet<OWLNamedIndividual> EMPTY_I = new OWLNamedIndividualNodeSet();

    @Override public NodeSet<OWLClass> getDisjointClasses(OWLClassExpression ce) { return EMPTY_C; }
    @Override public NodeSet<OWLClass> getTypes(OWLNamedIndividual ind, boolean direct) { return EMPTY_C; }
    @Override public NodeSet<OWLNamedIndividual> getInstances(OWLClassExpression ce, boolean direct) { return EMPTY_I; }
    @Override public NodeSet<OWLClass> getObjectPropertyDomains(OWLObjectPropertyExpression pe, boolean direct) { return EMPTY_C; }
    @Override public NodeSet<OWLClass> getObjectPropertyRanges(OWLObjectPropertyExpression pe, boolean direct) { return EMPTY_C; }
    @Override public NodeSet<OWLClass> getDataPropertyDomains(OWLDataProperty pe, boolean direct) { return EMPTY_C; }

    @Override public Node<OWLObjectPropertyExpression> getTopObjectPropertyNode() { return new OWLObjectPropertyNode(df.getOWLTopObjectProperty()); }
    @Override public Node<OWLObjectPropertyExpression> getBottomObjectPropertyNode() { return new OWLObjectPropertyNode(df.getOWLBottomObjectProperty()); }
    @Override public Node<OWLDataProperty> getTopDataPropertyNode() { return new OWLDataPropertyNode(df.getOWLTopDataProperty()); }
    @Override public Node<OWLDataProperty> getBottomDataPropertyNode() { return new OWLDataPropertyNode(df.getOWLBottomDataProperty()); }

    @Override public NodeSet<OWLObjectPropertyExpression> getSubObjectProperties(OWLObjectPropertyExpression pe, boolean direct) { return new OWLObjectPropertyNodeSet(); }
    @Override public NodeSet<OWLObjectPropertyExpression> getSuperObjectProperties(OWLObjectPropertyExpression pe, boolean direct) { return new OWLObjectPropertyNodeSet(); }
    @Override public Node<OWLObjectPropertyExpression> getEquivalentObjectProperties(OWLObjectPropertyExpression pe) { return new OWLObjectPropertyNode(pe); }
    @Override public NodeSet<OWLObjectPropertyExpression> getDisjointObjectProperties(OWLObjectPropertyExpression pe) { return new OWLObjectPropertyNodeSet(); }
    @Override public Node<OWLObjectPropertyExpression> getInverseObjectProperties(OWLObjectPropertyExpression pe) { return new OWLObjectPropertyNode(pe); }
    @Override public NodeSet<OWLNamedIndividual> getObjectPropertyValues(OWLNamedIndividual ind, OWLObjectPropertyExpression pe) { return EMPTY_I; }

    @Override public NodeSet<OWLDataProperty> getSubDataProperties(OWLDataProperty pe, boolean direct) { return new OWLDataPropertyNodeSet(); }
    @Override public NodeSet<OWLDataProperty> getSuperDataProperties(OWLDataProperty pe, boolean direct) { return new OWLDataPropertyNodeSet(); }
    @Override public Node<OWLDataProperty> getEquivalentDataProperties(OWLDataProperty pe) { return new OWLDataPropertyNode(pe); }
    @Override public NodeSet<OWLDataProperty> getDisjointDataProperties(OWLDataPropertyExpression pe) { return new OWLDataPropertyNodeSet(); }
    @Override public Set<OWLLiteral> getDataPropertyValues(OWLNamedIndividual ind, OWLDataProperty pe) { return Collections.emptySet(); }

    @Override public Node<OWLNamedIndividual> getSameIndividuals(OWLNamedIndividual ind) {
        return new org.semanticweb.owlapi.reasoner.impl.OWLNamedIndividualNode(ind);
    }
    @Override public NodeSet<OWLNamedIndividual> getDifferentIndividuals(OWLNamedIndividual ind) { return EMPTY_I; }
}
