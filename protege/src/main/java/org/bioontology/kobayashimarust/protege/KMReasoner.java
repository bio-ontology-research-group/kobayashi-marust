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

    private boolean consistent = true;
    private int dropped = 0;
    // representative -> the equivalence group (set of classes that are mutually equivalent)
    private final Map<OWLClass, Set<OWLClass>> group = new HashMap<>();
    private final Map<OWLClass, OWLClass> rep = new HashMap<>();
    // condensed proper super relation over representatives (transitively closed)
    private final Map<OWLClass, Set<OWLClass>> supers = new HashMap<>();
    private final Map<OWLClass, Set<OWLClass>> subs = new HashMap<>();
    private final Set<OWLClass> unsatisfiable = new HashSet<>();

    protected KMReasoner(OWLOntology rootOntology, OWLReasonerConfiguration config,
                         BufferingMode bufferingMode) {
        super(rootOntology, config, bufferingMode);
        this.df = rootOntology.getOWLOntologyManager().getOWLDataFactory();
        this.owlThing = df.getOWLThing();
        this.owlNothing = df.getOWLNothing();
        classify();
    }

    // ---- classification -------------------------------------------------

    private void classify() {
        group.clear(); rep.clear(); supers.clear(); subs.clear(); unsatisfiable.clear();
        OWLOntology ont = getRootOntology();

        // Complete IRI -> named class. Local fragments are not unique.
        Map<String, OWLClass> byIri = new HashMap<>();
        Set<OWLClass> classes = new HashSet<>(ont.getClassesInSignature(Imports.INCLUDED));
        classes.add(owlThing); classes.add(owlNothing);
        for (OWLClass c : classes) byIri.put(c.getIRI().toString(), c);

        Classifier.Result res;
        try {
            res = Classifier.classify(ont);
        } catch (Exception e) {
            throw new ReasonerInternalException(e);
        }
        consistent = res.consistent;
        dropped = res.dropped;

        // direct (non-closed) named subsumptions
        List<OWLClass[]> pairs = new ArrayList<>();
        for (String[] p : res.subsumptions) {
            OWLClass a = byIri.get(normalizeIri(p[0]));
            OWLClass b = byIri.get(normalizeIri(p[1]));
            if (a != null && b != null && !a.equals(b)) pairs.add(new OWLClass[]{a, b});
        }
        for (String u : res.unsatisfiable) {
            OWLClass c = byIri.get(normalizeIri(u));
            if (c != null) unsatisfiable.add(c);
        }

        // closure (engine already returns the transitive closure, but be safe)
        Map<OWLClass, Set<OWLClass>> sup = new HashMap<>();
        for (OWLClass c : classes) sup.put(c, new HashSet<>());
        for (OWLClass[] p : pairs) sup.get(p[0]).add(p[1]);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (OWLClass c : classes) {
                Set<OWLClass> s = sup.get(c);
                for (OWLClass m : new ArrayList<>(s))
                    if (s.addAll(sup.getOrDefault(m, Collections.emptySet()))) changed = true;
            }
        }
        // everything is below Thing
        for (OWLClass c : classes) if (!c.equals(owlThing)) sup.get(c).add(owlThing);

        // equivalence = mutual subsumption (union-find by representatives)
        for (OWLClass c : classes) rep.put(c, c);
        for (OWLClass c : classes)
            for (OWLClass d : sup.get(c))
                if (!c.equals(d) && sup.getOrDefault(d, Collections.emptySet()).contains(c))
                    union(c, d);
        // unsatisfiable classes are equivalent to owl:Nothing
        for (OWLClass u : unsatisfiable) union(u, owlNothing);

        for (OWLClass c : classes) group.computeIfAbsent(find(c), k -> new HashSet<>()).add(c);

        // condensed proper supers over representatives
        for (OWLClass c : classes) {
            OWLClass rc = find(c);
            supers.computeIfAbsent(rc, k -> new HashSet<>());
            subs.computeIfAbsent(rc, k -> new HashSet<>());
        }
        for (OWLClass c : classes) {
            OWLClass rc = find(c);
            for (OWLClass d : sup.get(c)) {
                OWLClass rd = find(d);
                if (!rc.equals(rd)) { supers.get(rc).add(rd); subs.get(rd).add(rc); }
            }
        }
    }

    private OWLClass find(OWLClass c) {
        OWLClass r = rep.get(c);
        while (!r.equals(rep.get(r))) r = rep.get(r);
        rep.put(c, r);
        return r;
    }

    private void union(OWLClass a, OWLClass b) {
        OWLClass ra = find(a), rb = find(b);
        if (!ra.equals(rb)) rep.put(ra, rb);
    }

    private static String normalizeIri(String iri) {
        if (iri.length() >= 2 && iri.charAt(0) == '<'
                && iri.charAt(iri.length() - 1) == '>') {
            return iri.substring(1, iri.length() - 1);
        }
        return iri;
    }

    // ---- node helpers ---------------------------------------------------

    private OWLClassNode nodeOf(OWLClass repClass) {
        return new OWLClassNode(group.getOrDefault(find(repClass),
                Collections.singleton(repClass)));
    }

    private OWLClass repOf(OWLClassExpression ce) {
        if (ce.isOWLThing()) return find(owlThing);
        if (ce.isOWLNothing()) return find(owlNothing);
        if (ce instanceof OWLClass) return find((OWLClass) ce);
        return null; // complex expressions are not classified
    }

    // ---- class hierarchy queries ---------------------------------------

    @Override public Node<OWLClass> getTopClassNode() { return nodeOf(owlThing); }
    @Override public Node<OWLClass> getBottomClassNode() { return nodeOf(owlNothing); }

    @Override public Node<OWLClass> getEquivalentClasses(OWLClassExpression ce) {
        OWLClass r = repOf(ce);
        return r != null ? nodeOf(r) : new OWLClassNode();
    }

    @Override public NodeSet<OWLClass> getSuperClasses(OWLClassExpression ce, boolean direct) {
        OWLClass r = repOf(ce);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (r == null) return ns;
        Set<OWLClass> all = supers.getOrDefault(r, Collections.emptySet());
        for (OWLClass s : direct ? minimal(all) : all) ns.addNode(nodeOf(s));
        return ns;
    }

    @Override public NodeSet<OWLClass> getSubClasses(OWLClassExpression ce, boolean direct) {
        OWLClass r = repOf(ce);
        OWLClassNodeSet ns = new OWLClassNodeSet();
        if (r == null) return ns;
        Set<OWLClass> all = subs.getOrDefault(r, Collections.emptySet());
        for (OWLClass s : direct ? maximal(all) : all) ns.addNode(nodeOf(s));
        return ns;
    }

    /** super-reps with no intermediate (direct supers). */
    private Set<OWLClass> minimal(Set<OWLClass> set) {
        Set<OWLClass> out = new HashSet<>();
        for (OWLClass x : set) {
            boolean isDirect = true;
            for (OWLClass y : set)
                if (!x.equals(y) && supers.getOrDefault(y, Collections.emptySet()).contains(x)) {
                    isDirect = false; break;
                }
            if (isDirect) out.add(x);
        }
        return out;
    }

    /** sub-reps with no intermediate (direct subs). */
    private Set<OWLClass> maximal(Set<OWLClass> set) {
        Set<OWLClass> out = new HashSet<>();
        for (OWLClass x : set) {
            boolean isDirect = true;
            for (OWLClass y : set)
                if (!x.equals(y) && subs.getOrDefault(y, Collections.emptySet()).contains(x)) {
                    isDirect = false; break;
                }
            if (isDirect) out.add(x);
        }
        return out;
    }

    @Override public Node<OWLClass> getUnsatisfiableClasses() { return nodeOf(owlNothing); }

    @Override public boolean isConsistent() { return consistent; }

    @Override public boolean isSatisfiable(OWLClassExpression ce) {
        if (!consistent) return false;
        OWLClass r = repOf(ce);
        if (ce.isOWLNothing()) return false;
        if (r == null) return true; // unknown complex expression: not refuted
        return !find(owlNothing).equals(r);
    }

    /** convenience for tests: dropped-clause count from the last classification. */
    public int getDroppedClauseCount() { return dropped; }

    // ---- precompute / metadata -----------------------------------------

    @Override public String getReasonerName() { return "Kobayashi-MaRust"; }
    @Override public Version getReasonerVersion() { return new Version(0, 3, 0, 0); }

    @Override public void precomputeInferences(InferenceType... types) { /* eager in ctor */ }
    @Override public boolean isPrecomputed(InferenceType inferenceType) { return true; }
    @Override public Set<InferenceType> getPrecomputableInferenceTypes() {
        return new HashSet<>(Arrays.asList(InferenceType.CLASS_HIERARCHY));
    }

    @Override protected void handleChanges(Set<OWLAxiom> addAxioms, Set<OWLAxiom> removeAxioms) {
        classify(); // re-run on flush()
    }

    @Override public void interrupt() { /* subprocess timeout is configurable */ }

    // ---- entailment ----------------------------------------------------

    @Override public boolean isEntailed(OWLAxiom axiom) {
        if (axiom instanceof OWLSubClassOfAxiom) {
            OWLSubClassOfAxiom s = (OWLSubClassOfAxiom) axiom;
            OWLClass a = s.getSubClass().isAnonymous() ? null : s.getSubClass().asOWLClass();
            OWLClassExpression sup = s.getSuperClass();
            if (a != null && sup instanceof OWLClass) {
                if (sup.isOWLThing()) return true;
                return supers.getOrDefault(find(a), Collections.emptySet())
                        .contains(find((OWLClass) sup));
            }
        }
        return false;
    }

    @Override public boolean isEntailed(Set<? extends OWLAxiom> axioms) {
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
