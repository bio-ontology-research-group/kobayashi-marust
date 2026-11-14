package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLDataPropertyNodeSet;
import org.semanticweb.owlapi.vocab.OWL2Datatype;

import java.util.*;

/**
 * The entailed data property hierarchy of one ontology revision, for the
 * ontologies where it follows from the asserted axioms and the class
 * taxonomy. KM has no native data property classification, so the model
 * refuses (with {@link UnsupportedOperationException}) every ontology outside
 * the fragment below instead of returning a told approximation.
 *
 * <p><b>The fragment.</b> Every axiom that mentions a data property is one of:
 * a non-logical axiom (declaration, annotation); {@code SubDataPropertyOf} or
 * {@code EquivalentDataProperties} between named data properties (the top and
 * bottom property included); {@code DataPropertyAssertion};
 * {@code FunctionalDataProperty}, {@code DataPropertyDomain} with a named
 * class and {@code DataPropertyRange} with a built-in datatype, these three
 * only on properties other than top and bottom. No class axiom, rule, key,
 * disjointness or complex range mentions a data property. If the ontology
 * has a {@code FunctionalDataProperty} axiom it must also have no nominal:
 * no {@code ObjectOneOf}, {@code ObjectHasValue} or {@code DataHasValue} in
 * any class expression and no SWRL rule (imports included).
 *
 * <p><b>Why the told hierarchy is then complete.</b> Let {@code r(p)} be the
 * properties reachable from {@code p} by the stated sub-property and
 * equivalence edges. Then {@code p ⊑ q} is entailed iff {@code q ∈ r(p)}, or
 * {@code q} is top, or {@code p} is empty, and {@code p} is empty iff
 * {@code bottom ∈ r(p)} or the domains collected over {@code r(p)} contain an
 * unsatisfiable class, or the ranges over {@code r(p)} name two different
 * datatypes (the last case is not decided here and refuses). The argument is
 * a model construction. If {@code p} is not empty by these rules and
 * {@code q ∉ r(p)}, take a model of the ontology (it exists: the
 * classification found it consistent) and add one pair {@code (x, l)} to
 * {@code p} and to every property of {@code r(p)}, with {@code x} in the
 * conjunction of the domains over {@code r(p)} and {@code l} in their one
 * datatype. The domains form a chain in the taxonomy (checked), so the
 * conjunction is the most specific one, which is satisfiable, so some element
 * of the model lies in it. The pair is in {@code p} but not in {@code q}.
 * Two things must hold for the extended interpretation to be a model.
 * (1) Functionality: {@code x} must have no data value for a functional
 * property of {@code r(p)}. Take the disjoint union of the model with a copy
 * of itself in which every element has no data value and no named individual
 * is interpreted (the named individuals stay in the original part), and let
 * {@code x} be the copy of an element of the conjunction. Without nominals
 * every class expression is satisfied by an element of the copy exactly as by
 * the original (the copy has the same object property and class structure),
 * so {@code x} lies in the conjunction, and every axiom of the ontology still
 * holds: assertions concern named individuals only, and the fragment's data
 * axioms are satisfied by empty data property extensions in the copy. With a
 * nominal this fails (for {@code D ≡ {a}} the only element of {@code D} is
 * {@code a}, which may carry a forced value) and the model refuses when a
 * functional property exists. Without functional properties {@code x} may be
 * any element of the conjunction, named or not, because adding a pair
 * violates no axiom. (2) No other axiom mentions a data property, so none can
 * fail; the sub-property axioms hold because the pair was added to all of
 * {@code r(p)}, and the range holds by the choice of {@code l}.
 *
 * <p>Domains follow the same way: {@code ∃p.rdfs:Literal ⊑ C} holds iff
 * {@code p} is empty, or {@code C} is a super class of the most specific
 * domain over {@code r(p)}, or {@code C} is owl:Thing. The hierarchy has
 * the shape of HermiT's: the top node holds {@code owl:topDataProperty} and
 * the properties equivalent to it, the bottom node holds
 * {@code owl:bottomDataProperty} and the empty properties, a node without
 * super nodes sits below the top node, a node without sub nodes sits above
 * the bottom node.
 */
final class DataPropertyModel {

    /** What the model needs to know about the class taxonomy of the same revision. */
    interface Taxonomy {
        /** Representative id of a named class in the taxonomy, or -1 when unknown. */
        int rep(OWLClass c);
        /** Whether the representative is the bottom node. */
        boolean isUnsatisfiable(int rep);
        /** Whether {@code sub ⊑ sup} for two representatives. */
        boolean below(int sub, int sup);
    }

    /** Codes of properties that are not in the model's index. */
    static final int TOP = -1;
    static final int BOTTOM = -2;
    static final int FRESH = -3;

    private static final int TOP_NODE = 0;
    private static final int BOTTOM_NODE = 1;
    private static final int TOP_ID = 0;
    private static final int BOTTOM_ID = 1;

    private final OWLDataFactory df;
    /** Index 0 and 1 are top and bottom; the named properties start at 2. */
    private final List<OWLDataProperty> props = new ArrayList<>();
    private final Map<OWLDataProperty, Integer> index = new HashMap<>();
    private BitSet[] reach;
    private boolean[] empty;
    /** The most specific domain class representative per property; -1 when none. */
    private int[] domainRep;
    private int[] nodeOf;
    private final List<List<Integer>> members = new ArrayList<>();
    private final List<BitSet> ancestors = new ArrayList<>();
    private final List<BitSet> parents = new ArrayList<>();
    private final List<BitSet> descendants = new ArrayList<>();
    private final List<BitSet> children = new ArrayList<>();
    private final Map<Integer, Node<OWLDataProperty>> nodeCache = new HashMap<>();

    private DataPropertyModel(OWLDataFactory df) {
        this.df = df;
        add(df.getOWLTopDataProperty());
        add(df.getOWLBottomDataProperty());
    }

    private int add(OWLDataProperty p) {
        Integer at = index.get(p);
        if (at != null) return at;
        index.put(p, props.size());
        props.add(p);
        return props.size() - 1;
    }

    // ---- the fragment ----------------------------------------------------

    /**
     * Why the ontology is outside the fragment, or null when it is inside.
     * The check is syntactic and cheap; the model may still refuse on the
     * taxonomy (incomparable domains).
     */
    static String outsideFragment(OWLOntology ontology) {
        String nominal = functionalWithNominals(ontology);
        if (nominal != null) return nominal;
        for (OWLDataProperty p : ontology.getDataPropertiesInSignature(Imports.INCLUDED)) {
            boolean special = p.isOWLTopDataProperty() || p.isOWLBottomDataProperty();
            for (OWLAxiom axiom : ontology.getReferencingAxioms(p, Imports.INCLUDED)) {
                String why = whyOutside(axiom, special);
                if (why != null) return why;
            }
        }
        return null;
    }

    /** A functional data property next to a nominal or a rule: the witness argument needs an unnamed element. */
    private static String functionalWithNominals(OWLOntology ontology) {
        boolean functional = false;
        for (OWLOntology o : ontology.getImportsClosure()) {
            if (!o.getAxioms(AxiomType.FUNCTIONAL_DATA_PROPERTY).isEmpty()) {
                functional = true;
                break;
            }
        }
        if (!functional) return null;
        for (OWLOntology o : ontology.getImportsClosure()) {
            for (OWLAxiom axiom : o.getLogicalAxioms()) {
                if (axiom instanceof SWRLRule) return "a functional data property and the rule " + axiom;
                for (OWLClassExpression ce : axiom.getNestedClassExpressions()) {
                    if (ce instanceof OWLObjectOneOf || ce instanceof OWLObjectHasValue || ce instanceof OWLDataHasValue) {
                        return "a functional data property and the nominal in " + axiom;
                    }
                }
            }
        }
        return null;
    }

    private static String whyOutside(OWLAxiom axiom, boolean special) {
        if (!axiom.isLogicalAxiom()) return null;
        if (axiom instanceof OWLSubDataPropertyOfAxiom || axiom instanceof OWLEquivalentDataPropertiesAxiom
                || axiom instanceof OWLDataPropertyAssertionAxiom) {
            return null;
        }
        if (!special) {
            if (axiom instanceof OWLFunctionalDataPropertyAxiom) return null;
            if (axiom instanceof OWLDataPropertyDomainAxiom) {
                if (!((OWLDataPropertyDomainAxiom) axiom).getDomain().isAnonymous()) return null;
            } else if (axiom instanceof OWLDataPropertyRangeAxiom) {
                OWLDataRange range = ((OWLDataPropertyRangeAxiom) axiom).getRange();
                if (range instanceof OWLDatatype && OWL2Datatype.isBuiltIn(((OWLDatatype) range).getIRI())) return null;
            }
        }
        return "the axiom " + axiom + " mentions a data property";
    }

    // ---- construction ---------------------------------------------------------

    /**
     * Build the model from the committed snapshot and the taxonomy.
     *
     * @throws UnsupportedOperationException outside the fragment, or when the
     *         domains or ranges over a property's super properties cannot be combined
     */
    static DataPropertyModel build(OWLDataFactory df, OWLOntology snapshot, Taxonomy taxonomy) {
        String why = outsideFragment(snapshot);
        if (why != null) {
            throw new UnsupportedOperationException(
                    "Kobayashi-MaRust computes the data property hierarchy only when the data properties occur in"
                            + " sub-property, equivalence, assertion, functionality, domain and range axioms; " + why);
        }
        DataPropertyModel m = new DataPropertyModel(df);
        List<OWLDataProperty> sig = new ArrayList<>(snapshot.getDataPropertiesInSignature(Imports.INCLUDED));
        sig.sort(Comparator.comparing(p -> p.getIRI().toString()));
        for (OWLDataProperty p : sig) m.add(p);
        int n = m.props.size();
        BitSet[] edge = new BitSet[n];
        for (int i = 0; i < n; i++) {
            edge[i] = new BitSet(n);
            edge[i].set(i);
        }
        List<List<OWLClass>> domains = new ArrayList<>();
        List<Set<IRI>> ranges = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            domains.add(new ArrayList<>());
            ranges.add(new TreeSet<>());
        }
        for (OWLAxiom axiom : snapshot.getAxioms()) {
            if (axiom instanceof OWLSubDataPropertyOfAxiom) {
                OWLSubDataPropertyOfAxiom a = (OWLSubDataPropertyOfAxiom) axiom;
                edge[m.id(a.getSubProperty())].set(m.id(a.getSuperProperty()));
            } else if (axiom instanceof OWLEquivalentDataPropertiesAxiom) {
                List<OWLDataPropertyExpression> eq = new ArrayList<>(
                        ((OWLEquivalentDataPropertiesAxiom) axiom).getProperties());
                for (int i = 0; i < eq.size(); i++) {
                    int a = m.id(eq.get(i)), b = m.id(eq.get((i + 1) % eq.size()));
                    edge[a].set(b);
                    edge[b].set(a);
                }
            } else if (axiom instanceof OWLDataPropertyDomainAxiom) {
                OWLDataPropertyDomainAxiom a = (OWLDataPropertyDomainAxiom) axiom;
                domains.get(m.id(a.getProperty())).add(a.getDomain().asOWLClass());
            } else if (axiom instanceof OWLDataPropertyRangeAxiom) {
                OWLDataPropertyRangeAxiom a = (OWLDataPropertyRangeAxiom) axiom;
                IRI datatype = ((OWLDatatype) a.getRange()).getIRI();
                if (!datatype.equals(OWL2Datatype.RDFS_LITERAL.getIRI())) ranges.get(m.id(a.getProperty())).add(datatype);
            }
        }
        // Reflexive and transitive closure over the stated edges (n is the property count; BFS per property).
        m.reach = new BitSet[n];
        for (int i = 0; i < n; i++) {
            BitSet seen = new BitSet(n);
            Deque<Integer> todo = new ArrayDeque<>();
            seen.set(i);
            todo.add(i);
            while (!todo.isEmpty()) {
                int x = todo.poll();
                for (int y = edge[x].nextSetBit(0); y >= 0; y = edge[x].nextSetBit(y + 1)) {
                    if (!seen.get(y)) {
                        seen.set(y);
                        todo.add(y);
                    }
                }
            }
            m.reach[i] = seen;
        }
        if (m.reach[TOP_ID].get(BOTTOM_ID)) {
            throw new UnsupportedOperationException(
                    "owl:topDataProperty is stated to be a sub property of owl:bottomDataProperty");
        }
        m.empty = new boolean[n];
        m.domainRep = new int[n];
        Arrays.fill(m.domainRep, -1);
        for (int p = 2; p < n; p++) {
            BitSet up = m.reach[p];
            if (up.get(BOTTOM_ID)) {
                m.empty[p] = true;
                continue;
            }
            Set<IRI> datatypes = new TreeSet<>();
            List<Integer> reps = new ArrayList<>();
            for (int q = up.nextSetBit(0); q >= 0; q = up.nextSetBit(q + 1)) {
                datatypes.addAll(ranges.get(q));
                for (OWLClass c : domains.get(q)) {
                    int rep = taxonomy.rep(c);
                    if (rep < 0) {
                        throw new UnsupportedOperationException("the domain class " + c + " of "
                                + m.props.get(q) + " is not in the class taxonomy");
                    }
                    reps.add(rep);
                }
            }
            if (datatypes.size() > 1) {
                throw new UnsupportedOperationException("the ranges of " + m.props.get(p) + " and its super"
                        + " properties name the datatypes " + datatypes + "; their intersection is not decided");
            }
            boolean unsatisfiableDomain = false;
            for (int rep : reps) if (taxonomy.isUnsatisfiable(rep)) unsatisfiableDomain = true;
            if (unsatisfiableDomain) {
                m.empty[p] = true;
                continue;
            }
            int lowest = -1;
            for (int rep : reps) {
                if (lowest < 0 || taxonomy.below(rep, lowest)) {
                    lowest = rep;
                } else if (!taxonomy.below(lowest, rep)) {
                    throw new UnsupportedOperationException("the domains of " + m.props.get(p)
                            + " and its super properties are not comparable classes; their intersection is not decided");
                }
            }
            // A chain: every other domain is above the lowest one.
            for (int rep : reps) {
                if (!taxonomy.below(lowest, rep)) {
                    throw new UnsupportedOperationException("the domains of " + m.props.get(p)
                            + " and its super properties are not comparable classes; their intersection is not decided");
                }
            }
            m.domainRep[p] = lowest;
        }
        m.buildHierarchy();
        return m;
    }

    private int id(OWLDataPropertyExpression e) {
        return index.get(e.asOWLDataProperty());
    }

    // ---- hierarchy ---------------------------------------------------------------

    private boolean universalProperty(int p) {
        return p >= 2 && reach[TOP_ID].get(p);
    }

    private void buildHierarchy() {
        int n = props.size();
        nodeOf = new int[n];
        Arrays.fill(nodeOf, -1);
        members.add(new ArrayList<>());
        members.add(new ArrayList<>());
        for (int p = 2; p < n; p++) {
            if (empty[p] || universalProperty(p) || nodeOf[p] >= 0) continue;
            int node = members.size();
            List<Integer> group = new ArrayList<>();
            group.add(p);
            nodeOf[p] = node;
            for (int q = reach[p].nextSetBit(p + 1); q >= 0; q = reach[p].nextSetBit(q + 1)) {
                if (q >= 2 && !empty[q] && !universalProperty(q) && nodeOf[q] < 0 && reach[q].get(p)) {
                    nodeOf[q] = node;
                    group.add(q);
                }
            }
            members.add(group);
        }
        for (int p = 2; p < n; p++) {
            if (universalProperty(p)) members.get(TOP_NODE).add(p);
            else if (empty[p]) members.get(BOTTOM_NODE).add(p);
        }
        int count = members.size();
        for (int c = 0; c < count; c++) {
            ancestors.add(new BitSet(count));
            parents.add(new BitSet(count));
            descendants.add(new BitSet(count));
            children.add(new BitSet(count));
        }
        for (int c = 2; c < count; c++) {
            for (int p : members.get(c)) {
                for (int q = reach[p].nextSetBit(0); q >= 0; q = reach[p].nextSetBit(q + 1)) {
                    if (q >= 2 && nodeOf[q] >= 2 && nodeOf[q] != c) ancestors.get(c).set(nodeOf[q]);
                }
            }
        }
        for (int c = 2; c < count; c++) {
            BitSet beyond = new BitSet(count);
            BitSet anc = ancestors.get(c);
            for (int a = anc.nextSetBit(0); a >= 0; a = anc.nextSetBit(a + 1)) beyond.or(ancestors.get(a));
            BitSet direct = (BitSet) anc.clone();
            direct.andNot(beyond);
            if (direct.isEmpty()) direct.set(TOP_NODE);
            parents.get(c).or(direct);
            for (int p = direct.nextSetBit(0); p >= 0; p = direct.nextSetBit(p + 1)) children.get(p).set(c);
            for (int a = anc.nextSetBit(0); a >= 0; a = anc.nextSetBit(a + 1)) descendants.get(a).set(c);
        }
        for (int c = 2; c < count; c++) {
            if (children.get(c).isEmpty()) {
                children.get(c).set(BOTTOM_NODE);
                parents.get(BOTTOM_NODE).set(c);
            }
        }
        if (count == 2) {
            children.get(TOP_NODE).set(BOTTOM_NODE);
            parents.get(BOTTOM_NODE).set(TOP_NODE);
        }
    }

    // ---- queries ------------------------------------------------------------------

    /** The index of the property, {@link #TOP}, {@link #BOTTOM}, or {@link #FRESH} outside the signature. */
    int code(OWLDataProperty p) {
        if (p.isOWLTopDataProperty()) return TOP;
        if (p.isOWLBottomDataProperty()) return BOTTOM;
        Integer i = index.get(p);
        return i == null ? FRESH : i;
    }

    private int nodeIndex(int code) {
        if (code == TOP) return TOP_NODE;
        if (code == BOTTOM) return BOTTOM_NODE;
        if (code == FRESH) return -1;
        if (universalProperty(code)) return TOP_NODE;
        if (empty[code]) return BOTTOM_NODE;
        return nodeOf[code];
    }

    /** Whether the property is in the bottom node (owl:bottomDataProperty included). */
    boolean isEmpty(OWLDataProperty p) {
        int code = code(p);
        return code == BOTTOM || (code >= 0 && empty[code]);
    }

    /** Whether the property is in the top node. */
    boolean isUniversal(OWLDataProperty p) {
        int code = code(p);
        return code == TOP || (code >= 0 && universalProperty(code));
    }

    /**
     * The representative of the most specific domain class of a property that is
     * not empty, or -1 when owl:Thing is its only known domain.
     */
    int domainRep(OWLDataProperty p) {
        int code = code(p);
        return code >= 0 && !empty[code] ? domainRep[code] : -1;
    }

    private Node<OWLDataProperty> node(int c) {
        Node<OWLDataProperty> cached = nodeCache.get(c);
        if (cached != null) return cached;
        Set<OWLDataProperty> set = new HashSet<>();
        if (c == TOP_NODE) set.add(df.getOWLTopDataProperty());
        if (c == BOTTOM_NODE) set.add(df.getOWLBottomDataProperty());
        for (int p : members.get(c)) set.add(props.get(p));
        Node<OWLDataProperty> built = new OWLDataPropertyNode(set);
        nodeCache.put(c, built);
        return built;
    }

    private NodeSet<OWLDataProperty> nodeSet(BitSet nodes) {
        Set<Node<OWLDataProperty>> out = new HashSet<>();
        for (int c = nodes.nextSetBit(0); c >= 0; c = nodes.nextSetBit(c + 1)) out.add(node(c));
        return new OWLDataPropertyNodeSet(out);
    }

    Node<OWLDataProperty> topNode() { return node(TOP_NODE); }

    Node<OWLDataProperty> bottomNode() { return node(BOTTOM_NODE); }

    Node<OWLDataProperty> equivalents(OWLDataProperty p) {
        int idx = nodeIndex(code(p));
        return idx < 0 ? new OWLDataPropertyNode(p) : node(idx);
    }

    NodeSet<OWLDataProperty> supers(OWLDataProperty p, boolean direct) {
        int idx = nodeIndex(code(p));
        BitSet out = new BitSet();
        if (idx < 0) {
            out.set(TOP_NODE);
        } else if (idx == TOP_NODE) {
            // nothing above
        } else if (idx == BOTTOM_NODE) {
            if (direct) {
                out.or(parents.get(BOTTOM_NODE));
            } else {
                for (int c = 0; c < members.size(); c++) if (c != BOTTOM_NODE) out.set(c);
            }
        } else if (direct) {
            out.or(parents.get(idx));
        } else {
            out.or(ancestors.get(idx));
            out.set(TOP_NODE);
        }
        return nodeSet(out);
    }

    NodeSet<OWLDataProperty> subs(OWLDataProperty p, boolean direct) {
        int idx = nodeIndex(code(p));
        BitSet out = new BitSet();
        if (idx < 0) {
            out.set(BOTTOM_NODE);
        } else if (idx == BOTTOM_NODE) {
            // nothing below
        } else if (idx == TOP_NODE) {
            if (direct) {
                out.or(children.get(TOP_NODE));
            } else {
                for (int c = 1; c < members.size(); c++) out.set(c);
            }
        } else if (direct) {
            out.or(children.get(idx));
        } else {
            out.or(descendants.get(idx));
            out.set(BOTTOM_NODE);
        }
        return nodeSet(out);
    }

    boolean isFresh(OWLDataProperty p) { return code(p) == FRESH; }

    /** A node set holding the bottom node alone. */
    NodeSet<OWLDataProperty> bottomOnly() {
        BitSet only = new BitSet();
        only.set(BOTTOM_NODE);
        return nodeSet(only);
    }

    /** Every node, the top and the bottom node included. */
    NodeSet<OWLDataProperty> allNodes() {
        BitSet all = new BitSet();
        all.set(0, members.size());
        return nodeSet(all);
    }
}
