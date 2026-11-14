package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNode;
import org.semanticweb.owlapi.reasoner.impl.OWLObjectPropertyNodeSet;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The entailed object property hierarchy of one ontology revision, built from
 * the rows of {@code km classify --lines --properties} (docs/PROPERTIES.md).
 *
 * <p><b>Expressions.</b> The named object properties {@code p_0 .. p_(n-1)}
 * give {@code 2n} expressions: {@code 2i} is {@code p_i} and {@code 2i+1} is
 * {@code ObjectInverseOf(p_i)}. Flipping the lowest bit takes the inverse.
 *
 * <p><b>Derivation of the order.</b> Every row {@code SUBPROP r f} states
 * {@code r ⊑ f} for a named {@code r} and any expression {@code f}. Inverse is
 * monotone: {@code e ⊑ f} iff {@code e⁻ ⊑ f⁻}. So each row also gives
 * {@code r⁻ ⊑ f⁻}, and together the two cover every pair whose left side is
 * named or inverse (for example {@code r⁻ ⊑ s} comes from the row
 * {@code r ⊑ s⁻}). The relation {@code up[e]} holds every {@code f} with
 * {@code e ⊑ f}, plus {@code e} itself. KM lists all entailed pairs, so
 * {@code up} is already transitive.
 *
 * <p>Empty expressions ({@code BOTPROP}, and their inverses) sit in the bottom
 * node and universal ones ({@code TOPPROP}, and their inverses) in the top
 * node, as in HermiT's role hierarchy (Reasoner.classifyObjectProperties maps
 * the top and bottom roles to owl:Thing and owl:Nothing, so a property
 * equivalent to either joins that node). The other expressions group by
 * mutual subsumption into nodes. A node's parents are its direct supers; a
 * node without any has the top node as parent, and a node without children
 * has the bottom node as child.
 *
 * <p><b>Inverse expressions.</b> HermiT only puts inverse roles into the
 * hierarchy when the ontology uses inverse roles
 * ({@code DLOntology.hasInverseRoles}); otherwise {@code ObjectInverseOf(r)}
 * is a node of its own between top and bottom
 * (Reasoner.getHierarchyNode, the {@code node==null} case). The model does
 * the same: {@code hasInverse} is false in that case and the hierarchy is
 * built over the named properties only.
 */
final class ObjectPropertyModel {

    /** Codes of expressions that are not a named property of the signature. */
    static final int TOP = -1;
    static final int BOTTOM = -2;
    static final int FRESH = -3;

    private static final int TOP_NODE = 0;
    private static final int BOTTOM_NODE = 1;

    private final OWLDataFactory df;
    private final List<OWLObjectProperty> props = new ArrayList<>();
    private final Map<OWLObjectProperty, Integer> index = new HashMap<>();
    private final boolean hasInverse;
    private BitSet[] up;
    private boolean[] empty;
    private boolean[] universal;
    /** Class IRIs of DOMAIN rows per expression; a RANGE row belongs to the inverse expression. */
    private final Map<Integer, List<String>> domainIris = new HashMap<>();

    /** Node index of each expression, or -1 when it has none (empty, universal, hidden inverse). */
    private int[] nodeOf;
    private final List<List<Integer>> members = new ArrayList<>();
    private final List<BitSet> ancestors = new ArrayList<>();
    private final List<BitSet> parents = new ArrayList<>();
    private final List<BitSet> descendants = new ArrayList<>();
    private final List<BitSet> children = new ArrayList<>();
    private final Map<Integer, Node<OWLObjectPropertyExpression>> nodeCache = new HashMap<>();

    ObjectPropertyModel(OWLDataFactory df, Iterable<OWLObjectProperty> signature,
                        Classifier.Properties rows, boolean hasInverse) {
        this.df = df;
        this.hasInverse = hasInverse;
        for (OWLObjectProperty p : signature) {
            if (!p.isOWLTopObjectProperty() && !p.isOWLBottomObjectProperty()) add(p);
        }
        // A property that only the rows mention still gets an index.
        if (rows != null) {
            for (String[] row : rows.subproperties) {
                add(parseExpression(row[0]).getNamedProperty().asOWLObjectProperty());
                add(parseExpression(row[1]).getNamedProperty().asOWLObjectProperty());
            }
            for (String name : rows.top) add(parseExpression(name).getNamedProperty().asOWLObjectProperty());
            for (String name : rows.bottom) add(parseExpression(name).getNamedProperty().asOWLObjectProperty());
            for (String[] row : rows.domains) add(parseExpression(row[0]).getNamedProperty().asOWLObjectProperty());
            for (String[] row : rows.ranges) add(parseExpression(row[0]).getNamedProperty().asOWLObjectProperty());
        }
        int n = 2 * props.size();
        up = new BitSet[n];
        for (int e = 0; e < n; e++) {
            up[e] = new BitSet(n);
            up[e].set(e);
        }
        empty = new boolean[n];
        universal = new boolean[n];
        if (rows != null) {
            for (String[] row : rows.subproperties) {
                int a = expr(row[0]);
                int b = expr(row[1]);
                if (a < 0 || b < 0) continue;
                up[a].set(b);
                up[a ^ 1].set(b ^ 1);
            }
            for (String name : rows.top) {
                int e = expr(name);
                if (e >= 0) { universal[e] = true; universal[e ^ 1] = true; }
            }
            for (String name : rows.bottom) {
                int e = expr(name);
                if (e >= 0) { empty[e] = true; empty[e ^ 1] = true; }
            }
            for (String[] row : rows.domains) {
                int e = expr(row[0]);
                if (e >= 0) domainIris.computeIfAbsent(e, k -> new ArrayList<>()).add(stripIri(row[1]));
            }
            for (String[] row : rows.ranges) {
                int e = expr(row[0]);
                if (e >= 0) domainIris.computeIfAbsent(e ^ 1, k -> new ArrayList<>()).add(stripIri(row[1]));
            }
        }
        buildHierarchy();
    }

    private void add(OWLObjectProperty p) {
        if (!index.containsKey(p)) {
            index.put(p, props.size());
            props.add(p);
        }
    }

    private static String stripIri(String name) {
        String s = name.trim();
        if (s.length() >= 2 && s.charAt(0) == '<' && s.charAt(s.length() - 1) == '>') {
            return s.substring(1, s.length() - 1);
        }
        return s;
    }

    /** {@code <iri>} or {@code ObjectInverseOf(<iri>)} as an expression. */
    private OWLObjectPropertyExpression parseExpression(String text) {
        String s = text.trim();
        if (s.startsWith("ObjectInverseOf(") && s.endsWith(")")) {
            String inner = s.substring("ObjectInverseOf(".length(), s.length() - 1);
            return df.getOWLObjectInverseOf(df.getOWLObjectProperty(IRI.create(stripIri(inner))));
        }
        return df.getOWLObjectProperty(IRI.create(stripIri(s)));
    }

    /** Index of a row expression: {@code 2i} or {@code 2i+1}; -1 if unknown. */
    private int expr(String text) {
        OWLObjectPropertyExpression pe = parseExpression(text);
        Integer i = index.get(pe.getNamedProperty().asOWLObjectProperty());
        if (i == null) return -1;
        return 2 * i + (pe.isAnonymous() ? 1 : 0);
    }

    private boolean visible(int e) {
        return hasInverse || (e & 1) == 0;
    }

    /**
     * Code of a queried expression: its index, {@link #TOP} or {@link #BOTTOM}
     * (also for their inverses, which equal them), or {@link #FRESH} when the
     * named property is outside the signature.
     */
    int code(OWLObjectPropertyExpression pe) {
        OWLObjectPropertyExpression simple = pe.getSimplified();
        OWLObjectProperty named = simple.getNamedProperty().asOWLObjectProperty();
        if (named.isOWLTopObjectProperty()) return TOP;
        if (named.isOWLBottomObjectProperty()) return BOTTOM;
        Integer i = index.get(named);
        if (i == null) return FRESH;
        return 2 * i + (simple.isAnonymous() ? 1 : 0);
    }

    /** The code of the inverse expression. */
    static int inverse(int code) {
        return code >= 0 ? code ^ 1 : code;
    }

    boolean hasInverseRoles() { return hasInverse; }

    boolean isEmpty(int code) {
        return code == BOTTOM || (code >= 0 && empty[code]);
    }

    boolean isUniversal(int code) {
        return code == TOP || (code >= 0 && universal[code]);
    }

    /** Class IRIs listed as domain of the expression (rows only; no owl:Thing). */
    List<String> domainIris(int code) {
        List<String> out = code >= 0 ? domainIris.get(code) : null;
        return out == null ? new ArrayList<>() : out;
    }

    /**
     * Whether {@code sub ⊑ sup} is entailed, for query expressions given by
     * their codes. A fresh expression is only below itself, below a universal
     * expression and, if empty, below everything, the answer HermiT's
     * tableau test gives (Reasoner.isSubObjectPropertyExpressionOf).
     */
    boolean entails(OWLObjectPropertyExpression subExpr, OWLObjectPropertyExpression supExpr) {
        int a = code(subExpr);
        int b = code(supExpr);
        if (a == BOTTOM || b == TOP) return true;
        if (a == FRESH || b == FRESH) {
            if (a == FRESH && b == FRESH) {
                return subExpr.getSimplified().equals(supExpr.getSimplified());
            }
            return a == FRESH ? isUniversal(b) : isEmpty(a);
        }
        if (a == TOP) return isUniversal(b);
        if (b == BOTTOM) return isEmpty(a);
        return empty[a] || universal[b] || up[a].get(b);
    }

    // ---- hierarchy ------------------------------------------------------

    private void buildHierarchy() {
        int n = 2 * props.size();
        nodeOf = new int[n];
        java.util.Arrays.fill(nodeOf, -1);
        // Two nodes first: top and bottom.
        members.add(new ArrayList<>());
        members.add(new ArrayList<>());
        // Equivalence classes of the other visible expressions by mutual subsumption.
        for (int e = 0; e < n; e++) {
            if (!visible(e) || empty[e] || universal[e] || nodeOf[e] >= 0) continue;
            int node = members.size();
            List<Integer> group = new ArrayList<>();
            group.add(e);
            nodeOf[e] = node;
            for (int f = up[e].nextSetBit(e + 1); f >= 0; f = up[e].nextSetBit(f + 1)) {
                if (f < n && visible(f) && !empty[f] && !universal[f] && nodeOf[f] < 0 && up[f].get(e)) {
                    nodeOf[f] = node;
                    group.add(f);
                }
            }
            members.add(group);
        }
        int count = members.size();
        for (int e = 0; e < n; e++) {
            if (!visible(e)) continue;
            if (universal[e]) members.get(TOP_NODE).add(e);
            else if (empty[e]) members.get(BOTTOM_NODE).add(e);
        }
        for (int c = 0; c < count; c++) {
            ancestors.add(new BitSet(count));
            parents.add(new BitSet(count));
            descendants.add(new BitSet(count));
            children.add(new BitSet(count));
        }
        // Strict ancestors among the regular nodes.
        for (int c = 2; c < count; c++) {
            for (int e : members.get(c)) {
                for (int f = up[e].nextSetBit(0); f >= 0; f = up[e].nextSetBit(f + 1)) {
                    if (f < n && nodeOf[f] >= 2 && nodeOf[f] != c) ancestors.get(c).set(nodeOf[f]);
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

    // ---- nodes ----------------------------------------------------------

    private OWLObjectPropertyExpression expression(int e) {
        OWLObjectProperty p = props.get(e >> 1);
        return (e & 1) == 0 ? p : df.getOWLObjectInverseOf(p);
    }

    private Node<OWLObjectPropertyExpression> node(int c) {
        Node<OWLObjectPropertyExpression> cached = nodeCache.get(c);
        if (cached != null) return cached;
        Set<OWLObjectPropertyExpression> set = new HashSet<>();
        if (c == TOP_NODE) set.add(df.getOWLTopObjectProperty());
        if (c == BOTTOM_NODE) set.add(df.getOWLBottomObjectProperty());
        for (int e : members.get(c)) set.add(expression(e));
        Node<OWLObjectPropertyExpression> built = new OWLObjectPropertyNode(set);
        nodeCache.put(c, built);
        return built;
    }

    private NodeSet<OWLObjectPropertyExpression> nodeSet(BitSet nodes) {
        Set<Node<OWLObjectPropertyExpression>> out = new HashSet<>();
        for (int c = nodes.nextSetBit(0); c >= 0; c = nodes.nextSetBit(c + 1)) out.add(node(c));
        return new OWLObjectPropertyNodeSet(out);
    }

    /** Node of the expression, or -1 for a fresh or hidden expression (a node of its own). */
    private int nodeIndex(int code) {
        if (code == TOP) return TOP_NODE;
        if (code == BOTTOM) return BOTTOM_NODE;
        if (code == FRESH) return -1;
        // An inverse expression of an ontology without inverse roles is no element of
        // HermiT's hierarchy, even when its property is empty or universal.
        if (!visible(code)) return -1;
        if (universal[code]) return TOP_NODE;
        if (empty[code]) return BOTTOM_NODE;
        return nodeOf[code];
    }

    /** Every node, the top and the bottom node included. */
    NodeSet<OWLObjectPropertyExpression> allNodes() {
        BitSet all = new BitSet();
        all.set(0, members.size());
        return nodeSet(all);
    }

    /** Number of nodes; node 0 is the top node, node 1 the bottom node. */
    int nodeCount() { return members.size(); }

    Node<OWLObjectPropertyExpression> nodeAt(int c) { return node(c); }

    /** One expression of a node other than top and bottom (every member is equivalent). */
    OWLObjectPropertyExpression representative(int c) {
        return members.get(c).isEmpty() ? null : expression(members.get(c).get(0));
    }

    Node<OWLObjectPropertyExpression> topNode() { return node(TOP_NODE); }

    Node<OWLObjectPropertyExpression> bottomNode() { return node(BOTTOM_NODE); }

    Node<OWLObjectPropertyExpression> equivalents(OWLObjectPropertyExpression pe) {
        int idx = nodeIndex(code(pe));
        return idx < 0 ? new OWLObjectPropertyNode(pe.getSimplified()) : node(idx);
    }

    NodeSet<OWLObjectPropertyExpression> supers(OWLObjectPropertyExpression pe, boolean direct) {
        int idx = nodeIndex(code(pe));
        BitSet out = new BitSet();
        if (idx < 0) {
            // Between top and bottom (HermiT's synthetic node).
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

    NodeSet<OWLObjectPropertyExpression> subs(OWLObjectPropertyExpression pe, boolean direct) {
        int idx = nodeIndex(code(pe));
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
}
