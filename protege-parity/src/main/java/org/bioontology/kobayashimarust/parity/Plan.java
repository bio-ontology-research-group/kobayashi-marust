package org.bioontology.kobayashimarust.parity;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.vocab.OWL2Datatype;

import java.util.*;
import java.util.function.Function;

/**
 * The list of OWLReasoner calls that both reasoners answer. The plan depends
 * only on the ontology and the seed, so the HermiT worker and the KM worker
 * build the same list in separate processes and the parent can match their
 * answers by call id.
 */
final class Plan {

    /** One reasoner call. */
    static final class Call {
        final String id;
        final String method;
        final String phase;
        final Function<OWLReasoner, Object> fn;
        /** Marks calls whose answer differs by nature (names, versions); not compared. */
        final boolean info;

        Call(String phase, String method, String args, boolean info, Function<OWLReasoner, Object> fn) {
            this.id = method + "(" + args + ")";
            this.method = method;
            this.phase = phase;
            this.info = info;
            this.fn = fn;
        }
    }

    static final String CREATE = "create";
    static final String CONSISTENCY = "consistency";
    static final String PRECOMPUTE = "precompute";
    static final String CLASSES = "classes";
    static final String CLASS_EXPR = "class_expr";
    static final String OBJECT_PROPS = "object_props";
    static final String DATA_PROPS = "data_props";
    static final String INDIVIDUALS = "individuals";
    static final String VALUES = "property_values";
    static final String ENTAILMENT = "entailment";
    static final String META = "meta";
    /** Disjointness and different-individual queries: slow in HermiT, run last. */
    static final String DISJOINT = "disjoint";
    static final List<String> ORDER = Arrays.asList(META, CONSISTENCY, PRECOMPUTE, CLASSES, INDIVIDUALS,
            OBJECT_PROPS, DATA_PROPS, VALUES, ENTAILMENT, CLASS_EXPR, DISJOINT);

    /** Queries that cost HermiT one tableau test per entity are asked for this many entities only. */
    static final int DISJOINT_CAP = 6;

    final List<Call> calls = new ArrayList<>();
    final Map<String, Integer> signature = new LinkedHashMap<>();

    private final OWLOntology ont;
    private final OWLDataFactory df;
    private final long seed;
    private final int sample;

    Plan(OWLOntology ont, long seed, int sample) {
        this.ont = ont;
        this.df = ont.getOWLOntologyManager().getOWLDataFactory();
        this.seed = seed;
        this.sample = sample;
        build();
    }

    static String name(Object o) {
        if (o instanceof OWLObjectInverseOf) {
            return "inv(" + ((OWLObjectInverseOf) o).getInverse().asOWLObjectProperty().getIRI() + ")";
        }
        if (o instanceof OWLEntity) return ((OWLEntity) o).getIRI().toString();
        if (o instanceof OWLLiteral) return o.toString();
        return String.valueOf(o);
    }

    private <T extends OWLEntity> List<T> sorted(Collection<T> in) {
        List<T> out = new ArrayList<>(in);
        out.sort(Comparator.comparing(e -> e.getIRI().toString()));
        return out;
    }

    /** Deterministic sample of at most n elements, kept in sorted order. */
    private <T extends OWLEntity> List<T> pick(List<T> all, int n, String kind) {
        if (all.size() <= n) return all;
        List<T> copy = new ArrayList<>(all);
        Collections.shuffle(copy, new Random(seed * 31 + kind.hashCode()));
        List<T> out = new ArrayList<>(copy.subList(0, n));
        out.sort(Comparator.comparing(e -> e.getIRI().toString()));
        return out;
    }

    private void add(String phase, String method, String args, Function<OWLReasoner, Object> fn) {
        calls.add(new Call(phase, method, args, false, fn));
    }

    private void info(String phase, String method, String args, Function<OWLReasoner, Object> fn) {
        calls.add(new Call(phase, method, args, true, fn));
    }

    private void build() {
        Set<OWLOntology> closure = ont.getImportsClosure();
        Set<OWLClass> cs = new HashSet<>();
        Set<OWLObjectProperty> ops = new HashSet<>();
        Set<OWLDataProperty> dps = new HashSet<>();
        Set<OWLNamedIndividual> inds = new HashSet<>();
        for (OWLOntology o : closure) {
            cs.addAll(o.getClassesInSignature());
            ops.addAll(o.getObjectPropertiesInSignature());
            dps.addAll(o.getDataPropertiesInSignature());
            inds.addAll(o.getIndividualsInSignature());
        }
        cs.remove(df.getOWLThing());
        cs.remove(df.getOWLNothing());
        ops.remove(df.getOWLTopObjectProperty());
        ops.remove(df.getOWLBottomObjectProperty());
        dps.remove(df.getOWLTopDataProperty());
        dps.remove(df.getOWLBottomDataProperty());
        signature.put("classes", cs.size());
        signature.put("object_properties", ops.size());
        signature.put("data_properties", dps.size());
        signature.put("individuals", inds.size());
        int axioms = 0;
        for (OWLOntology o : closure) axioms += o.getLogicalAxiomCount();
        signature.put("logical_axioms", axioms);

        List<OWLClass> classes = pick(sorted(cs), sample, "class");
        List<OWLObjectProperty> objProps = pick(sorted(ops), sample, "op");
        List<OWLDataProperty> dataProps = pick(sorted(dps), sample, "dp");
        List<OWLNamedIndividual> indivs = pick(sorted(inds), sample, "ind");
        List<OWLClass> classQ = new ArrayList<>();
        classQ.add(df.getOWLThing());
        classQ.add(df.getOWLNothing());
        classQ.addAll(classes);

        // Metadata and lifecycle.
        info(META, "getReasonerName", "", r -> r.getReasonerName());
        info(META, "getReasonerVersion", "", r -> r.getReasonerVersion().toString());
        add(META, "getBufferingMode", "", r -> r.getBufferingMode().toString());
        // getTimeOut returns the timeout of the configuration the reasoner was created with. HermiT gets its
        // own Configuration here (to set ignoreUnsupportedDatatypes), which reports -1, while KM gets a
        // SimpleConfiguration (Long.MAX_VALUE); both mean "no limit". The two answers are not comparable, so
        // the call is informational. PluginBehaviourTest and ConventionsTest check that KM, like HermiT,
        // returns the configured value.
        info(META, "getTimeOut", "", r -> r.getTimeOut());
        add(META, "getFreshEntityPolicy", "", r -> r.getFreshEntityPolicy().toString());
        add(META, "getIndividualNodeSetPolicy", "", r -> r.getIndividualNodeSetPolicy().toString());
        add(META, "getRootOntology", "", r -> String.valueOf(r.getRootOntology().getOntologyID()));
        add(META, "getPendingChanges", "", r -> sizeOf(r.getPendingChanges()));
        add(META, "getPendingAxiomAdditions", "", r -> sizeOf(r.getPendingAxiomAdditions()));
        add(META, "getPendingAxiomRemovals", "", r -> sizeOf(r.getPendingAxiomRemovals()));
        add(META, "flush", "", r -> { r.flush(); return null; });
        add(META, "interrupt", "idle", r -> { r.interrupt(); return null; });

        // Consistency, then the precomputable inference types.
        add(CONSISTENCY, "isConsistent", "", r -> r.isConsistent());
        add(PRECOMPUTE, "getPrecomputableInferenceTypes", "", r -> sortedStrings(r.getPrecomputableInferenceTypes()));
        for (InferenceType t : InferenceType.values()) {
            add(PRECOMPUTE, "precomputeInferences", t.name(), r -> { r.precomputeInferences(t); return null; });
        }
        for (InferenceType t : InferenceType.values()) {
            add(PRECOMPUTE, "isPrecomputed", t.name(), r -> r.isPrecomputed(t));
        }

        // Class hierarchy.
        add(CLASSES, "getTopClassNode", "", r -> r.getTopClassNode());
        add(CLASSES, "getBottomClassNode", "", r -> r.getBottomClassNode());
        add(CLASSES, "getUnsatisfiableClasses", "", r -> r.getUnsatisfiableClasses());
        for (OWLClass c : classQ) {
            String a = name(c);
            add(CLASSES, "isSatisfiable", a, r -> r.isSatisfiable(c));
            add(CLASSES, "getSubClasses", a + ",true", r -> r.getSubClasses(c, true));
            add(CLASSES, "getSubClasses", a + ",false", r -> r.getSubClasses(c, false));
            add(CLASSES, "getSuperClasses", a + ",true", r -> r.getSuperClasses(c, true));
            add(CLASSES, "getSuperClasses", a + ",false", r -> r.getSuperClasses(c, false));
            add(CLASSES, "getEquivalentClasses", a, r -> r.getEquivalentClasses(c));
            // HermiT runs one tableau test per class here (seconds each), so ask for few.
            if (classQ.indexOf(c) < DISJOINT_CAP) add(DISJOINT, "getDisjointClasses", a, r -> r.getDisjointClasses(c));
        }
        for (OWLClass c : classQ) {
            String a = name(c);
            add(INDIVIDUALS, "getInstances", a + ",true", r -> r.getInstances(c, true));
            add(INDIVIDUALS, "getInstances", a + ",false", r -> r.getInstances(c, false));
        }

        // Anonymous class expressions built from the signature.
        Random rnd = new Random(seed * 17 + 3);
        List<OWLClassExpression> exprs = new ArrayList<>();
        if (!classes.isEmpty()) {
            for (int i = 0; i < 2; i++) {
                OWLClass c = classes.get(rnd.nextInt(classes.size()));
                OWLClass d = classes.get(rnd.nextInt(classes.size()));
                exprs.add(df.getOWLObjectComplementOf(c));
                exprs.add(df.getOWLObjectIntersectionOf(c, d));
                exprs.add(df.getOWLObjectUnionOf(c, d));
                if (!objProps.isEmpty()) {
                    OWLObjectProperty p = objProps.get(rnd.nextInt(objProps.size()));
                    exprs.add(df.getOWLObjectSomeValuesFrom(p, c));
                    exprs.add(df.getOWLObjectAllValuesFrom(p, c));
                    if (i == 0) {
                        exprs.add(df.getOWLObjectSomeValuesFrom(df.getOWLObjectInverseOf(p), c));
                        exprs.add(df.getOWLObjectMinCardinality(2, p, c));
                        exprs.add(df.getOWLObjectSomeValuesFrom(p, df.getOWLThing()));
                    }
                    if (!indivs.isEmpty() && i == 0) {
                        exprs.add(df.getOWLObjectHasValue(p, indivs.get(rnd.nextInt(indivs.size()))));
                    }
                }
            }
        }
        if (!indivs.isEmpty()) exprs.add(df.getOWLObjectOneOf(indivs.get(0)));
        if (!dataProps.isEmpty()) {
            exprs.add(df.getOWLDataSomeValuesFrom(dataProps.get(0), df.getTopDatatype()));
        }
        for (OWLClassExpression e : exprs) {
            String a = String.valueOf(e);
            add(CLASS_EXPR, "isSatisfiable", a, r -> r.isSatisfiable(e));
            add(CLASS_EXPR, "getSubClasses", a + ",true", r -> r.getSubClasses(e, true));
            add(CLASS_EXPR, "getSubClasses", a + ",false", r -> r.getSubClasses(e, false));
            add(CLASS_EXPR, "getSuperClasses", a + ",true", r -> r.getSuperClasses(e, true));
            add(CLASS_EXPR, "getSuperClasses", a + ",false", r -> r.getSuperClasses(e, false));
            add(CLASS_EXPR, "getEquivalentClasses", a, r -> r.getEquivalentClasses(e));
            if (exprs.indexOf(e) < 4) add(DISJOINT, "getDisjointClasses", a, r -> r.getDisjointClasses(e));
            add(CLASS_EXPR, "getInstances", a + ",true", r -> r.getInstances(e, true));
            add(CLASS_EXPR, "getInstances", a + ",false", r -> r.getInstances(e, false));
        }

        // Object properties, named and inverse expressions.
        add(OBJECT_PROPS, "getTopObjectPropertyNode", "", r -> r.getTopObjectPropertyNode());
        add(OBJECT_PROPS, "getBottomObjectPropertyNode", "", r -> r.getBottomObjectPropertyNode());
        List<OWLObjectPropertyExpression> opq = new ArrayList<>();
        opq.add(df.getOWLTopObjectProperty());
        opq.add(df.getOWLBottomObjectProperty());
        for (OWLObjectProperty p : objProps) {
            opq.add(p);
            opq.add(df.getOWLObjectInverseOf(p));
        }
        for (OWLObjectPropertyExpression p : opq) {
            String a = name(p);
            add(OBJECT_PROPS, "getSubObjectProperties", a + ",true", r -> r.getSubObjectProperties(p, true));
            add(OBJECT_PROPS, "getSubObjectProperties", a + ",false", r -> r.getSubObjectProperties(p, false));
            add(OBJECT_PROPS, "getSuperObjectProperties", a + ",true", r -> r.getSuperObjectProperties(p, true));
            add(OBJECT_PROPS, "getSuperObjectProperties", a + ",false", r -> r.getSuperObjectProperties(p, false));
            add(OBJECT_PROPS, "getEquivalentObjectProperties", a, r -> r.getEquivalentObjectProperties(p));
            add(OBJECT_PROPS, "getInverseObjectProperties", a, r -> r.getInverseObjectProperties(p));
            if (opq.indexOf(p) < DISJOINT_CAP) add(DISJOINT, "getDisjointObjectProperties", a, r -> r.getDisjointObjectProperties(p));
            // HermiT needs about half a second per domain or range query: ask for 30 expressions.
            if (opq.indexOf(p) < 30) {
                add(OBJECT_PROPS, "getObjectPropertyDomains", a + ",true", r -> r.getObjectPropertyDomains(p, true));
                add(OBJECT_PROPS, "getObjectPropertyDomains", a + ",false", r -> r.getObjectPropertyDomains(p, false));
                add(OBJECT_PROPS, "getObjectPropertyRanges", a + ",true", r -> r.getObjectPropertyRanges(p, true));
                add(OBJECT_PROPS, "getObjectPropertyRanges", a + ",false", r -> r.getObjectPropertyRanges(p, false));
            }
        }

        // Data properties.
        add(DATA_PROPS, "getTopDataPropertyNode", "", r -> r.getTopDataPropertyNode());
        add(DATA_PROPS, "getBottomDataPropertyNode", "", r -> r.getBottomDataPropertyNode());
        List<OWLDataProperty> dpq = new ArrayList<>();
        dpq.add(df.getOWLTopDataProperty());
        dpq.add(df.getOWLBottomDataProperty());
        dpq.addAll(dataProps);
        for (OWLDataProperty p : dpq) {
            String a = name(p);
            add(DATA_PROPS, "getSubDataProperties", a + ",true", r -> r.getSubDataProperties(p, true));
            add(DATA_PROPS, "getSubDataProperties", a + ",false", r -> r.getSubDataProperties(p, false));
            add(DATA_PROPS, "getSuperDataProperties", a + ",true", r -> r.getSuperDataProperties(p, true));
            add(DATA_PROPS, "getSuperDataProperties", a + ",false", r -> r.getSuperDataProperties(p, false));
            add(DATA_PROPS, "getEquivalentDataProperties", a, r -> r.getEquivalentDataProperties(p));
            if (dpq.indexOf(p) < DISJOINT_CAP) add(DISJOINT, "getDisjointDataProperties", a, r -> r.getDisjointDataProperties(p));
            if (dpq.indexOf(p) < 20) {
                add(DATA_PROPS, "getDataPropertyDomains", a + ",true", r -> r.getDataPropertyDomains(p, true));
                add(DATA_PROPS, "getDataPropertyDomains", a + ",false", r -> r.getDataPropertyDomains(p, false));
            }
        }

        // Individuals.
        for (OWLNamedIndividual i : indivs) {
            String a = name(i);
            add(INDIVIDUALS, "getTypes", a + ",true", r -> r.getTypes(i, true));
            add(INDIVIDUALS, "getTypes", a + ",false", r -> r.getTypes(i, false));
            add(INDIVIDUALS, "getSameIndividuals", a, r -> r.getSameIndividuals(i));
            if (indivs.indexOf(i) < DISJOINT_CAP) add(DISJOINT, "getDifferentIndividuals", a, r -> r.getDifferentIndividuals(i));
        }

        // Property values: individuals and properties that occur in assertions come first.
        List<OWLNamedIndividual> valInds = new ArrayList<>();
        Set<OWLObjectProperty> assertedOps = new TreeSet<>();
        Set<OWLDataProperty> assertedDps = new TreeSet<>();
        Set<OWLNamedIndividual> seenInd = new TreeSet<>();
        for (OWLOntology o : closure) {
            for (OWLObjectPropertyAssertionAxiom ax : o.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION)) {
                if (!ax.getProperty().isAnonymous()) assertedOps.add(ax.getProperty().asOWLObjectProperty());
                if (!ax.getSubject().isAnonymous()) seenInd.add(ax.getSubject().asOWLNamedIndividual());
            }
            for (OWLDataPropertyAssertionAxiom ax : o.getAxioms(AxiomType.DATA_PROPERTY_ASSERTION)) {
                if (!ax.getProperty().isAnonymous()) assertedDps.add(ax.getProperty().asOWLDataProperty());
                if (!ax.getSubject().isAnonymous()) seenInd.add(ax.getSubject().asOWLNamedIndividual());
            }
        }
        valInds.addAll(pick(sorted(seenInd), 25, "valind"));
        for (OWLNamedIndividual i : indivs) {
            if (valInds.size() >= 40) break;
            if (!valInds.contains(i)) valInds.add(i);
        }
        List<OWLObjectProperty> valOps = new ArrayList<>(pick(sorted(assertedOps), 12, "valop"));
        for (OWLObjectProperty p : objProps) {
            if (valOps.size() >= 15) break;
            if (!valOps.contains(p)) valOps.add(p);
        }
        List<OWLDataProperty> valDps = new ArrayList<>(pick(sorted(assertedDps), 12, "valdp"));
        for (OWLDataProperty p : dataProps) {
            if (valDps.size() >= 15) break;
            if (!valDps.contains(p)) valDps.add(p);
        }
        for (OWLNamedIndividual i : valInds) {
            for (OWLObjectProperty p : valOps) {
                add(VALUES, "getObjectPropertyValues", name(i) + "," + name(p), r -> r.getObjectPropertyValues(i, p));
            }
            for (int k = 0; k < Math.min(3, valOps.size()); k++) {
                OWLObjectPropertyExpression inv = df.getOWLObjectInverseOf(valOps.get(k));
                add(VALUES, "getObjectPropertyValues", name(i) + "," + name(inv), r -> r.getObjectPropertyValues(i, inv));
            }
            for (OWLDataProperty p : valDps) {
                add(VALUES, "getDataPropertyValues", name(i) + "," + name(p), r -> r.getDataPropertyValues(i, p));
            }
        }

        buildEntailments(closure, classes, objProps, dataProps, indivs);
        // Stable sort: cheap phases first, so a budget that runs out costs the slow tail.
        calls.sort(Comparator.comparingInt(c -> ORDER.indexOf(c.phase)));
    }

    private static Object sizeOf(Collection<?> c) { return c == null ? null : c.size(); }

    private static List<String> sortedStrings(Collection<?> c) {
        List<String> out = new ArrayList<>();
        for (Object o : c) out.add(String.valueOf(o));
        Collections.sort(out);
        return out;
    }

    private void buildEntailments(Set<OWLOntology> closure, List<OWLClass> cs, List<OWLObjectProperty> ops,
                                  List<OWLDataProperty> dps, List<OWLNamedIndividual> is) {
        Random rnd = new Random(seed * 13 + 7);
        List<AxiomType<?>> types = new ArrayList<>(AxiomType.AXIOM_TYPES);
        types.sort(Comparator.comparing(AxiomType::getName));
        for (AxiomType<?> t : types) {
            add(ENTAILMENT, "isEntailmentCheckingSupported", t.getName(), r -> r.isEntailmentCheckingSupported(t));
        }
        List<OWLAxiom> own = new ArrayList<>();
        for (AxiomType<?> t : types) {
            List<OWLAxiom> ofType = new ArrayList<>();
            for (OWLOntology o : closure) ofType.addAll(o.getAxioms(t));
            ofType.sort(Comparator.comparing(OWLAxiom::toString));
            Collections.shuffle(ofType, new Random(seed * 7 + t.getName().hashCode()));
            List<OWLAxiom> chosen = new ArrayList<>();
            for (OWLAxiom ax : ofType) {
                if (chosen.size() >= 3) break;
                if (ax.toString().length() > 400) continue;
                chosen.add(ax);
            }
            List<OWLAxiom> all = new ArrayList<>(chosen);
            own.addAll(chosen.subList(0, Math.min(2, chosen.size())));
            all.addAll(generated(t, rnd, cs, ops, dps, is));
            Set<String> seen = new HashSet<>();
            for (OWLAxiom ax : all) {
                if (!seen.add(ax.toString())) continue;
                add(ENTAILMENT, "isEntailed", ax.toString(), r -> r.isEntailed(ax));
            }
        }
        if (own.size() >= 2) {
            Set<OWLAxiom> set = new LinkedHashSet<>(own.subList(0, 2));
            add(ENTAILMENT, "isEntailed", "set:" + set, r -> r.isEntailed(set));
        }
    }

    private <T> T any(List<T> l, Random rnd) { return l.isEmpty() ? null : l.get(rnd.nextInt(l.size())); }

    private List<OWLAxiom> generated(AxiomType<?> t, Random rnd, List<OWLClass> cs, List<OWLObjectProperty> ops,
                                     List<OWLDataProperty> dps, List<OWLNamedIndividual> is) {
        List<OWLAxiom> out = new ArrayList<>();
        for (int n = 0; n < 2; n++) {
            OWLClass c = any(cs, rnd), d = any(cs, rnd), e = any(cs, rnd);
            OWLObjectProperty r1 = any(ops, rnd), r2 = any(ops, rnd), r3 = any(ops, rnd);
            OWLDataProperty d1 = any(dps, rnd), d2 = any(dps, rnd);
            OWLNamedIndividual i1 = any(is, rnd), i2 = any(is, rnd);
            OWLAxiom ax = null;
            String k = t.getName();
            if (k.equals("SubClassOf") && c != null && d != null) {
                ax = (n == 1 && r1 != null) ? df.getOWLSubClassOfAxiom(c, df.getOWLObjectSomeValuesFrom(r1, d))
                        : df.getOWLSubClassOfAxiom(c, d);
            } else if (k.equals("EquivalentClasses") && c != null && d != null) {
                ax = df.getOWLEquivalentClassesAxiom(c, d);
            } else if (k.equals("DisjointClasses") && c != null && d != null) {
                ax = df.getOWLDisjointClassesAxiom(c, d);
            } else if (k.equals("DisjointUnion") && c != null && d != null && e != null && !d.equals(e)) {
                ax = df.getOWLDisjointUnionAxiom(c, new LinkedHashSet<OWLClassExpression>(Arrays.asList(d, e)));
            } else if (k.equals("ClassAssertion") && c != null && i1 != null) {
                ax = df.getOWLClassAssertionAxiom(c, i1);
            } else if (k.equals("ObjectPropertyAssertion") && r1 != null && i1 != null && i2 != null) {
                ax = df.getOWLObjectPropertyAssertionAxiom(r1, i1, i2);
            } else if (k.equals("NegativeObjectPropertyAssertion") && r1 != null && i1 != null && i2 != null) {
                ax = df.getOWLNegativeObjectPropertyAssertionAxiom(r1, i1, i2);
            } else if (k.equals("DataPropertyAssertion") && d1 != null && i1 != null) {
                ax = df.getOWLDataPropertyAssertionAxiom(d1, i1, df.getOWLLiteral("x"));
            } else if (k.equals("NegativeDataPropertyAssertion") && d1 != null && i1 != null) {
                ax = df.getOWLNegativeDataPropertyAssertionAxiom(d1, i1, df.getOWLLiteral("x"));
            } else if (k.equals("SameIndividual") && i1 != null && i2 != null) {
                ax = df.getOWLSameIndividualAxiom(i1, i2);
            } else if (k.equals("DifferentIndividuals") && i1 != null && i2 != null && !i1.equals(i2)) {
                ax = df.getOWLDifferentIndividualsAxiom(i1, i2);
            } else if (k.equals("SubObjectPropertyOf") && r1 != null && r2 != null) {
                ax = df.getOWLSubObjectPropertyOfAxiom(r1, n == 1 ? df.getOWLObjectInverseOf(r2) : r2);
            } else if (k.equals("SubPropertyChainOf") && r1 != null && r2 != null && r3 != null) {
                ax = df.getOWLSubPropertyChainOfAxiom(Arrays.<OWLObjectPropertyExpression>asList(r1, r2), r3);
            } else if (k.equals("EquivalentObjectProperties") && r1 != null && r2 != null) {
                ax = df.getOWLEquivalentObjectPropertiesAxiom(r1, r2);
            } else if (k.equals("DisjointObjectProperties") && r1 != null && r2 != null && !r1.equals(r2)) {
                ax = df.getOWLDisjointObjectPropertiesAxiom(r1, r2);
            } else if (k.equals("InverseObjectProperties") && r1 != null && r2 != null) {
                ax = df.getOWLInverseObjectPropertiesAxiom(r1, r2);
            } else if (k.equals("ObjectPropertyDomain") && r1 != null && c != null) {
                ax = df.getOWLObjectPropertyDomainAxiom(r1, c);
            } else if (k.equals("ObjectPropertyRange") && r1 != null && c != null) {
                ax = df.getOWLObjectPropertyRangeAxiom(r1, c);
            } else if (k.equals("FunctionalObjectProperty") && r1 != null) {
                ax = df.getOWLFunctionalObjectPropertyAxiom(r1);
            } else if (k.equals("InverseFunctionalObjectProperty") && r1 != null) {
                ax = df.getOWLInverseFunctionalObjectPropertyAxiom(r1);
            } else if (k.equals("TransitiveObjectProperty") && r1 != null) {
                ax = df.getOWLTransitiveObjectPropertyAxiom(r1);
            } else if (k.equals("SymmetricObjectProperty") && r1 != null) {
                ax = df.getOWLSymmetricObjectPropertyAxiom(r1);
            } else if (k.equals("AsymmetricObjectProperty") && r1 != null) {
                ax = df.getOWLAsymmetricObjectPropertyAxiom(r1);
            } else if (k.equals("ReflexiveObjectProperty") && r1 != null) {
                ax = df.getOWLReflexiveObjectPropertyAxiom(r1);
            } else if (k.equals("IrrefexiveObjectProperty") || k.equals("IrreflexiveObjectProperty")) {
                if (r1 != null) ax = df.getOWLIrreflexiveObjectPropertyAxiom(r1);
            } else if (k.equals("SubDataPropertyOf") && d1 != null && d2 != null) {
                ax = df.getOWLSubDataPropertyOfAxiom(d1, d2);
            } else if (k.equals("EquivalentDataProperties") && d1 != null && d2 != null) {
                ax = df.getOWLEquivalentDataPropertiesAxiom(d1, d2);
            } else if (k.equals("DisjointDataProperties") && d1 != null && d2 != null && !d1.equals(d2)) {
                ax = df.getOWLDisjointDataPropertiesAxiom(d1, d2);
            } else if (k.equals("DataPropertyDomain") && d1 != null && c != null) {
                ax = df.getOWLDataPropertyDomainAxiom(d1, c);
            } else if (k.equals("DataPropertyRange") && d1 != null) {
                ax = df.getOWLDataPropertyRangeAxiom(d1, df.getOWLDatatype(OWL2Datatype.XSD_STRING.getIRI()));
            } else if (k.equals("FunctionalDataProperty") && d1 != null) {
                ax = df.getOWLFunctionalDataPropertyAxiom(d1);
            }
            if (ax != null) out.add(ax);
        }
        return out;
    }
}
