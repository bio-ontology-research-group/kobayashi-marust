package org.bioontology.kobayashimarust.protege;

import org.junit.BeforeClass;
import org.junit.Test;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;

import java.util.*;

import static org.junit.Assert.*;

/**
 * Differential test on 200 deterministically generated random OWL 2 DL
 * ontologies comparing every {@link OWLReasoner} answer of {@link KMReasoner}
 * with HermiT and verifying that all 25 plugin reductions in
 * {@code docs/V1.7.0-PLUGIN-REDUCTIONS.md} are reached.
 */
public class RandomDifferentialTest {

    public static final long SEED = 20261117L;

    @BeforeClass
    public static void setUp() {
        HermitDifferentialTest.locateKm();
    }

    public static final class ComparisonSummary {
        public int ontologiesRun;
        public int totalChecks;
        public int hermitDirectTypesAdjudicated;
        public int hermitDirectInstancesAdjudicated;
        public int hermitDataValuesAdjudicated;
        public int hermitBottomPropertyAdjudicated;
        public final List<String> kmMismatches = new ArrayList<>();
        public Map<String, Long> reductionHits = new LinkedHashMap<>();
    }

    @Test
    public void twoHundredRandomOntologiesMatchHermiTAndHitAllReductions() {
        KMReasoner.resetReductionHits();
        ComparisonSummary summary = runBatch(SEED, 0, 200);
        System.out.println("RandomDifferentialTest summary: ontologies=" + summary.ontologiesRun
                + " checks=" + summary.totalChecks
                + " hermitDirectTypesAdjudicated=" + summary.hermitDirectTypesAdjudicated
                + " hermitDirectInstancesAdjudicated=" + summary.hermitDirectInstancesAdjudicated
                + " hermitDataValuesAdjudicated=" + summary.hermitDataValuesAdjudicated
                + " hits=" + summary.reductionHits);
        assertEquals(200, summary.ontologiesRun);
        assertTrue("Expected zero KM mismatches but found: " + summary.kmMismatches,
                summary.kmMismatches.isEmpty());
        for (Map.Entry<String, Long> e : summary.reductionHits.entrySet()) {
            assertTrue("Reduction " + e.getKey() + " was never reached in 200 random ontologies (hits="
                    + summary.reductionHits + ")", e.getValue() > 0L);
        }
    }

    public static ComparisonSummary runBatch(long seed, int startIndex, int count) {
        ComparisonSummary summary = new ComparisonSummary();
        for (int i = startIndex; i < startIndex + count; i++) {
            RandomOntologyGenerator.GeneratedOntology gen = RandomOntologyGenerator.generate(seed, i);
            compareOne(gen, summary);
            summary.ontologiesRun++;
        }
        summary.reductionHits = KMReasoner.getReductionHits();
        return summary;
    }

    public static void compareOne(
            RandomOntologyGenerator.GeneratedOntology gen, ComparisonSummary summary) {
        OWLOntology ont = gen.ontology;
        OWLDataFactory df = ont.getOWLOntologyManager().getOWLDataFactory();
        org.semanticweb.HermiT.Configuration hConf = new org.semanticweb.HermiT.Configuration();
        hConf.ignoreUnsupportedDatatypes = true;
        OWLReasoner hermit = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(ont, hConf);
        OWLReasoner km = new KMReasonerFactory().createReasoner(ont, new SimpleConfiguration());
        String ctx = "ont#" + gen.index + "(" + gen.archetype + ")";
        try {
            boolean hCons = hermit.isConsistent();
            boolean kCons = km.isConsistent();
            summary.totalChecks++;
            if (hCons != kCons) {
                summary.kmMismatches.add(ctx + " isConsistent: hermit=" + hCons + " km=" + kCons);
                return;
            }
            if (!kCons) return;

            checkNode(ctx, "getTopClassNode", hermit.getTopClassNode(), km.getTopClassNode(), summary);
            checkNode(ctx, "getBottomClassNode", hermit.getBottomClassNode(), km.getBottomClassNode(), summary);
            checkNode(ctx, "getUnsatisfiableClasses",
                    hermit.getUnsatisfiableClasses(), km.getUnsatisfiableClasses(), summary);

            // Named classes
            List<OWLClass> classes = new ArrayList<>(ont.getClassesInSignature());
            classes.sort(Comparator.comparing(c -> c.getIRI().toString()));
            for (OWLClass c : classes) {
                String cn = c.getIRI().getFragment();
                checkBool(ctx, "isSatisfiable(" + cn + ")",
                        hermit.isSatisfiable(c), km.isSatisfiable(c), summary);
                checkNodeSet(ctx, "getSubClasses(" + cn + ",true)",
                        hermit.getSubClasses(c, true), km.getSubClasses(c, true), summary);
                checkNodeSet(ctx, "getSubClasses(" + cn + ",false)",
                        hermit.getSubClasses(c, false), km.getSubClasses(c, false), summary);
                checkNodeSet(ctx, "getSuperClasses(" + cn + ",true)",
                        hermit.getSuperClasses(c, true), km.getSuperClasses(c, true), summary);
                checkNodeSet(ctx, "getSuperClasses(" + cn + ",false)",
                        hermit.getSuperClasses(c, false), km.getSuperClasses(c, false), summary);
                checkNode(ctx, "getEquivalentClasses(" + cn + ")",
                        hermit.getEquivalentClasses(c), km.getEquivalentClasses(c), summary);
                checkNodeSet(ctx, "getDisjointClasses(" + cn + ")",
                        hermit.getDisjointClasses(c), km.getDisjointClasses(c), summary);
                checkNodeSet(ctx, "getInstances(" + cn + ",false)",
                        hermit.getInstances(c, false), km.getInstances(c, false), summary);
                checkDirectInstances(ctx, c, hermit, km, summary);
            }

            // Anonymous class expressions
            for (OWLClassExpression ce : gen.classExpressions) {
                String cen = ce.toString();
                checkBool(ctx, "isSatisfiable(" + cen + ")",
                        hermit.isSatisfiable(ce), km.isSatisfiable(ce), summary);
                checkNodeSet(ctx, "getSubClasses(" + cen + ",true)",
                        hermit.getSubClasses(ce, true), km.getSubClasses(ce, true), summary);
                checkNodeSet(ctx, "getSubClasses(" + cen + ",false)",
                        hermit.getSubClasses(ce, false), km.getSubClasses(ce, false), summary);
                checkNodeSet(ctx, "getSuperClasses(" + cen + ",true)",
                        hermit.getSuperClasses(ce, true), km.getSuperClasses(ce, true), summary);
                checkNodeSet(ctx, "getSuperClasses(" + cen + ",false)",
                        hermit.getSuperClasses(ce, false), km.getSuperClasses(ce, false), summary);
                checkNode(ctx, "getEquivalentClasses(" + cen + ")",
                        hermit.getEquivalentClasses(ce), km.getEquivalentClasses(ce), summary);
                checkNodeSet(ctx, "getDisjointClasses(" + cen + ")",
                        hermit.getDisjointClasses(ce), km.getDisjointClasses(ce), summary);
                checkNodeSet(ctx, "getInstances(" + cen + ",false)",
                        hermit.getInstances(ce, false), km.getInstances(ce, false), summary);
                checkDirectInstances(ctx, ce, hermit, km, summary);
            }

            // Object properties
            checkNode(ctx, "getTopObjectPropertyNode",
                    hermit.getTopObjectPropertyNode(), km.getTopObjectPropertyNode(), summary);
            checkNode(ctx, "getBottomObjectPropertyNode",
                    hermit.getBottomObjectPropertyNode(), km.getBottomObjectPropertyNode(), summary);
            List<OWLObjectProperty> ops = new ArrayList<>(ont.getObjectPropertiesInSignature());
            ops.remove(df.getOWLTopObjectProperty());
            ops.remove(df.getOWLBottomObjectProperty());
            ops.sort(Comparator.comparing(p -> p.getIRI().toString()));
            for (OWLObjectProperty p : ops) {
                for (OWLObjectPropertyExpression pe : Arrays.asList(p, p.getInverseProperty())) {
                    String pn = pe.toString();
                    checkNodeSet(ctx, "getSubObjectProperties(" + pn + ",true)",
                            hermit.getSubObjectProperties(pe, true), km.getSubObjectProperties(pe, true), summary);
                    checkNodeSet(ctx, "getSubObjectProperties(" + pn + ",false)",
                            hermit.getSubObjectProperties(pe, false), km.getSubObjectProperties(pe, false), summary);
                    checkNodeSet(ctx, "getSuperObjectProperties(" + pn + ",true)",
                            hermit.getSuperObjectProperties(pe, true), km.getSuperObjectProperties(pe, true), summary);
                    checkNodeSet(ctx, "getSuperObjectProperties(" + pn + ",false)",
                            hermit.getSuperObjectProperties(pe, false), km.getSuperObjectProperties(pe, false), summary);
                    checkNode(ctx, "getEquivalentObjectProperties(" + pn + ")",
                            hermit.getEquivalentObjectProperties(pe), km.getEquivalentObjectProperties(pe), summary);
                    checkNode(ctx, "getInverseObjectProperties(" + pn + ")",
                            hermit.getInverseObjectProperties(pe), km.getInverseObjectProperties(pe), summary);
                    checkNodeSet(ctx, "getDisjointObjectProperties(" + pn + ")",
                            hermit.getDisjointObjectProperties(pe), km.getDisjointObjectProperties(pe), summary);
                    checkNodeSet(ctx, "getObjectPropertyDomains(" + pn + ",true)",
                            hermit.getObjectPropertyDomains(pe, true), km.getObjectPropertyDomains(pe, true), summary);
                    checkNodeSet(ctx, "getObjectPropertyDomains(" + pn + ",false)",
                            hermit.getObjectPropertyDomains(pe, false), km.getObjectPropertyDomains(pe, false), summary);
                    checkNodeSet(ctx, "getObjectPropertyRanges(" + pn + ",true)",
                            hermit.getObjectPropertyRanges(pe, true), km.getObjectPropertyRanges(pe, true), summary);
                    checkNodeSet(ctx, "getObjectPropertyRanges(" + pn + ",false)",
                            hermit.getObjectPropertyRanges(pe, false), km.getObjectPropertyRanges(pe, false), summary);
                }
            }

            // Data properties
            checkNode(ctx, "getTopDataPropertyNode",
                    hermit.getTopDataPropertyNode(), km.getTopDataPropertyNode(), summary);
            checkNode(ctx, "getBottomDataPropertyNode",
                    hermit.getBottomDataPropertyNode(), km.getBottomDataPropertyNode(), summary);
            List<OWLDataProperty> dps = new ArrayList<>(ont.getDataPropertiesInSignature());
            dps.remove(df.getOWLTopDataProperty());
            dps.remove(df.getOWLBottomDataProperty());
            dps.sort(Comparator.comparing(p -> p.getIRI().toString()));
            for (OWLDataProperty p : dps) {
                String pn = p.getIRI().getFragment();
                checkNodeSet(ctx, "getSubDataProperties(" + pn + ",true)",
                        hermit.getSubDataProperties(p, true), km.getSubDataProperties(p, true), summary);
                checkNodeSet(ctx, "getSubDataProperties(" + pn + ",false)",
                        hermit.getSubDataProperties(p, false), km.getSubDataProperties(p, false), summary);
                checkNodeSet(ctx, "getSuperDataProperties(" + pn + ",true)",
                        hermit.getSuperDataProperties(p, true), km.getSuperDataProperties(p, true), summary);
                checkNodeSet(ctx, "getSuperDataProperties(" + pn + ",false)",
                        hermit.getSuperDataProperties(p, false), km.getSuperDataProperties(p, false), summary);
                checkNode(ctx, "getEquivalentDataProperties(" + pn + ")",
                        hermit.getEquivalentDataProperties(p), km.getEquivalentDataProperties(p), summary);
                checkNodeSet(ctx, "getDisjointDataProperties(" + pn + ")",
                        hermit.getDisjointDataProperties(p), km.getDisjointDataProperties(p), summary);
                checkNodeSet(ctx, "getDataPropertyDomains(" + pn + ",true)",
                        hermit.getDataPropertyDomains(p, true), km.getDataPropertyDomains(p, true), summary);
                checkNodeSet(ctx, "getDataPropertyDomains(" + pn + ",false)",
                        hermit.getDataPropertyDomains(p, false), km.getDataPropertyDomains(p, false), summary);
            }

            // Individuals
            List<OWLNamedIndividual> inds = new ArrayList<>(ont.getIndividualsInSignature());
            inds.sort(Comparator.comparing(a -> a.getIRI().toString()));
            for (OWLNamedIndividual ind : inds) {
                String in = ind.getIRI().getFragment();
                checkNodeSet(ctx, "getTypes(" + in + ",false)",
                        hermit.getTypes(ind, false), km.getTypes(ind, false), summary);
                checkDirectTypes(ctx, ind, hermit, km, summary);
                checkNode(ctx, "getSameIndividuals(" + in + ")",
                        hermit.getSameIndividuals(ind), km.getSameIndividuals(ind), summary);
                checkNodeSet(ctx, "getDifferentIndividuals(" + in + ")",
                        hermit.getDifferentIndividuals(ind), km.getDifferentIndividuals(ind), summary);
                for (OWLObjectProperty p : ops) {
                    checkNodeSet(ctx, "getObjectPropertyValues(" + in + "," + p.getIRI().getFragment() + ")",
                            hermit.getObjectPropertyValues(ind, p), km.getObjectPropertyValues(ind, p), summary);
                }
                for (OWLDataProperty p : dps) {
                    summary.totalChecks++;
                    Set<OWLLiteral> hLit = hermit.getDataPropertyValues(ind, p);
                    Set<OWLLiteral> kLit = km.getDataPropertyValues(ind, p);
                    Set<String> hs = canonLiterals(hLit);
                    Set<String> ks = canonLiterals(kLit);
                    if (!hs.equals(ks)) {
                        // HermiT's getDataPropertyValues only checks literals occurring in ABox
                        // DataPropertyAssertions, omitting entailed values introduced via TBox
                        // DataHasValue restrictions even when hermit.isEntailed(p(ind, lit)) is true.
                        boolean hermitIncompleteOnDataHasValue = ks.containsAll(hs);
                        if (hermitIncompleteOnDataHasValue) {
                            for (OWLLiteral l : kLit) {
                                if (!hs.contains(l.toString())
                                        && !hermit.isEntailed(df.getOWLDataPropertyAssertionAxiom(p, ind, l))) {
                                    hermitIncompleteOnDataHasValue = false;
                                    break;
                                }
                            }
                        }
                        if (hermitIncompleteOnDataHasValue) {
                            summary.hermitDataValuesAdjudicated++;
                        } else {
                            summary.kmMismatches.add(ctx + " getDataPropertyValues(" + in + "," + p.getIRI().getFragment()
                                    + "): hermit=" + hs + " km=" + ks);
                        }
                    }
                }
            }

            // Entailments
            for (OWLAxiom ax : gen.entailmentAxioms) {
                if (ax instanceof SWRLRule) {
                    summary.totalChecks++;
                    boolean kEnt = km.isEntailed(ax);
                    if (!kEnt) {
                        summary.kmMismatches.add(ctx + " isEntailed(" + ax + "): expected true, got false");
                    }
                } else {
                    checkBool(ctx, "isEntailed(" + ax + ")",
                            hermit.isEntailed(ax), km.isEntailed(ax), summary);
                }
            }
        } finally {
            hermit.dispose();
            km.dispose();
        }
    }

    private static void checkBool(
            String ctx, String call, boolean h, boolean k, ComparisonSummary summary) {
        summary.totalChecks++;
        if (h != k) {
            summary.kmMismatches.add(ctx + " " + call + ": hermit=" + h + " km=" + k);
        }
    }

    private static void checkNode(
            String ctx, String call, Node<?> h, Node<?> k, ComparisonSummary summary) {
        summary.totalChecks++;
        Set<String> hs = canonNode(h), ks = canonNode(k);
        if (!hs.equals(ks)) {
            summary.kmMismatches.add(ctx + " " + call + ": hermit=" + hs + " km=" + ks);
        }
    }

    private static void checkNodeSet(
            String ctx, String call, NodeSet<?> h, NodeSet<?> k, ComparisonSummary summary) {
        summary.totalChecks++;
        Set<Set<String>> hs = canonNodeSet(h), ks = canonNodeSet(k);
        if (!hs.equals(ks)) {
            summary.kmMismatches.add(ctx + " " + call + ": hermit=" + hs + " km=" + ks);
        }
    }

    private static void checkDirectTypes(
            String ctx, OWLNamedIndividual ind, OWLReasoner hermit, OWLReasoner km, ComparisonSummary summary) {
        summary.totalChecks++;
        NodeSet<OWLClass> hDirect = hermit.getTypes(ind, true);
        NodeSet<OWLClass> kDirect = km.getTypes(ind, true);
        Set<Set<String>> hs = canonNodeSet(hDirect);
        Set<Set<String>> ks = canonNodeSet(kDirect);
        if (hs.equals(ks)) return;
        // Filter out non-minimal nodes from HermiT's direct types
        Set<Set<String>> filtered = new LinkedHashSet<>();
        for (Node<OWLClass> n : hDirect.getNodes()) {
            OWLClass rep = n.getRepresentativeElement();
            Set<OWLClass> subs = hermit.getSubClasses(rep, false).getFlattened();
            boolean hasStrictSubInTypes = false;
            for (Node<OWLClass> other : hDirect.getNodes()) {
                if (!other.equals(n) && subs.contains(other.getRepresentativeElement())) {
                    hasStrictSubInTypes = true;
                    break;
                }
            }
            if (!hasStrictSubInTypes) filtered.add(canonNode(n));
        }
        if (filtered.equals(ks)) {
            summary.hermitDirectTypesAdjudicated++;
        } else {
            summary.kmMismatches.add(ctx + " getTypes(" + ind.getIRI().getFragment()
                    + ",true): hermit=" + hs + " km=" + ks);
        }
    }

    private static void checkDirectInstances(
            String ctx, OWLClassExpression ce, OWLReasoner hermit, OWLReasoner km, ComparisonSummary summary) {
        summary.totalChecks++;
        NodeSet<OWLNamedIndividual> hDirect = hermit.getInstances(ce, true);
        NodeSet<OWLNamedIndividual> kDirect = km.getInstances(ce, true);
        Set<Set<String>> hs = canonNodeSet(hDirect);
        Set<Set<String>> ks = canonNodeSet(kDirect);
        if (hs.equals(ks)) return;
        // Compute direct instances under OWL 2 Direct Semantics from HermiT's own all-instances and sub-classes
        Set<OWLClass> strictSubClasses = new LinkedHashSet<>(hermit.getSubClasses(ce, false).getFlattened());
        strictSubClasses.removeAll(hermit.getEquivalentClasses(ce).getEntities());
        Set<Set<String>> expected = new LinkedHashSet<>();
        for (Node<OWLNamedIndividual> indNode : hermit.getInstances(ce, false).getNodes()) {
            OWLNamedIndividual rep = indNode.getRepresentativeElement();
            Set<OWLClass> allTypes = hermit.getTypes(rep, false).getFlattened();
            boolean inStrictSub = false;
            for (OWLClass sub : strictSubClasses) {
                if (!sub.isOWLNothing() && allTypes.contains(sub)) {
                    inStrictSub = true;
                    break;
                }
            }
            if (!inStrictSub) expected.add(canonNode(indNode));
        }
        if (expected.equals(ks)) {
            summary.hermitDirectInstancesAdjudicated++;
        } else {
            summary.kmMismatches.add(ctx + " getInstances(" + ce + ",true): hermit=" + hs + " km=" + ks);
        }
    }

    private static Set<String> canonLiterals(Set<OWLLiteral> lits) {
        Set<String> out = new TreeSet<>();
        for (OWLLiteral l : lits) out.add(l.toString());
        return out;
    }

    private static Set<String> canonNode(Node<?> n) {
        Set<String> s = new TreeSet<>();
        for (Object e : n.getEntities()) s.add(e.toString());
        return s;
    }

    private static Set<Set<String>> canonNodeSet(NodeSet<?> ns) {
        Set<Set<String>> out = new LinkedHashSet<>();
        List<Set<String>> list = new ArrayList<>();
        for (Node<?> n : ns.getNodes()) list.add(canonNode(n));
        list.sort(Comparator.comparing(Object::toString));
        out.addAll(list);
        return out;
    }
}
