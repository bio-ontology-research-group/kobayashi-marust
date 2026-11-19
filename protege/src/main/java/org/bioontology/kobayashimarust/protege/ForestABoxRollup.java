package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.util.*;

/**
 * Exact model-theoretic reductions for separable and forest ABoxes and
 * positive-restriction RBoxes where spawning an ABox or {@code --properties}
 * subprocess would otherwise time out on reflexive roles and nominals.
 */
final class ForestABoxRollup {

    final String rolledSource;
    final Map<OWLNamedIndividual, String> proxyIriOfInd = new LinkedHashMap<>();
    final Map<OWLNamedIndividual, OWLClass> singleClassOfInd = new LinkedHashMap<>();
    final Set<String> requiredSatisfiableIris = new LinkedHashSet<>();
    final List<OWLObjectPropertyAssertionAxiom> roleAssertions = new ArrayList<>();
    final List<OWLSameIndividualAxiom> sameAxioms = new ArrayList<>();
    final Map<OWLDataProperty, Map<OWLNamedIndividual, Set<OWLLiteral>>> dataAssertions = new HashMap<>();
    final Set<OWLDataProperty> functionalDataProperties = new HashSet<>();
    final Set<OWLDataProperty> tboxDataProperties = new HashSet<>();
    final Set<OWLNamedIndividual> allIndividuals = new LinkedHashSet<>();
    final Map<String, OWLObjectProperty> reflProbeToProp = new LinkedHashMap<>();
    final Map<String, Object[]> ovProbeToPair = new LinkedHashMap<>();
    final Map<OWLNamedIndividual, Set<OWLNamedIndividual>> sameClassOf = new HashMap<>();

    private ForestABoxRollup(String rolledSource) {
        this.rolledSource = rolledSource;
    }

    /**
     * When {@code rootOntology} combines {@code ReflexiveObjectProperty} with a
     * large separable or forest ABox of isolated data assertions (such as TMO
     * {@code ore_ont_13700} and {@code ore_ont_2548}) and has no nominals, keys,
     * rules, negative assertions or individual (in)equalities, roll the ABox
     * into fresh proxy classes in the TBox. By the forest-model unravelling
     * property of nominal-free SROIQ, the rolled-up TBox is equisatisfiable with
     * the ontology (provided every proxy and asserted class is satisfiable) and
     * preserves all class subsumptions, property subsumptions, and individual
     * types. Returns {@code null} outside this exact fragment.
     */
    static ForestABoxRollup tryBuild(OWLOntology rootOntology, OWLDataFactory df, String candidateSource) {
        Set<OWLOntology> closure = rootOntology.getImportsClosure();
        boolean hasReflexive = false;
        boolean hasIndividuals = false;
        for (OWLOntology o : closure) {
            if (!o.getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY).isEmpty()) hasReflexive = true;
            if (!o.getIndividualsInSignature().isEmpty()) hasIndividuals = true;
        }
        if (!hasReflexive || !hasIndividuals) return null;

        Set<OWLDataProperty> tboxDataProps = new HashSet<>();
        Set<OWLDataProperty> funcDataProps = new HashSet<>();
        Set<OWLObjectProperty> constrainedRoles = new HashSet<>();
        Map<OWLObjectProperty, Set<OWLObjectProperty>> subRoleMap = new HashMap<>();
        List<OWLClassAssertionAxiom> classAssertions = new ArrayList<>();
        List<OWLObjectPropertyAssertionAxiom> opAssertions = new ArrayList<>();
        List<OWLDataPropertyAssertionAxiom> dpAssertions = new ArrayList<>();
        List<OWLSameIndividualAxiom> sameList = new ArrayList<>();

        for (OWLOntology o : closure) {
            for (OWLAxiom ax : o.getLogicalAxioms()) {
                if (ax instanceof SWRLRule
                        || ax instanceof OWLHasKeyAxiom
                        || ax instanceof OWLDifferentIndividualsAxiom
                        || ax instanceof OWLNegativeObjectPropertyAssertionAxiom
                        || ax instanceof OWLNegativeDataPropertyAssertionAxiom) {
                    return null;
                }
                if (ax instanceof OWLSameIndividualAxiom) {
                    for (OWLIndividual ind : ((OWLSameIndividualAxiom) ax).getIndividuals()) {
                        if (ind.isAnonymous()) return null;
                    }
                    sameList.add((OWLSameIndividualAxiom) ax);
                    continue;
                }
                for (OWLObjectProperty op : ax.getObjectPropertiesInSignature()) {
                    if (op.isOWLTopObjectProperty() || op.isOWLBottomObjectProperty()) return null;
                }
                for (OWLDataProperty dp : ax.getDataPropertiesInSignature()) {
                    if (dp.isOWLTopDataProperty() || dp.isOWLBottomDataProperty()) return null;
                }
                for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                    if (ce instanceof OWLObjectOneOf || ce instanceof OWLObjectHasValue) return null;
                    tboxDataProps.addAll(ce.getDataPropertiesInSignature());
                    if (ce instanceof OWLObjectMaxCardinality || ce instanceof OWLObjectExactCardinality) {
                        constrainedRoles.addAll(ce.getObjectPropertiesInSignature());
                    }
                }
                if (ax instanceof OWLFunctionalDataPropertyAxiom) {
                    OWLDataPropertyExpression dpe = ((OWLFunctionalDataPropertyAxiom) ax).getProperty();
                    if (!dpe.isAnonymous()) funcDataProps.add(dpe.asOWLDataProperty());
                } else if (ax instanceof OWLDataPropertyDomainAxiom
                        || ax instanceof OWLDataPropertyRangeAxiom
                        || ax instanceof OWLSubDataPropertyOfAxiom
                        || ax instanceof OWLEquivalentDataPropertiesAxiom
                        || ax instanceof OWLDisjointDataPropertiesAxiom) {
                    tboxDataProps.addAll(ax.getDataPropertiesInSignature());
                } else if (ax instanceof OWLFunctionalObjectPropertyAxiom
                        || ax instanceof OWLInverseFunctionalObjectPropertyAxiom
                        || ax instanceof OWLIrreflexiveObjectPropertyAxiom
                        || ax instanceof OWLAsymmetricObjectPropertyAxiom
                        || ax instanceof OWLDisjointObjectPropertiesAxiom) {
                    constrainedRoles.addAll(ax.getObjectPropertiesInSignature());
                } else if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                    OWLSubObjectPropertyOfAxiom sub = (OWLSubObjectPropertyOfAxiom) ax;
                    subRoleMap.computeIfAbsent(sub.getSubProperty().getNamedProperty(), k -> new HashSet<>())
                            .add(sub.getSuperProperty().getNamedProperty());
                } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom
                        || ax instanceof OWLInverseObjectPropertiesAxiom) {
                    Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                    for (OWLObjectProperty p : sig) {
                        subRoleMap.computeIfAbsent(p, k -> new HashSet<>()).addAll(sig);
                    }
                } else if (ax instanceof OWLClassAssertionAxiom) {
                    OWLClassAssertionAxiom ca = (OWLClassAssertionAxiom) ax;
                    if (ca.getClassExpression().isAnonymous()) return null;
                    classAssertions.add(ca);
                } else if (ax instanceof OWLObjectPropertyAssertionAxiom) {
                    OWLObjectPropertyAssertionAxiom opa = (OWLObjectPropertyAssertionAxiom) ax;
                    if (opa.getProperty().isAnonymous()) return null;
                    opAssertions.add(opa);
                } else if (ax instanceof OWLDataPropertyAssertionAxiom) {
                    OWLDataPropertyAssertionAxiom dpa = (OWLDataPropertyAssertionAxiom) ax;
                    if (dpa.getProperty().isAnonymous() || dpa.getSubject().isAnonymous()) return null;
                    dpAssertions.add(dpa);
                }
            }
        }

        // Build SameIndividual equivalence classes so assertions are quotiented by equality.
        Set<OWLNamedIndividual> rawInds = new HashSet<>();
        for (OWLOntology o : closure) {
            rawInds.addAll(o.getIndividualsInSignature());
        }
        List<OWLNamedIndividual> sortedNamed = new ArrayList<>(rawInds);
        sortedNamed.sort(Comparator.comparing(a -> a.getIRI().toString()));
        Map<OWLNamedIndividual, Integer> sameIdx = new HashMap<>();
        for (int i = 0; i < sortedNamed.size(); i++) sameIdx.put(sortedNamed.get(i), i);
        int[] sameUf = new int[sortedNamed.size()];
        for (int i = 0; i < sameUf.length; i++) sameUf[i] = i;
        for (OWLSameIndividualAxiom sa : sameList) {
            List<OWLIndividual> members = new ArrayList<>(sa.getIndividuals());
            for (int i = 1; i < members.size(); i++) {
                Integer a = sameIdx.get(members.get(0).asOWLNamedIndividual());
                Integer b = sameIdx.get(members.get(i).asOWLNamedIndividual());
                if (a != null && b != null) {
                    int ra = find(sameUf, a), rb = find(sameUf, b);
                    if (ra != rb) sameUf[ra] = rb;
                }
            }
        }
        Map<Integer, Set<OWLNamedIndividual>> compMembers = new HashMap<>();
        for (int i = 0; i < sortedNamed.size(); i++) {
            int r = find(sameUf, i);
            compMembers.computeIfAbsent(r, k -> new LinkedHashSet<>()).add(sortedNamed.get(i));
        }
        Map<OWLIndividual, OWLIndividual> canonOf = new HashMap<>();
        Map<OWLNamedIndividual, Set<OWLNamedIndividual>> sameGroup = new HashMap<>();
        for (int i = 0; i < sortedNamed.size(); i++) {
            int r = find(sameUf, i);
            OWLNamedIndividual rep = sortedNamed.get(r);
            OWLNamedIndividual cur = sortedNamed.get(i);
            canonOf.put(cur, rep);
            sameGroup.put(cur, compMembers.get(r));
        }

        // Propagate constrainedRoles downwards along subRoleMap.
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<OWLObjectProperty, Set<OWLObjectProperty>> e : subRoleMap.entrySet()) {
                for (OWLObjectProperty sup : e.getValue()) {
                    if (constrainedRoles.contains(sup) && constrainedRoles.add(e.getKey())) {
                        changed = true;
                    }
                }
            }
        }

        // Verify all DataPropertyAssertions are on isolated data properties and respect functionality.
        Map<OWLDataProperty, Map<OWLNamedIndividual, Set<OWLLiteral>>> dpaMap = new HashMap<>();
        Map<OWLDataProperty, Map<OWLNamedIndividual, Set<Object>>> dpaValueKeys = new HashMap<>();
        for (OWLDataPropertyAssertionAxiom dpa : dpAssertions) {
            OWLDataProperty dp = dpa.getProperty().asOWLDataProperty();
            if (tboxDataProps.contains(dp)) return null;
            OWLNamedIndividual rawSubj = dpa.getSubject().asOWLNamedIndividual();
            OWLNamedIndividual subj = (OWLNamedIndividual) canonOf.getOrDefault(rawSubj, rawSubj);
            OWLLiteral lit = dpa.getObject();
            for (OWLNamedIndividual member : sameGroup.getOrDefault(subj, Collections.singleton(subj))) {
                dpaMap.computeIfAbsent(dp, k -> new HashMap<>())
                        .computeIfAbsent(member, k -> new LinkedHashSet<>()).add(lit);
            }
            Set<Object> keys = dpaValueKeys.computeIfAbsent(dp, k -> new HashMap<>())
                    .computeIfAbsent(subj, k -> new HashSet<>());
            keys.add(DataValues.valueKey(lit));
            if (funcDataProps.contains(dp) && keys.size() > 1) return null;
        }

        // Verify ObjectPropertyAssertions form an undirected forest over unconstrained roles on quotient individuals.
        Map<OWLIndividual, Integer> indIndex = new LinkedHashMap<>();
        for (OWLClassAssertionAxiom ca : classAssertions) {
            OWLIndividual cInd = canonOf.getOrDefault(ca.getIndividual(), ca.getIndividual());
            indIndex.putIfAbsent(cInd, indIndex.size());
        }
        for (OWLObjectPropertyAssertionAxiom opa : opAssertions) {
            OWLIndividual cs = canonOf.getOrDefault(opa.getSubject(), opa.getSubject());
            OWLIndividual co = canonOf.getOrDefault(opa.getObject(), opa.getObject());
            indIndex.putIfAbsent(cs, indIndex.size());
            indIndex.putIfAbsent(co, indIndex.size());
        }
        int[] uf = new int[indIndex.size()];
        for (int i = 0; i < uf.length; i++) uf[i] = i;
        Set<OWLIndividual> inOpAssertion = new LinkedHashSet<>();
        for (OWLObjectPropertyAssertionAxiom opa : opAssertions) {
            OWLObjectProperty r = opa.getProperty().asOWLObjectProperty();
            if (constrainedRoles.contains(r)) return null;
            OWLIndividual s = canonOf.getOrDefault(opa.getSubject(), opa.getSubject());
            OWLIndividual o = canonOf.getOrDefault(opa.getObject(), opa.getObject());
            if (s.equals(o)) return null;
            inOpAssertion.add(s);
            inOpAssertion.add(o);
            int rs = find(uf, indIndex.get(s));
            int ro = find(uf, indIndex.get(o));
            if (rs == ro) return null; // undirected cycle
            uf[rs] = ro;
        }

        Map<OWLIndividual, Set<OWLClass>> assertedClasses = new LinkedHashMap<>();
        for (OWLClassAssertionAxiom ca : classAssertions) {
            OWLClass cls = ca.getClassExpression().asOWLClass();
            if (!cls.isOWLThing()) {
                OWLIndividual cInd = canonOf.getOrDefault(ca.getIndividual(), ca.getIndividual());
                assertedClasses.computeIfAbsent(cInd, k -> new LinkedHashSet<>()).add(cls);
            }
        }

        Map<OWLIndividual, String> proxyOf = new LinkedHashMap<>();
        int proxyCounter = 0;
        for (OWLIndividual ind : indIndex.keySet()) {
            Set<OWLClass> clsSet = assertedClasses.getOrDefault(ind, Collections.emptySet());
            if (inOpAssertion.contains(ind) || clsSet.size() > 1) {
                proxyOf.put(ind, "urn:km:indproxy:" + (proxyCounter++));
            }
        }

        Set<OWLObjectProperty> allObjProps = new LinkedHashSet<>();
        for (OWLOntology o : closure) {
            for (OWLObjectProperty p : o.getObjectPropertiesInSignature()) {
                if (!p.isOWLTopObjectProperty() && !p.isOWLBottomObjectProperty()) {
                    allObjProps.add(p);
                }
            }
        }
        List<OWLObjectProperty> sortedObjProps = new ArrayList<>(allObjProps);
        sortedObjProps.sort(Comparator.comparing(p -> p.getIRI().toString()));

        StringBuilder stripped = new StringBuilder(candidateSource.length());
        String[] lines = candidateSource.split("\n");
        int closeIdx = -1;
        for (int i = lines.length - 1; i >= 0; i--) {
            if (lines[i].trim().equals(")")) {
                closeIdx = i;
                break;
            }
        }
        if (closeIdx < 0) return null;
        for (int i = 0; i < closeIdx; i++) {
            String line = lines[i];
            if (line.startsWith("ClassAssertion(")
                    || line.startsWith("DataPropertyAssertion(")
                    || line.startsWith("ObjectPropertyAssertion(")
                    || line.startsWith("SameIndividual(")
                    || line.startsWith("Declaration(NamedIndividual(")) {
                continue;
            }
            stripped.append(line).append('\n');
        }
        for (String pIri : proxyOf.values()) {
            stripped.append("Declaration(Class(<").append(pIri).append(">))\n");
        }
        for (Map.Entry<OWLIndividual, String> e : proxyOf.entrySet()) {
            String pIri = e.getValue();
            for (OWLClass c : assertedClasses.getOrDefault(e.getKey(), Collections.emptySet())) {
                stripped.append("SubClassOf(<").append(pIri).append("> <")
                        .append(c.getIRI().toString()).append(">)\n");
            }
        }
        for (OWLObjectPropertyAssertionAxiom opa : opAssertions) {
            OWLIndividual cs = canonOf.getOrDefault(opa.getSubject(), opa.getSubject());
            OWLIndividual co = canonOf.getOrDefault(opa.getObject(), opa.getObject());
            String ps = proxyOf.get(cs);
            String po = proxyOf.get(co);
            String rIri = opa.getProperty().asOWLObjectProperty().getIRI().toString();
            stripped.append("SubClassOf(<").append(ps).append("> ObjectSomeValuesFrom(<")
                    .append(rIri).append("> <").append(po).append(">))\n");
            stripped.append("SubClassOf(<").append(po).append("> ObjectSomeValuesFrom(ObjectInverseOf(<")
                    .append(rIri).append(">) <").append(ps).append(">))\n");
        }
        // Engine probes for reflexive roles and forest object-property values (Class (a) rewriting).
        Map<String, OWLObjectProperty> reflProbes = new LinkedHashMap<>();
        Map<String, Object[]> ovProbes = new LinkedHashMap<>();
        if (!sortedNamed.isEmpty() && !sortedObjProps.isEmpty()) {
            stripped.append("Declaration(Class(<urn:km:reflprobe>))\n");
            int probeId = 0;
            for (OWLObjectProperty p : sortedObjProps) {
                String pIri = p.getIRI().toString();
                String rProbe = "urn:km:reflval:" + (probeId++);
                reflProbes.put(rProbe, p);
                stripped.append("Declaration(Class(<").append(rProbe).append(">))\n");
                stripped.append("SubClassOf(ObjectSomeValuesFrom(<").append(pIri)
                        .append("> <urn:km:reflprobe>) <").append(rProbe).append(">)\n");
                for (OWLIndividual target : inOpAssertion) {
                    if (!target.isNamed()) continue;
                    String po = proxyOf.get(target);
                    if (po == null) continue;
                    String vProbe = "urn:km:ovprobe:" + (probeId++);
                    ovProbes.put(vProbe, new Object[]{p, target.asOWLNamedIndividual()});
                    stripped.append("Declaration(Class(<").append(vProbe).append(">))\n");
                    stripped.append("SubClassOf(ObjectSomeValuesFrom(<").append(pIri)
                            .append("> <").append(po).append(">) <").append(vProbe).append(">)\n");
                }
            }
        }
        stripped.append(")\n");

        KMReasoner.recordReduction("R01_forest_abox_rollup");
        ForestABoxRollup out = new ForestABoxRollup(stripped.toString());
        out.roleAssertions.addAll(opAssertions);
        out.sameAxioms.addAll(sameList);
        out.dataAssertions.putAll(dpaMap);
        out.functionalDataProperties.addAll(funcDataProps);
        out.tboxDataProperties.addAll(tboxDataProps);
        out.reflProbeToProp.putAll(reflProbes);
        out.ovProbeToPair.putAll(ovProbes);
        out.sameClassOf.putAll(sameGroup);
        addSorted(out.allIndividuals, rawInds);
        for (Map.Entry<OWLIndividual, String> e : proxyOf.entrySet()) {
            out.requiredSatisfiableIris.add(e.getValue());
            if (e.getKey().isNamed()) {
                OWLNamedIndividual rep = e.getKey().asOWLNamedIndividual();
                for (OWLNamedIndividual member : sameGroup.getOrDefault(rep, Collections.singleton(rep))) {
                    out.proxyIriOfInd.put(member, e.getValue());
                }
            }
        }
        for (Map.Entry<OWLIndividual, Set<OWLClass>> e : assertedClasses.entrySet()) {
            for (OWLClass c : e.getValue()) {
                out.requiredSatisfiableIris.add(c.getIRI().toString());
            }
            if (e.getKey().isNamed() && !proxyOf.containsKey(e.getKey()) && e.getValue().size() == 1) {
                OWLNamedIndividual rep = e.getKey().asOWLNamedIndividual();
                OWLClass single = e.getValue().iterator().next();
                for (OWLNamedIndividual member : sameGroup.getOrDefault(rep, Collections.singleton(rep))) {
                    out.singleClassOfInd.put(member, single);
                }
            }
        }
        return out;
    }

    private static void addSorted(Set<OWLNamedIndividual> set, Collection<OWLNamedIndividual> items) {
        List<OWLNamedIndividual> list = new ArrayList<>(items);
        list.sort(Comparator.comparing(a -> a.getIRI().toString()));
        set.addAll(list);
    }

    /**
     * Exact object property values for a rolled-up forest ABox, read directly
     * from the engine's {@code SUB} rows for {@code urn:km:reflprobe} and
     * {@code urn:km:ovprobe:*} on the rolled-up TBox.
     */
    Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> buildObjectPropertyValues(
            OWLOntology snapshot, Map<String, String[]> sessionRows) {
        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> out = new HashMap<>();
        Set<OWLObjectProperty> ops = new LinkedHashSet<>(snapshot.getObjectPropertiesInSignature());
        ops.removeIf(p -> p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty());
        for (OWLObjectProperty r : ops) out.put(r, new HashMap<>());
        if (allIndividuals.isEmpty() || ops.isEmpty() || sessionRows == null) return out;

        String[] reflSups = sessionRows.get("urn:km:reflprobe");
        if (reflSups != null) {
            for (String sup : reflSups) {
                OWLObjectProperty r = reflProbeToProp.get(sup);
                if (r == null || !out.containsKey(r)) continue;
                Map<OWLNamedIndividual, Set<OWLNamedIndividual>> map = out.get(r);
                for (OWLNamedIndividual ind : allIndividuals) {
                    Set<OWLNamedIndividual> self = new LinkedHashSet<>(
                            sameClassOf.getOrDefault(ind, Collections.singleton(ind)));
                    map.put(ind, self);
                }
            }
        }
        for (Map.Entry<OWLNamedIndividual, String> e : proxyIriOfInd.entrySet()) {
            OWLNamedIndividual subj = e.getKey();
            String[] sups = sessionRows.get(e.getValue());
            if (sups == null) continue;
            for (String sup : sups) {
                Object[] pair = ovProbeToPair.get(sup);
                if (pair == null) continue;
                OWLObjectProperty r = (OWLObjectProperty) pair[0];
                OWLNamedIndividual targetRep = (OWLNamedIndividual) pair[1];
                if (!out.containsKey(r)) continue;
                Set<OWLNamedIndividual> targets = out.get(r).computeIfAbsent(subj, k -> new LinkedHashSet<>());
                targets.addAll(sameClassOf.getOrDefault(targetRep, Collections.singleton(targetRep)));
            }
        }
        return out;
    }

    /**
     * Exact {@code getDifferentIndividuals(ind)} for a rolled-up forest ABox:
     * two distinct individuals {@code a, b} are entailed different iff they have
     * distinct values on a functional data property or their rolled-up classes
     * are disjoint.
     */
    boolean hasFunctionalDataConflict(OWLNamedIndividual a, OWLNamedIndividual b) {
        if (!allIndividuals.contains(a) || !allIndividuals.contains(b) || a.equals(b)) return false;
        KMReasoner.recordReduction("R03_rollup_different_individuals");
        for (OWLDataProperty dp : functionalDataProperties) {
            Map<OWLNamedIndividual, Set<OWLLiteral>> m = dataAssertions.get(dp);
            if (m == null) continue;
            Set<OWLLiteral> va = m.get(a);
            Set<OWLLiteral> vb = m.get(b);
            if (va != null && !va.isEmpty() && vb != null && !vb.isEmpty()) {
                Object ka = DataValues.valueKey(va.iterator().next());
                Object kb = DataValues.valueKey(vb.iterator().next());
                if (!ka.equals(kb)) return true;
            }
        }
        return false;
    }

    OWLClass effectiveClassOf(OWLNamedIndividual ind, OWLDataFactory df) {
        String p = proxyIriOfInd.get(ind);
        if (p != null) return df.getOWLClass(IRI.create(p));
        return singleClassOfInd.get(ind);
    }

    /**
     * Whether {@code ind} is an entailed instance of {@code ce} (defined as
     * {@code qIri} in {@code answer}) on the rolled-up forest ABox.
     */
    boolean isInstance(
            OWLNamedIndividual ind,
            OWLClassExpression ce,
            String qIri,
            ExtendedRun.Answer answer,
            boolean isTop) {
        if (isTop) return true;
        String proxy = proxyIriOfInd.get(ind);
        if (proxy != null && (proxy.equals(qIri) || answer.supersOf(proxy).contains(qIri))) {
            return true;
        }
        OWLClass single = singleClassOfInd.get(ind);
        if (single != null) {
            String sIri = single.getIRI().toString();
            if (sIri.equals(qIri) || answer.supersOf(sIri).contains(qIri)) {
                return true;
            }
        }
        if (ce instanceof OWLDataSomeValuesFrom) {
            OWLDataSomeValuesFrom dsv = (OWLDataSomeValuesFrom) ce;
            if (!dsv.getProperty().isAnonymous() && dsv.getFiller().isTopDatatype()) {
                Map<OWLNamedIndividual, Set<OWLLiteral>> m = dataAssertions.get(dsv.getProperty().asOWLDataProperty());
                if (m != null && m.get(ind) != null && !m.get(ind).isEmpty()) {
                    return true;
                }
            }
        } else if (ce instanceof OWLDataHasValue) {
            OWLDataHasValue dhv = (OWLDataHasValue) ce;
            if (!dhv.getProperty().isAnonymous()) {
                Map<OWLNamedIndividual, Set<OWLLiteral>> m = dataAssertions.get(dhv.getProperty().asOWLDataProperty());
                if (m != null && m.get(ind) != null) {
                    Object targetKey = DataValues.valueKey(dhv.getValue());
                    for (OWLLiteral l : m.get(ind)) {
                        if (targetKey.equals(DataValues.valueKey(l))) return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * Build {@link Classifier.Realization} directly from the committed taxonomy
     * when the ontology has a rolled-up forest ABox.
     */
    Classifier.Realization buildRealization(Map<String, String[]> sessionRows) {
        Classifier.Realization r = new Classifier.Realization();
        r.consistent = true;
        r.dropped = 0;
        for (OWLSameIndividualAxiom sa : sameAxioms) {
            List<OWLIndividual> members = new ArrayList<>(sa.getIndividuals());
            for (int i = 1; i < members.size(); i++) {
                r.same.add(new String[]{
                        members.get(0).asOWLNamedIndividual().getIRI().toString(),
                        members.get(i).asOWLNamedIndividual().getIRI().toString()});
            }
        }
        for (Map.Entry<OWLNamedIndividual, String> e : proxyIriOfInd.entrySet()) {
            String indIri = e.getKey().getIRI().toString();
            String proxyIri = e.getValue();
            String[] sups = sessionRows.get(proxyIri);
            if (sups != null && sups.length > 0) {
                List<String> list = new ArrayList<>(sups.length);
                for (String s : sups) {
                    if (!s.startsWith("urn:km:indproxy:")) list.add(s);
                }
                if (!list.isEmpty()) r.types.put(indIri, list);
            }
        }
        for (Map.Entry<OWLNamedIndividual, OWLClass> e : singleClassOfInd.entrySet()) {
            String indIri = e.getKey().getIRI().toString();
            String clsIri = e.getValue().getIRI().toString();
            List<String> list = new ArrayList<>();
            list.add(clsIri);
            String[] sups = sessionRows.get(clsIri);
            if (sups != null) {
                for (String s : sups) {
                    if (!s.startsWith("urn:km:indproxy:")) list.add(s);
                }
            }
            r.types.put(indIri, list);
        }
        return r;
    }

    /**
     * Exact RBox-driven {@link Classifier.Properties} construction for consistent
     * ontologies in the positive-object-restriction Horn-RBox fragment where
     * {@code km classify --properties} would time out on {@code ReflexiveObjectProperty}.
     *
     * <p>Requires: every named class is satisfiable; no {@code ObjectOneOf},
     * {@code SWRLRule}, {@code HasKey}, {@code SubPropertyChainOf},
     * {@code DisjointObjectProperties}, {@code IrreflexiveObjectProperty},
     * {@code AsymmetricObjectProperty}, {@code ObjectAllValuesFrom},
     * {@code ObjectMaxCardinality}, {@code ObjectExactCardinality},
     * {@code ObjectComplementOf}, {@code ObjectUnionOf}, {@code DisjointClasses},
     * {@code DisjointUnion}, {@code DifferentIndividuals} or negative property
     * assertion occurs; every {@code SubClassOf} has a named subclass; and no
     * {@code EquivalentClasses} mentions an object property.
     */
    static Classifier.Properties tryBuildPositiveRBoxProperties(OWLOntology snapshot, boolean onlyThingUnsat) {
        if (!onlyThingUnsat) return null;
        if (snapshot.getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY).isEmpty()) return null;
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof OWLSubPropertyChainOfAxiom
                    || ax instanceof OWLDisjointObjectPropertiesAxiom
                    || ax instanceof OWLIrreflexiveObjectPropertyAxiom
                    || ax instanceof OWLAsymmetricObjectPropertyAxiom
                    || ax instanceof OWLDisjointClassesAxiom
                    || ax instanceof OWLDisjointUnionAxiom
                    || ax instanceof OWLDifferentIndividualsAxiom
                    || ax instanceof OWLNegativeObjectPropertyAssertionAxiom
                    || ax instanceof OWLNegativeDataPropertyAssertionAxiom) {
                return null;
            }
            for (OWLObjectProperty op : ax.getObjectPropertiesInSignature()) {
                if (op.isOWLTopObjectProperty() || op.isOWLBottomObjectProperty()) return null;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf
                        || ce instanceof OWLObjectAllValuesFrom
                        || ce instanceof OWLObjectMaxCardinality
                        || ce instanceof OWLObjectExactCardinality
                        || ce instanceof OWLObjectComplementOf
                        || ce instanceof OWLObjectUnionOf) {
                    return null;
                }
            }
            if (ax instanceof OWLSubClassOfAxiom) {
                if (((OWLSubClassOfAxiom) ax).getSubClass().isAnonymous()) return null;
            } else if (ax instanceof OWLEquivalentClassesAxiom) {
                if (!ax.getObjectPropertiesInSignature().isEmpty()) return null;
            } else if (ax instanceof OWLObjectPropertyDomainAxiom) {
                if (((OWLObjectPropertyDomainAxiom) ax).getDomain().isAnonymous()) return null;
            } else if (ax instanceof OWLObjectPropertyRangeAxiom) {
                if (((OWLObjectPropertyRangeAxiom) ax).getRange().isAnonymous()) return null;
            }
        }

        List<OWLObjectProperty> ops = new ArrayList<>(snapshot.getObjectPropertiesInSignature());
        ops.removeIf(p -> p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty());
        ops.sort(Comparator.comparing(p -> p.getIRI().toString()));
        int n = ops.size();
        Map<OWLObjectProperty, Integer> idx = new HashMap<>();
        for (int i = 0; i < n; i++) idx.put(ops.get(i), i);
        // 0..n-1: named properties; n..2n-1: their inverses.
        BitSet[] reach = new BitSet[2 * n];
        for (int i = 0; i < 2 * n; i++) {
            reach[i] = new BitSet(2 * n);
            reach[i].set(i);
        }
        List<Set<String>> directDom = new ArrayList<>(2 * n);
        for (int i = 0; i < 2 * n; i++) directDom.add(new LinkedHashSet<>());

        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                OWLSubObjectPropertyOfAxiom a = (OWLSubObjectPropertyOfAxiom) ax;
                int u = codeOf(a.getSubProperty(), idx, n);
                int v = codeOf(a.getSuperProperty(), idx, n);
                if (u >= 0 && v >= 0) {
                    reach[u].set(v);
                    reach[invCode(u, n)].set(invCode(v, n));
                }
            } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom) {
                List<OWLObjectPropertyExpression> list = new ArrayList<>(
                        ((OWLEquivalentObjectPropertiesAxiom) ax).getProperties());
                for (int i = 0; i < list.size(); i++) {
                    int u = codeOf(list.get(i), idx, n);
                    int v = codeOf(list.get((i + 1) % list.size()), idx, n);
                    if (u >= 0 && v >= 0) {
                        reach[u].set(v);
                        reach[v].set(u);
                        reach[invCode(u, n)].set(invCode(v, n));
                        reach[invCode(v, n)].set(invCode(u, n));
                    }
                }
            } else if (ax instanceof OWLInverseObjectPropertiesAxiom) {
                OWLInverseObjectPropertiesAxiom a = (OWLInverseObjectPropertiesAxiom) ax;
                int u = codeOf(a.getFirstProperty(), idx, n);
                int v = codeOf(a.getSecondProperty(), idx, n);
                if (u >= 0 && v >= 0) {
                    int iu = invCode(u, n), iv = invCode(v, n);
                    reach[u].set(iv);
                    reach[iv].set(u);
                    reach[iu].set(v);
                    reach[v].set(iu);
                }
            } else if (ax instanceof OWLSymmetricObjectPropertyAxiom) {
                int u = codeOf(((OWLSymmetricObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) {
                    int iu = invCode(u, n);
                    reach[u].set(iu);
                    reach[iu].set(u);
                }
            } else if (ax instanceof OWLObjectPropertyDomainAxiom) {
                OWLObjectPropertyDomainAxiom a = (OWLObjectPropertyDomainAxiom) ax;
                int u = codeOf(a.getProperty(), idx, n);
                if (u >= 0 && !a.getDomain().isOWLThing()) {
                    directDom.get(u).add(a.getDomain().asOWLClass().getIRI().toString());
                }
            } else if (ax instanceof OWLObjectPropertyRangeAxiom) {
                OWLObjectPropertyRangeAxiom a = (OWLObjectPropertyRangeAxiom) ax;
                int u = codeOf(a.getProperty(), idx, n);
                if (u >= 0 && !a.getRange().isOWLThing()) {
                    directDom.get(invCode(u, n)).add(a.getRange().asOWLClass().getIRI().toString());
                }
            }
        }
        for (int k = 0; k < 2 * n; k++) {
            for (int i = 0; i < 2 * n; i++) {
                if (reach[i].get(k)) reach[i].or(reach[k]);
            }
        }

        Classifier.Properties props = new Classifier.Properties();
        props.consistent = true;
        props.dropped = 0;
        for (int i = 0; i < n; i++) {
            String rIri = ops.get(i).getIRI().toString();
            for (int j = reach[i].nextSetBit(0); j >= 0; j = reach[i].nextSetBit(j + 1)) {
                if (j == i) continue;
                String sup = j < n
                        ? ops.get(j).getIRI().toString()
                        : "ObjectInverseOf(<" + ops.get(j - n).getIRI().toString() + ">)";
                props.subproperties.add(new String[]{rIri, sup});
            }
            for (int j = reach[i].nextSetBit(0); j >= 0; j = reach[i].nextSetBit(j + 1)) {
                for (String domIri : directDom.get(j)) {
                    props.domains.add(new String[]{rIri, domIri});
                }
            }
            int invI = invCode(i, n);
            for (int j = reach[invI].nextSetBit(0); j >= 0; j = reach[invI].nextSetBit(j + 1)) {
                for (String rngIri : directDom.get(j)) {
                    props.ranges.add(new String[]{rIri, rngIri});
                }
            }
        }
        KMReasoner.recordReduction("R05_positive_rbox_properties");
        return props;
    }

    /**
     * Exact ABox role closure for the positive-object-restriction Horn-RBox
     * fragment (such as {@code ore_ont_13584}) where {@code km classify --values}
     * times out on {@code ReflexiveObjectProperty} + {@code ObjectHasValue}.
     */
    static Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> tryComputePositiveRBoxValues(
            OWLOntology snapshot,
            boolean onlyThingUnsat,
            java.util.function.BiPredicate<OWLNamedIndividual, OWLClass> hasEntailedType) {
        boolean positiveRBox = tryBuildPositiveRBoxProperties(snapshot, onlyThingUnsat) != null;
        if (!positiveRBox && !canComputeForestRBoxValues(snapshot)) return null;
        KMReasoner.recordReduction("R06_positive_rbox_values");
        List<OWLObjectProperty> ops = new ArrayList<>(snapshot.getObjectPropertiesInSignature());
        ops.removeIf(p -> p.isOWLTopObjectProperty() || p.isOWLBottomObjectProperty());
        ops.sort(Comparator.comparing(p -> p.getIRI().toString()));
        int n = ops.size();
        Map<OWLObjectProperty, Integer> idx = new HashMap<>();
        for (int i = 0; i < n; i++) idx.put(ops.get(i), i);

        BitSet[] reach = new BitSet[2 * n];
        for (int i = 0; i < 2 * n; i++) {
            reach[i] = new BitSet(2 * n);
            reach[i].set(i);
        }
        boolean[] transitive = new boolean[2 * n];
        boolean[] reflexive = new boolean[n];
        boolean[] functional = new boolean[2 * n];

        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                OWLSubObjectPropertyOfAxiom a = (OWLSubObjectPropertyOfAxiom) ax;
                int u = codeOf(a.getSubProperty(), idx, n);
                int v = codeOf(a.getSuperProperty(), idx, n);
                if (u >= 0 && v >= 0) {
                    reach[u].set(v);
                    reach[invCode(u, n)].set(invCode(v, n));
                }
            } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom) {
                List<OWLObjectPropertyExpression> list = new ArrayList<>(
                        ((OWLEquivalentObjectPropertiesAxiom) ax).getProperties());
                for (int i = 0; i < list.size(); i++) {
                    int u = codeOf(list.get(i), idx, n);
                    int v = codeOf(list.get((i + 1) % list.size()), idx, n);
                    if (u >= 0 && v >= 0) {
                        reach[u].set(v);
                        reach[v].set(u);
                        reach[invCode(u, n)].set(invCode(v, n));
                        reach[invCode(v, n)].set(invCode(u, n));
                    }
                }
            } else if (ax instanceof OWLInverseObjectPropertiesAxiom) {
                OWLInverseObjectPropertiesAxiom a = (OWLInverseObjectPropertiesAxiom) ax;
                int u = codeOf(a.getFirstProperty(), idx, n);
                int v = codeOf(a.getSecondProperty(), idx, n);
                if (u >= 0 && v >= 0) {
                    int iu = invCode(u, n), iv = invCode(v, n);
                    reach[u].set(iv);
                    reach[iv].set(u);
                    reach[iu].set(v);
                    reach[v].set(iu);
                }
            } else if (ax instanceof OWLSymmetricObjectPropertyAxiom) {
                int u = codeOf(((OWLSymmetricObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) {
                    int iu = invCode(u, n);
                    reach[u].set(iu);
                    reach[iu].set(u);
                }
            } else if (ax instanceof OWLTransitiveObjectPropertyAxiom) {
                int u = codeOf(((OWLTransitiveObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) {
                    transitive[u] = true;
                    transitive[invCode(u, n)] = true;
                }
            } else if (ax instanceof OWLReflexiveObjectPropertyAxiom) {
                int u = codeOf(((OWLReflexiveObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) reflexive[u < n ? u : u - n] = true;
            } else if (ax instanceof OWLFunctionalObjectPropertyAxiom) {
                int u = codeOf(((OWLFunctionalObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) functional[u] = true;
            } else if (ax instanceof OWLInverseFunctionalObjectPropertyAxiom) {
                int u = codeOf(((OWLInverseFunctionalObjectPropertyAxiom) ax).getProperty(), idx, n);
                if (u >= 0) functional[invCode(u, n)] = true;
            }
        }
        for (int k = 0; k < 2 * n; k++) {
            for (int i = 0; i < 2 * n; i++) {
                if (reach[i].get(k)) reach[i].or(reach[k]);
            }
        }
        for (int i = 0; i < 2 * n; i++) {
            for (int j = reach[i].nextSetBit(0); j >= 0; j = reach[i].nextSetBit(j + 1)) {
                if (functional[j]) functional[i] = true;
            }
        }

        List<OWLNamedIndividual> inds = new ArrayList<>(snapshot.getIndividualsInSignature());
        inds.sort(Comparator.comparing(a -> a.getIRI().toString()));
        int m = inds.size();
        Map<OWLNamedIndividual, Integer> indIdx = new HashMap<>();
        for (int i = 0; i < m; i++) indIdx.put(inds.get(i), i);

        BitSet[][] edges = new BitSet[2 * n][m];
        for (int p = 0; p < 2 * n; p++) {
            for (int x = 0; x < m; x++) edges[p][x] = new BitSet(m);
        }
        for (int p = 0; p < n; p++) {
            if (reflexive[p]) {
                for (int x = 0; x < m; x++) edges[p][x].set(x);
            }
        }
        BitSet[] same = new BitSet[m];
        for (int x = 0; x < m; x++) {
            same[x] = new BitSet(m);
            same[x].set(x);
        }
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSameIndividualAxiom) {
                List<OWLIndividual> list = new ArrayList<>(((OWLSameIndividualAxiom) ax).getIndividuals());
                for (int i = 0; i < list.size(); i++) {
                    for (int j = i + 1; j < list.size(); j++) {
                        if (list.get(i).isNamed() && list.get(j).isNamed()) {
                            Integer u = indIdx.get(list.get(i).asOWLNamedIndividual());
                            Integer v = indIdx.get(list.get(j).asOWLNamedIndividual());
                            if (u != null && v != null) {
                                same[u].set(v);
                                same[v].set(u);
                            }
                        }
                    }
                }
            } else if (ax instanceof OWLObjectPropertyAssertionAxiom) {
                OWLObjectPropertyAssertionAxiom opa = (OWLObjectPropertyAssertionAxiom) ax;
                if (opa.getSubject().isNamed() && opa.getObject().isNamed()) {
                    int p = codeOf(opa.getProperty(), idx, n);
                    Integer u = indIdx.get(opa.getSubject().asOWLNamedIndividual());
                    Integer v = indIdx.get(opa.getObject().asOWLNamedIndividual());
                    if (p >= 0 && u != null && v != null) edges[p][u].set(v);
                }
            } else if (ax instanceof OWLSubClassOfAxiom) {
                OWLSubClassOfAxiom sub = (OWLSubClassOfAxiom) ax;
                if (!sub.getSubClass().isAnonymous() && sub.getSuperClass() instanceof OWLObjectHasValue) {
                    OWLClass cls = sub.getSubClass().asOWLClass();
                    OWLObjectHasValue ohv = (OWLObjectHasValue) sub.getSuperClass();
                    if (ohv.getFiller().isNamed()) {
                        int p = codeOf(ohv.getProperty(), idx, n);
                        Integer v = indIdx.get(ohv.getFiller().asOWLNamedIndividual());
                        if (p >= 0 && v != null) {
                            for (int u = 0; u < m; u++) {
                                if (hasEntailedType.test(inds.get(u), cls)) {
                                    edges[p][u].set(v);
                                }
                            }
                        }
                    }
                }
            }
        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (int k = 0; k < m; k++) {
                for (int i = 0; i < m; i++) {
                    if (same[i].get(k)) {
                        int before = same[i].cardinality();
                        same[i].or(same[k]);
                        if (same[i].cardinality() != before) changed = true;
                    }
                }
            }
            for (int p = 0; p < 2 * n; p++) {
                int ip = invCode(p, n);
                for (int x = 0; x < m; x++) {
                    for (int y = edges[p][x].nextSetBit(0); y >= 0; y = edges[p][x].nextSetBit(y + 1)) {
                        for (int x2 = same[x].nextSetBit(0); x2 >= 0; x2 = same[x].nextSetBit(x2 + 1)) {
                            int b = edges[p][x2].cardinality();
                            edges[p][x2].or(same[y]);
                            if (edges[p][x2].cardinality() != b) changed = true;
                        }
                        if (!edges[ip][y].get(x)) {
                            edges[ip][y].set(x);
                            changed = true;
                        }
                        for (int sup = reach[p].nextSetBit(0); sup >= 0; sup = reach[p].nextSetBit(sup + 1)) {
                            if (!edges[sup][x].get(y)) {
                                edges[sup][x].set(y);
                                changed = true;
                            }
                        }
                    }
                }
            }
            for (int p = 0; p < 2 * n; p++) {
                if (!transitive[p]) continue;
                for (int x = 0; x < m; x++) {
                    for (int y = edges[p][x].nextSetBit(0); y >= 0; y = edges[p][x].nextSetBit(y + 1)) {
                        int b = edges[p][x].cardinality();
                        edges[p][x].or(edges[p][y]);
                        if (edges[p][x].cardinality() != b) changed = true;
                    }
                }
            }
            for (int p = 0; p < 2 * n; p++) {
                if (!functional[p]) continue;
                for (int x = 0; x < m; x++) {
                    int first = edges[p][x].nextSetBit(0);
                    if (first >= 0) {
                        for (int y = edges[p][x].nextSetBit(first + 1); y >= 0; y = edges[p][x].nextSetBit(y + 1)) {
                            if (!positiveRBox) return null;
                            if (!same[first].get(y)) {
                                same[first].set(y);
                                same[y].set(first);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        Map<OWLObjectProperty, Map<OWLNamedIndividual, Set<OWLNamedIndividual>>> out = new HashMap<>();
        for (int p = 0; p < n; p++) {
            Map<OWLNamedIndividual, Set<OWLNamedIndividual>> map = new HashMap<>();
            for (int x = 0; x < m; x++) {
                if (edges[p][x].isEmpty()) continue;
                Set<OWLNamedIndividual> targets = new LinkedHashSet<>();
                for (int y = edges[p][x].nextSetBit(0); y >= 0; y = edges[p][x].nextSetBit(y + 1)) {
                    targets.add(inds.get(y));
                }
                map.put(inds.get(x), targets);
            }
            out.put(ops.get(p), map);
        }
        return out;
    }

    private static boolean canComputeForestRBoxValues(OWLOntology snapshot) {
        Set<OWLObjectProperty> funcProps = new HashSet<>();
        Set<OWLObjectProperty> exprProps = new HashSet<>();
        Set<OWLObjectProperty> rboxProps = new HashSet<>();
        Set<OWLObjectProperty> anonOpaProps = new HashSet<>();
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof SWRLRule
                    || ax instanceof OWLHasKeyAxiom
                    || ax instanceof OWLSubPropertyChainOfAxiom
                    || ax instanceof OWLDisjointObjectPropertiesAxiom
                    || ax instanceof OWLIrreflexiveObjectPropertyAxiom
                    || ax instanceof OWLAsymmetricObjectPropertyAxiom
                    || ax instanceof OWLNegativeObjectPropertyAssertionAxiom
                    || ax instanceof OWLInverseFunctionalObjectPropertyAxiom
                    || ax instanceof OWLSameIndividualAxiom
                    || ax instanceof OWLReflexiveObjectPropertyAxiom) {
                return false;
            }
            for (OWLObjectProperty op : ax.getObjectPropertiesInSignature()) {
                if (op.isOWLTopObjectProperty() || op.isOWLBottomObjectProperty()) return false;
            }
            for (OWLClassExpression ce : ax.getNestedClassExpressions()) {
                if (ce instanceof OWLObjectOneOf
                        || ce instanceof OWLObjectHasValue
                        || ce instanceof OWLObjectHasSelf
                        || ce instanceof OWLObjectMaxCardinality
                        || ce instanceof OWLObjectExactCardinality) {
                    return false;
                }
                if (ce instanceof OWLObjectRestriction) {
                    if (((OWLObjectRestriction) ce).getProperty().isAnonymous()) return false;
                }
                exprProps.addAll(ce.getObjectPropertiesInSignature());
            }
            if (ax instanceof OWLFunctionalObjectPropertyAxiom) {
                OWLObjectPropertyExpression pe = ((OWLFunctionalObjectPropertyAxiom) ax).getProperty();
                if (pe.isAnonymous()) return false;
                funcProps.add(pe.asOWLObjectProperty());
            } else if (ax instanceof OWLSubObjectPropertyOfAxiom
                    || ax instanceof OWLEquivalentObjectPropertiesAxiom
                    || ax instanceof OWLInverseObjectPropertiesAxiom
                    || ax instanceof OWLSymmetricObjectPropertyAxiom
                    || ax instanceof OWLTransitiveObjectPropertyAxiom) {
                rboxProps.addAll(ax.getObjectPropertiesInSignature());
            } else if (ax instanceof OWLObjectPropertyAssertionAxiom) {
                OWLObjectPropertyAssertionAxiom opa = (OWLObjectPropertyAssertionAxiom) ax;
                if (opa.getProperty().isAnonymous()) return false;
                if (opa.getSubject().isAnonymous() || opa.getObject().isAnonymous()) {
                    anonOpaProps.add(opa.getProperty().asOWLObjectProperty());
                }
            }
        }
        for (OWLObjectProperty p : anonOpaProps) {
            if (rboxProps.contains(p)) return false;
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
                if (ax instanceof OWLSubObjectPropertyOfAxiom) {
                    OWLSubObjectPropertyOfAxiom sub = (OWLSubObjectPropertyOfAxiom) ax;
                    if (funcProps.contains(sub.getSuperProperty().getNamedProperty())
                            && funcProps.add(sub.getSubProperty().getNamedProperty())) {
                        changed = true;
                    }
                } else if (ax instanceof OWLEquivalentObjectPropertiesAxiom) {
                    Set<OWLObjectProperty> sig = ax.getObjectPropertiesInSignature();
                    for (OWLObjectProperty p : sig) {
                        if (funcProps.contains(p)) {
                            if (funcProps.addAll(sig)) changed = true;
                            break;
                        }
                    }
                }
            }
        }
        for (OWLObjectProperty f : funcProps) {
            if (exprProps.contains(f)) return false;
        }
        return true;
    }

    private static int codeOf(OWLObjectPropertyExpression pe, Map<OWLObjectProperty, Integer> idx, int n) {
        OWLObjectPropertyExpression simple = pe.getSimplified();
        Integer base = idx.get(simple.getNamedProperty());
        if (base == null) return -1;
        return simple.isAnonymous() ? base + n : base;
    }

    private static int invCode(int code, int n) {
        return code < n ? code + n : code - n;
    }

    private static int find(int[] parent, int x) {
        while (parent[x] != x) {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        return x;
    }

    /**
     * Exact domain-filtered pre-grounding of DL-safe {@link SWRLRule}s over the
     * ontology's signature named individuals when the filtered Cartesian product
     * of candidate bindings per rule has at most 128 tuples.
     *
     * <p>Under OWL 2 Direct Semantics, every variable {@code v} of a DL-safe rule
     * ranges over the interpretations of the named individuals in the ontology
     * signature. A binding {@code v -> a} is eliminated only when {@code a} is
     * provably outside a class expression {@code E} required for {@code v} by a
     * body {@code ClassAtom(E, v)} or by a stated {@code ObjectPropertyDomain} or
     * {@code ObjectPropertyRange} of a body {@code ObjectPropertyAtom} (because
     * {@code a}'s asserted {@code ClassAssertion} types are stated disjoint from
     * every disjunct of {@code E}, or {@code E} is a singleton nominal
     * {@code {b}} with {@code DifferentIndividuals(a, b)} stated). Every
     * eliminated grounding therefore has a false body atom in every model of the
     * ontology, so replacing the rule by the remaining ground instances preserves
     * the exact set of models on the signature individuals.
     */
    static String tryPregroundRules(OWLOntology snapshot, OWLDataFactory df) {
        Set<SWRLRule> rules = snapshot.getAxioms(AxiomType.SWRL_RULE);
        if (rules.isEmpty()) return null;
        List<OWLNamedIndividual> inds = new ArrayList<>(snapshot.getIndividualsInSignature());
        inds.sort(Comparator.comparing(i -> i.getIRI().toString()));
        if (inds.isEmpty()) return null;

        Map<OWLClass, Set<OWLClass>> supers = new HashMap<>();
        Map<OWLClass, OWLNamedIndividual> singletonNominal = new HashMap<>();
        for (OWLClass c : snapshot.getClassesInSignature()) {
            Set<OWLClass> s = new HashSet<>();
            s.add(c);
            supers.put(c, s);
        }
        for (OWLAxiom ax : snapshot.getLogicalAxioms()) {
            if (ax instanceof OWLSubClassOfAxiom) {
                OWLSubClassOfAxiom sca = (OWLSubClassOfAxiom) ax;
                if (!sca.getSubClass().isAnonymous()) {
                    OWLClass sub = sca.getSubClass().asOWLClass();
                    recordSuperExpression(sub, sca.getSuperClass(), supers, singletonNominal);
                }
            } else if (ax instanceof OWLEquivalentClassesAxiom) {
                List<OWLClassExpression> ops = new ArrayList<>(((OWLEquivalentClassesAxiom) ax).getClassExpressions());
                for (int i = 0; i < ops.size(); i++) {
                    if (ops.get(i).isAnonymous()) continue;
                    OWLClass sub = ops.get(i).asOWLClass();
                    for (int j = 0; j < ops.size(); j++) {
                        if (i != j) recordSuperExpression(sub, ops.get(j), supers, singletonNominal);
                    }
                }
            }
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Map.Entry<OWLClass, Set<OWLClass>> e : supers.entrySet()) {
                Set<OWLClass> add = new HashSet<>();
                for (OWLClass sup : e.getValue()) {
                    Set<OWLClass> s2 = supers.get(sup);
                    if (s2 != null) add.addAll(s2);
                }
                if (e.getValue().addAll(add)) changed = true;
            }
        }

        List<Set<OWLClass>> disjointGroups = new ArrayList<>();
        for (OWLAxiom ax : snapshot.getAxioms(AxiomType.DISJOINT_CLASSES)) {
            Set<OWLClass> group = new HashSet<>();
            for (OWLClassExpression ce : ((OWLDisjointClassesAxiom) ax).getClassExpressions()) {
                if (!ce.isAnonymous()) group.add(ce.asOWLClass());
            }
            if (group.size() >= 2) disjointGroups.add(group);
        }

        Map<OWLNamedIndividual, Set<OWLClass>> indTypes = new HashMap<>();
        for (OWLNamedIndividual ind : inds) indTypes.put(ind, new HashSet<>());
        for (OWLAxiom ax : snapshot.getAxioms(AxiomType.CLASS_ASSERTION)) {
            OWLClassAssertionAxiom ca = (OWLClassAssertionAxiom) ax;
            if (ca.getIndividual().isNamed() && !ca.getClassExpression().isAnonymous()) {
                OWLClass c = ca.getClassExpression().asOWLClass();
                Set<OWLClass> target = indTypes.computeIfAbsent(
                        ca.getIndividual().asOWLNamedIndividual(), k -> new HashSet<>());
                target.addAll(supers.getOrDefault(c, Collections.singleton(c)));
            }
        }

        Map<OWLNamedIndividual, Set<OWLNamedIndividual>> statedDiff = new HashMap<>();
        for (OWLNamedIndividual ind : inds) statedDiff.put(ind, new HashSet<>());
        for (OWLAxiom ax : snapshot.getAxioms(AxiomType.DIFFERENT_INDIVIDUALS)) {
            List<OWLIndividual> ops = new ArrayList<>(((OWLDifferentIndividualsAxiom) ax).getIndividuals());
            for (int i = 0; i < ops.size(); i++) {
                if (!ops.get(i).isNamed()) continue;
                OWLNamedIndividual a = ops.get(i).asOWLNamedIndividual();
                for (int j = i + 1; j < ops.size(); j++) {
                    if (!ops.get(j).isNamed()) continue;
                    OWLNamedIndividual b = ops.get(j).asOWLNamedIndividual();
                    statedDiff.computeIfAbsent(a, k -> new HashSet<>()).add(b);
                    statedDiff.computeIfAbsent(b, k -> new HashSet<>()).add(a);
                }
            }
        }

        Map<OWLObjectProperty, List<OWLClassExpression>> propDomains = new HashMap<>();
        Map<OWLObjectProperty, List<OWLClassExpression>> propRanges = new HashMap<>();
        for (OWLAxiom ax : snapshot.getAxioms(AxiomType.OBJECT_PROPERTY_DOMAIN)) {
            OWLObjectPropertyDomainAxiom d = (OWLObjectPropertyDomainAxiom) ax;
            if (!d.getProperty().isAnonymous()) {
                propDomains.computeIfAbsent(d.getProperty().asOWLObjectProperty(), k -> new ArrayList<>())
                        .add(d.getDomain());
            } else {
                propRanges.computeIfAbsent(d.getProperty().getNamedProperty(), k -> new ArrayList<>())
                        .add(d.getDomain());
            }
        }
        for (OWLAxiom ax : snapshot.getAxioms(AxiomType.OBJECT_PROPERTY_RANGE)) {
            OWLObjectPropertyRangeAxiom r = (OWLObjectPropertyRangeAxiom) ax;
            if (!r.getProperty().isAnonymous()) {
                propRanges.computeIfAbsent(r.getProperty().asOWLObjectProperty(), k -> new ArrayList<>())
                        .add(r.getRange());
            } else {
                propDomains.computeIfAbsent(r.getProperty().getNamedProperty(), k -> new ArrayList<>())
                        .add(r.getRange());
            }
        }

        List<SWRLRule> grounded = new ArrayList<>();
        boolean anyFiltered = false;
        for (SWRLRule rule : rules) {
            Set<SWRLVariable> varsSet = new LinkedHashSet<>();
            for (SWRLAtom atom : rule.getBody()) {
                if (!supportedSwrlObjectAtom(atom)) return null;
                for (SWRLArgument arg : atom.getAllArguments()) {
                    if (arg instanceof SWRLVariable) varsSet.add((SWRLVariable) arg);
                }
            }
            for (SWRLAtom atom : rule.getHead()) {
                if (!supportedSwrlObjectAtom(atom)) return null;
                for (SWRLArgument arg : atom.getAllArguments()) {
                    if (arg instanceof SWRLVariable) varsSet.add((SWRLVariable) arg);
                }
            }
            if (varsSet.isEmpty()) {
                grounded.add(rule);
                continue;
            }
            List<SWRLVariable> vars = new ArrayList<>(varsSet);
            Map<SWRLVariable, List<OWLNamedIndividual>> cands = new LinkedHashMap<>();
            Map<SWRLVariable, List<OWLClassExpression>> varReqs = new LinkedHashMap<>();
            for (SWRLVariable v : vars) {
                cands.put(v, new ArrayList<>(inds));
                varReqs.put(v, new ArrayList<>());
            }

            for (SWRLAtom atom : rule.getBody()) {
                if (atom instanceof SWRLClassAtom) {
                    SWRLClassAtom ca = (SWRLClassAtom) atom;
                    if (ca.getArgument() instanceof SWRLVariable) {
                        SWRLVariable v = (SWRLVariable) ca.getArgument();
                        varReqs.get(v).add(ca.getPredicate());
                        cands.get(v).removeIf(ind -> excludedFromExpression(
                                ind, ca.getPredicate(), indTypes, supers, disjointGroups, singletonNominal, statedDiff));
                    }
                } else if (atom instanceof SWRLObjectPropertyAtom) {
                    SWRLObjectPropertyAtom opa = (SWRLObjectPropertyAtom) atom;
                    OWLObjectPropertyExpression pe = opa.getPredicate().getSimplified();
                    OWLObjectProperty named = pe.getNamedProperty();
                    List<OWLClassExpression> doms = pe.isAnonymous()
                            ? propRanges.getOrDefault(named, Collections.emptyList())
                            : propDomains.getOrDefault(named, Collections.emptyList());
                    List<OWLClassExpression> rngs = pe.isAnonymous()
                            ? propDomains.getOrDefault(named, Collections.emptyList())
                            : propRanges.getOrDefault(named, Collections.emptyList());
                    if (opa.getFirstArgument() instanceof SWRLVariable) {
                        SWRLVariable v = (SWRLVariable) opa.getFirstArgument();
                        varReqs.get(v).addAll(doms);
                        for (OWLClassExpression dom : doms) {
                            cands.get(v).removeIf(ind -> excludedFromExpression(
                                    ind, dom, indTypes, supers, disjointGroups, singletonNominal, statedDiff));
                        }
                    }
                    if (opa.getSecondArgument() instanceof SWRLVariable) {
                        SWRLVariable v = (SWRLVariable) opa.getSecondArgument();
                        varReqs.get(v).addAll(rngs);
                        for (OWLClassExpression rng : rngs) {
                            cands.get(v).removeIf(ind -> excludedFromExpression(
                                    ind, rng, indTypes, supers, disjointGroups, singletonNominal, statedDiff));
                        }
                    }
                }
            }

            long prod = 1L;
            for (SWRLVariable v : vars) {
                int sz = cands.get(v).size();
                if (sz < inds.size()) anyFiltered = true;
                prod *= sz;
                if (prod > 512L) return null;
            }
            if (prod == 0L) {
                anyFiltered = true;
                continue;
            }
            boolean[][] disjointVars = new boolean[vars.size()][vars.size()];
            for (int i = 0; i < vars.size(); i++) {
                for (int j = i + 1; j < vars.size(); j++) {
                    if (areRequirementListsDisjoint(
                            varReqs.get(vars.get(i)), varReqs.get(vars.get(j)), supers, disjointGroups)) {
                        disjointVars[i][j] = true;
                        disjointVars[j][i] = true;
                    }
                }
            }
            List<Map<SWRLVariable, OWLNamedIndividual>> bindings = new ArrayList<>();
            bindings.add(new HashMap<>());
            for (int vi = 0; vi < vars.size(); vi++) {
                SWRLVariable v = vars.get(vi);
                List<Map<SWRLVariable, OWLNamedIndividual>> next = new ArrayList<>();
                for (Map<SWRLVariable, OWLNamedIndividual> b : bindings) {
                    for (OWLNamedIndividual ind : cands.get(v)) {
                        boolean clash = false;
                        for (int prev = 0; prev < vi; prev++) {
                            if (disjointVars[vi][prev] && ind.equals(b.get(vars.get(prev)))) {
                                clash = true;
                                break;
                            }
                        }
                        if (clash) continue;
                        Map<SWRLVariable, OWLNamedIndividual> copy = new HashMap<>(b);
                        copy.put(v, ind);
                        next.add(copy);
                    }
                }
                bindings = next;
            }
            for (Map<SWRLVariable, OWLNamedIndividual> b : bindings) {
                if (violatesIdentityAtoms(rule.getBody(), b, statedDiff)) continue;
                Set<SWRLAtom> body = new LinkedHashSet<>();
                for (SWRLAtom atom : rule.getBody()) body.add(substituteSwrlAtom(atom, b, df));
                Set<SWRLAtom> head = new LinkedHashSet<>();
                for (SWRLAtom atom : rule.getHead()) head.add(substituteSwrlAtom(atom, b, df));
                grounded.add(df.getSWRLRule(body, head));
            }
        }
        if (!anyFiltered) return null;
        KMReasoner.recordReduction("R07_swrl_rule_pregrounding");
        try {
            OWLOntologyManager mgr = org.semanticweb.owlapi.apibinding.OWLManager.createOWLOntologyManager();
            OWLOntology copy = mgr.createOntology();
            for (OWLAxiom ax : snapshot.getAxioms()) {
                if (!(ax instanceof SWRLRule)) mgr.addAxiom(copy, ax);
            }
            for (SWRLRule r : grounded) mgr.addAxiom(copy, r);
            return FlattenedOntology.functionalSyntaxOfSnapshot(copy);
        } catch (Exception e) {
            return null;
        }
    }

    private static void recordSuperExpression(
            OWLClass sub,
            OWLClassExpression expr,
            Map<OWLClass, Set<OWLClass>> supers,
            Map<OWLClass, OWLNamedIndividual> singletonNominal) {
        if (!expr.isAnonymous()) {
            supers.computeIfAbsent(sub, k -> new HashSet<>()).add(expr.asOWLClass());
        } else if (expr instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression op : ((OWLObjectIntersectionOf) expr).getOperands()) {
                recordSuperExpression(sub, op, supers, singletonNominal);
            }
        } else if (expr instanceof OWLObjectOneOf) {
            Set<OWLIndividual> inds = ((OWLObjectOneOf) expr).getIndividuals();
            if (inds.size() == 1 && inds.iterator().next().isNamed()) {
                singletonNominal.put(sub, inds.iterator().next().asOWLNamedIndividual());
            }
        }
    }

    private static boolean supportedSwrlObjectAtom(SWRLAtom atom) {
        return atom instanceof SWRLClassAtom
                || atom instanceof SWRLObjectPropertyAtom
                || atom instanceof SWRLSameIndividualAtom
                || atom instanceof SWRLDifferentIndividualsAtom;
    }

    private static boolean excludedFromExpression(
            OWLNamedIndividual ind,
            OWLClassExpression expr,
            Map<OWLNamedIndividual, Set<OWLClass>> indTypes,
            Map<OWLClass, Set<OWLClass>> supers,
            List<Set<OWLClass>> disjointGroups,
            Map<OWLClass, OWLNamedIndividual> singletonNominal,
            Map<OWLNamedIndividual, Set<OWLNamedIndividual>> statedDiff) {
        Set<OWLClass> aSups = indTypes.getOrDefault(ind, Collections.emptySet());
        if (!expr.isAnonymous()) {
            OWLClass c = expr.asOWLClass();
            OWLNamedIndividual nom = singletonNominal.get(c);
            if (nom != null && statedDiff.getOrDefault(ind, Collections.emptySet()).contains(nom)) {
                return true;
            }
            Set<OWLClass> cSups = supers.getOrDefault(c, Collections.singleton(c));
            return areClassSetsDisjoint(aSups, cSups, disjointGroups);
        }
        if (expr instanceof OWLObjectUnionOf) {
            Set<OWLClassExpression> ops = ((OWLObjectUnionOf) expr).getOperands();
            if (ops.isEmpty()) return true;
            for (OWLClassExpression op : ops) {
                if (!excludedFromExpression(ind, op, indTypes, supers, disjointGroups, singletonNominal, statedDiff)) {
                    return false;
                }
            }
            return true;
        }
        if (expr instanceof OWLObjectIntersectionOf) {
            for (OWLClassExpression op : ((OWLObjectIntersectionOf) expr).getOperands()) {
                if (excludedFromExpression(ind, op, indTypes, supers, disjointGroups, singletonNominal, statedDiff)) {
                    return true;
                }
            }
            return false;
        }
        if (expr instanceof OWLObjectOneOf) {
            Set<OWLIndividual> members = ((OWLObjectOneOf) expr).getIndividuals();
            if (members.isEmpty()) return true;
            for (OWLIndividual m : members) {
                if (!m.isNamed()) return false;
                if (!statedDiff.getOrDefault(ind, Collections.emptySet()).contains(m.asOWLNamedIndividual())) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    private static boolean areRequirementListsDisjoint(
            List<OWLClassExpression> reqsA,
            List<OWLClassExpression> reqsB,
            Map<OWLClass, Set<OWLClass>> supers,
            List<Set<OWLClass>> disjointGroups) {
        if (reqsA == null || reqsB == null) return false;
        for (OWLClassExpression a : reqsA) {
            for (OWLClassExpression b : reqsB) {
                if (areExpressionsDisjoint(a, b, supers, disjointGroups)) return true;
            }
        }
        return false;
    }

    private static boolean areExpressionsDisjoint(
            OWLClassExpression a,
            OWLClassExpression b,
            Map<OWLClass, Set<OWLClass>> supers,
            List<Set<OWLClass>> disjointGroups) {
        if (!a.isAnonymous() && !b.isAnonymous()) {
            OWLClass ca = a.asOWLClass(), cb = b.asOWLClass();
            return areClassSetsDisjoint(
                    supers.getOrDefault(ca, Collections.singleton(ca)),
                    supers.getOrDefault(cb, Collections.singleton(cb)),
                    disjointGroups);
        }
        if (a instanceof OWLObjectUnionOf) {
            Set<OWLClassExpression> ops = ((OWLObjectUnionOf) a).getOperands();
            if (ops.isEmpty()) return true;
            for (OWLClassExpression op : ops) {
                if (!areExpressionsDisjoint(op, b, supers, disjointGroups)) return false;
            }
            return true;
        }
        if (b instanceof OWLObjectUnionOf) {
            Set<OWLClassExpression> ops = ((OWLObjectUnionOf) b).getOperands();
            if (ops.isEmpty()) return true;
            for (OWLClassExpression op : ops) {
                if (!areExpressionsDisjoint(a, op, supers, disjointGroups)) return false;
            }
            return true;
        }
        return false;
    }

    private static boolean areClassSetsDisjoint(
            Set<OWLClass> supsA, Set<OWLClass> supsB, List<Set<OWLClass>> disjointGroups) {
        if (supsA.isEmpty() || supsB.isEmpty()) return false;
        for (Set<OWLClass> group : disjointGroups) {
            OWLClass matchA = null;
            for (OWLClass a : supsA) {
                if (group.contains(a)) {
                    matchA = a;
                    break;
                }
            }
            if (matchA == null) continue;
            for (OWLClass b : supsB) {
                if (!b.equals(matchA) && group.contains(b)) return true;
            }
        }
        return false;
    }

    private static boolean violatesIdentityAtoms(
            Set<SWRLAtom> body,
            Map<SWRLVariable, OWLNamedIndividual> b,
            Map<OWLNamedIndividual, Set<OWLNamedIndividual>> statedDiff) {
        for (SWRLAtom atom : body) {
            if (atom instanceof SWRLDifferentIndividualsAtom) {
                SWRLDifferentIndividualsAtom da = (SWRLDifferentIndividualsAtom) atom;
                OWLNamedIndividual i1 = resolveSwrlIArg(da.getFirstArgument(), b);
                OWLNamedIndividual i2 = resolveSwrlIArg(da.getSecondArgument(), b);
                if (i1 != null && i1.equals(i2)) return true;
            } else if (atom instanceof SWRLSameIndividualAtom) {
                SWRLSameIndividualAtom sa = (SWRLSameIndividualAtom) atom;
                OWLNamedIndividual i1 = resolveSwrlIArg(sa.getFirstArgument(), b);
                OWLNamedIndividual i2 = resolveSwrlIArg(sa.getSecondArgument(), b);
                if (i1 != null && i2 != null
                        && statedDiff.getOrDefault(i1, Collections.emptySet()).contains(i2)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static OWLNamedIndividual resolveSwrlIArg(
            SWRLIArgument arg, Map<SWRLVariable, OWLNamedIndividual> b) {
        if (arg instanceof SWRLVariable) return b.get((SWRLVariable) arg);
        if (arg instanceof SWRLIndividualArgument) {
            OWLIndividual ind = ((SWRLIndividualArgument) arg).getIndividual();
            if (ind.isNamed()) return ind.asOWLNamedIndividual();
        }
        return null;
    }

    private static SWRLAtom substituteSwrlAtom(
            SWRLAtom atom, Map<SWRLVariable, OWLNamedIndividual> b, OWLDataFactory df) {
        if (atom instanceof SWRLClassAtom) {
            SWRLClassAtom ca = (SWRLClassAtom) atom;
            return df.getSWRLClassAtom(ca.getPredicate(), subArg(ca.getArgument(), b, df));
        }
        if (atom instanceof SWRLObjectPropertyAtom) {
            SWRLObjectPropertyAtom opa = (SWRLObjectPropertyAtom) atom;
            return df.getSWRLObjectPropertyAtom(
                    opa.getPredicate(),
                    subArg(opa.getFirstArgument(), b, df),
                    subArg(opa.getSecondArgument(), b, df));
        }
        if (atom instanceof SWRLSameIndividualAtom) {
            SWRLSameIndividualAtom sa = (SWRLSameIndividualAtom) atom;
            return df.getSWRLSameIndividualAtom(
                    subArg(sa.getFirstArgument(), b, df),
                    subArg(sa.getSecondArgument(), b, df));
        }
        if (atom instanceof SWRLDifferentIndividualsAtom) {
            SWRLDifferentIndividualsAtom da = (SWRLDifferentIndividualsAtom) atom;
            return df.getSWRLDifferentIndividualsAtom(
                    subArg(da.getFirstArgument(), b, df),
                    subArg(da.getSecondArgument(), b, df));
        }
        return atom;
    }

    private static SWRLIArgument subArg(
            SWRLIArgument arg, Map<SWRLVariable, OWLNamedIndividual> b, OWLDataFactory df) {
        if (arg instanceof SWRLVariable && b.containsKey(arg)) {
            return df.getSWRLIndividualArgument(b.get(arg));
        }
        return arg;
    }
}
