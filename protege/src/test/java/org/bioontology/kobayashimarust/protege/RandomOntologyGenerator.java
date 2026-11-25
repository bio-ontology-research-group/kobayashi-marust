package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.vocab.OWL2Datatype;

import java.util.*;

/**
 * Deterministic generator of small random OWL 2 DL ontologies covering classes,
 * object and data properties, individuals, and all constructors that the
 * Protégé plugin reductions key on (reflexive, transitive, symmetric,
 * inverse, functional, inverse-functional, disjoint properties, property
 * chains, nominals, cardinalities, data ranges, keys, DL-safe rules, forest
 * ABoxes, positive RBoxes, Horn ontologies, and conservative ABoxes).
 */
public final class RandomOntologyGenerator {

    public static final String NS = "http://example.org/rand#";

    public static final class GeneratedOntology {
        public final int index;
        public final String archetype;
        public final OWLOntology ontology;
        public final List<OWLClassExpression> classExpressions = new ArrayList<>();
        public final List<OWLAxiom> entailmentAxioms = new ArrayList<>();

        GeneratedOntology(int index, String archetype, OWLOntology ontology) {
            this.index = index;
            this.archetype = archetype;
            this.ontology = ontology;
        }
    }

    private RandomOntologyGenerator() {}

    public static GeneratedOntology generate(long baseSeed, int index) {
        try {
            Random rnd = new Random(baseSeed * 6364136223846793005L + index * 1442695040888963407L + 17L);
            OWLOntologyManager m = OWLManager.createOWLOntologyManager();
            OWLDataFactory df = m.getOWLDataFactory();
            OWLOntology ont = m.createOntology(IRI.create(NS + "ont" + index));

            int family = index % 10;
            String archetype;
            switch (family) {
                case 0:
                    archetype = "forest_abox_reflexive_rollup";
                    buildForestABoxRollup(m, df, ont, rnd);
                    break;
                case 1:
                    archetype = "positive_rbox_reflexive_chains";
                    buildPositiveRBoxReflexive(m, df, ont, rnd);
                    break;
                case 2:
                    archetype = "dlsafe_swrl_rules";
                    buildSwrlRules(m, df, ont, rnd);
                    break;
                case 3:
                    archetype = "syntactic_data_property_hierarchy";
                    buildSyntacticDataProperties(m, df, ont, rnd);
                    break;
                case 4:
                    archetype = "data_properties_nominals_functional";
                    buildDataPropertiesNominalsFunctional(m, df, ont, rnd);
                    break;
                case 5:
                    archetype = "data_properties_literal_probes_disjoint";
                    buildDataPropertiesLiteralProbes(m, df, ont, rnd);
                    break;
                case 6:
                    archetype = "horn_tbox_complement_conservativity";
                    buildHornComplementAndConservativity(m, df, ont, rnd);
                    break;
                case 7:
                    archetype = "reflexive_min_cardinality";
                    buildReflexiveMinCardinality(m, df, ont, rnd);
                    break;
                case 8:
                    archetype = "haskey_nominals_cardinalities";
                    buildHasKeyAndNominals(m, df, ont, rnd);
                    break;
                default:
                    archetype = "general_alc_sroiq_mix";
                    buildGeneralMix(m, df, ont, rnd);
                    break;
            }
            GeneratedOntology out = new GeneratedOntology(index, archetype, ont);
            populateQueries(df, ont, rnd, family, out);
            return out;
        } catch (OWLOntologyCreationException e) {
            throw new IllegalStateException(e);
        }
    }

    private static OWLClass cls(OWLDataFactory df, int i) {
        return df.getOWLClass(IRI.create(NS + "C" + i));
    }

    private static OWLObjectProperty op(OWLDataFactory df, int i) {
        return df.getOWLObjectProperty(IRI.create(NS + "r" + i));
    }

    private static OWLDataProperty dp(OWLDataFactory df, int i) {
        return df.getOWLDataProperty(IRI.create(NS + "p" + i));
    }

    private static OWLNamedIndividual ind(OWLDataFactory df, int i) {
        return df.getOWLNamedIndividual(IRI.create(NS + "i" + i));
    }

    /**
     * Archetype 0: Forest-shaped ABox with ReflexiveObjectProperty, SameIndividual,
     * DifferentIndividuals, DataPropertyAssertion, and TBox axioms (hits R01, R02, R03, R04).
     */
    private static void buildForestABoxRollup(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        int nCls = 3 + rnd.nextInt(2);
        int nOp = 2 + rnd.nextInt(2);
        int nDp = 2;
        int nInd = 3 + rnd.nextInt(3);
        for (int i = 0; i < nCls; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < nOp; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        for (int i = 0; i < nDp; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, i)));
        for (int i = 0; i < nInd; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLReflexiveObjectPropertyAxiom(op(df, 0)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLSubObjectPropertyOfAxiom(op(df, 0), op(df, 1)));
        } else {
            m.addAxiom(ont, df.getOWLSubObjectPropertyOfAxiom(op(df, 1), op(df, 0)));
        }
        if (nOp >= 3 && rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLTransitiveObjectPropertyAxiom(op(df, 1)));
        }
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), cls(df, 1)));
        m.addAxiom(ont, df.getOWLDisjointClassesAxiom(cls(df, 1), cls(df, 2)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                df.getOWLObjectSomeValuesFrom(op(df, 1), cls(df, 0)), cls(df, 1)));

        m.addAxiom(ont, df.getOWLFunctionalDataPropertyAxiom(dp(df, 0)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 0),
                df.getOWLDataSomeValuesFrom(dp(df, 1), OWL2Datatype.XSD_INTEGER.getDatatype(df))));

        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 2), ind(df, 1)));
        // Directed tree edges: 0 -> 1 -> 2
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 1), ind(df, 0), ind(df, 1)));
        if (nInd >= 4) {
            m.addAxiom(ont, df.getOWLSameIndividualAxiom(ind(df, 2), ind(df, 3)));
            m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 1), ind(df, 2)));
        }
        m.addAxiom(ont, df.getOWLDataPropertyAssertionAxiom(dp(df, 0), ind(df, 0), df.getOWLLiteral("v" + rnd.nextInt(5))));
        m.addAxiom(ont, df.getOWLDataPropertyAssertionAxiom(dp(df, 0), ind(df, 1), df.getOWLLiteral("w" + rnd.nextInt(5))));
    }

    /**
     * Archetype 1: Positive RBox with ReflexiveObjectProperty, TransitiveObjectProperty,
     * SubPropertyChainOf, ObjectHasValue, ObjectHasSelf (hits R05, R06).
     */
    private static void buildPositiveRBoxReflexive(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLReflexiveObjectPropertyAxiom(op(df, 0)));
        m.addAxiom(ont, df.getOWLSubObjectPropertyOfAxiom(op(df, 0), op(df, 1)));
        m.addAxiom(ont, df.getOWLTransitiveObjectPropertyAxiom(op(df, 1)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLInverseObjectPropertiesAxiom(op(df, 0), op(df, 2)));
        } else {
            m.addAxiom(ont, df.getOWLSymmetricObjectPropertyAxiom(op(df, 2)));
        }
        m.addAxiom(ont, df.getOWLObjectPropertyDomainAxiom(op(df, 1), cls(df, 0)));
        m.addAxiom(ont, df.getOWLObjectPropertyRangeAxiom(op(df, 1), cls(df, 1)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), cls(df, 2)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 0), df.getOWLObjectHasValue(op(df, 1), ind(df, 1))));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 2), ind(df, 0), ind(df, 2)));
    }

    /**
     * Archetype 2: DL-safe SWRLRule with leaf-class domain filtering and object/data
     * properties (hits R07, R08, R25).
     */
    private static void buildSwrlRules(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 4; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, 0)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLDisjointClassesAxiom(cls(df, 0), cls(df, 1)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 2), cls(df, 3)));
        m.addAxiom(ont, df.getOWLSubObjectPropertyOfAxiom(op(df, 0), op(df, 1)));
        m.addAxiom(ont, df.getOWLObjectPropertyDomainAxiom(op(df, 0), cls(df, 0)));
        m.addAxiom(ont, df.getOWLObjectPropertyRangeAxiom(op(df, 0), cls(df, 1)));

        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 1), ind(df, 1)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 0), ind(df, 1)));
        m.addAxiom(ont, df.getOWLDataPropertyAssertionAxiom(dp(df, 0), ind(df, 0), df.getOWLLiteral("s" + rnd.nextInt(4))));

        SWRLVariable vx = df.getSWRLVariable(IRI.create(NS + "x"));
        SWRLVariable vy = df.getSWRLVariable(IRI.create(NS + "y"));
        Set<SWRLAtom> body = new LinkedHashSet<>();
        body.add(df.getSWRLClassAtom(cls(df, 0), vx));
        body.add(df.getSWRLClassAtom(cls(df, 1), vy));
        body.add(df.getSWRLObjectPropertyAtom(op(df, 0), vx, vy));
        Set<SWRLAtom> head = new LinkedHashSet<>();
        head.add(df.getSWRLClassAtom(cls(df, 2), vx));
        m.addAxiom(ont, df.getOWLFunctionalObjectPropertyAxiom(op(df, 0)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 3), df.getOWLObjectOneOf(ind(df, 0), ind(df, 1))));
        m.addAxiom(ont, df.getSWRLRule(body, head));
    }

    /**
     * Archetype 3: Pure syntactic data-property hierarchy with domains and ranges
     * (hits R09 and R11 domain-conjunction path).
     */
    private static void buildSyntacticDataProperties(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, i)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), cls(df, 1)));
        m.addAxiom(ont, df.getOWLDisjointClassesAxiom(cls(df, 1), cls(df, 2)));
        m.addAxiom(ont, df.getOWLSubDataPropertyOfAxiom(dp(df, 0), dp(df, 1)));
        m.addAxiom(ont, df.getOWLDataPropertyDomainAxiom(dp(df, 0), cls(df, 0)));
        m.addAxiom(ont, df.getOWLDataPropertyDomainAxiom(dp(df, 1), cls(df, 1)));
        m.addAxiom(ont, df.getOWLDataPropertyDomainAxiom(dp(df, 2), cls(df, 2)));
        OWLDatatype dt1 = rnd.nextBoolean()
                ? OWL2Datatype.XSD_INTEGER.getDatatype(df)
                : OWL2Datatype.XSD_NON_NEGATIVE_INTEGER.getDatatype(df);
        OWLDatatype dt2 = rnd.nextBoolean()
                ? OWL2Datatype.XSD_STRING.getDatatype(df)
                : OWL2Datatype.XSD_BOOLEAN.getDatatype(df);
        m.addAxiom(ont, df.getOWLDataPropertyRangeAxiom(dp(df, 1), dt1));
        m.addAxiom(ont, df.getOWLDataPropertyRangeAxiom(dp(df, 2), dt2));
    }

    /**
     * Archetype 4: FunctionalDataProperty + DataHasValue + ObjectOneOf (hits R12 and
     * Classifier.dataProperties native path).
     */
    private static void buildDataPropertiesNominalsFunctional(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLFunctionalDataPropertyAxiom(dp(df, 0)));
        m.addAxiom(ont, df.getOWLSubDataPropertyOfAxiom(dp(df, 1), dp(df, 0)));
        OWLLiteral lit = df.getOWLLiteral("val" + rnd.nextInt(5));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), df.getOWLDataHasValue(dp(df, 1), lit)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 1), df.getOWLObjectOneOf(ind(df, 0), ind(df, 1))));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 2), ind(df, 2)));
        m.addAxiom(ont, df.getOWLDataPropertyAssertionAxiom(dp(df, 2), ind(df, 2), df.getOWLLiteral(42)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 0), ind(df, 1)));
    }

    /**
     * Archetype 5: Data properties with DataAllValuesFrom / DataSomeValuesFrom
     * and InverseObjectProperties (hits R10 dataPropertiesByLiteralProbes and
     * R11 disjointDataProperties probeCandidates path).
     */
    private static void buildDataPropertiesLiteralProbes(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLInverseObjectPropertiesAxiom(op(df, 0), op(df, 1)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 0),
                df.getOWLDataSomeValuesFrom(dp(df, 0), OWL2Datatype.XSD_INTEGER.getDatatype(df))));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 1),
                df.getOWLDataAllValuesFrom(dp(df, 1), OWL2Datatype.XSD_STRING.getDatatype(df))));
        m.addAxiom(ont, df.getOWLDisjointDataPropertiesAxiom(dp(df, 0), dp(df, 2)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 1), ind(df, 1)));
    }

    /**
     * Archetype 6: Nominal-free Horn ontology with ABox assertions (hits R17
     * hornComplementClassAnswer and R20 tboxQuerySource conservativity).
     */
    private static void buildHornComplementAndConservativity(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 4; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, 0)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), cls(df, 1)));
        m.addAxiom(ont, df.getOWLDisjointClassesAxiom(cls(df, 1), cls(df, 2)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                df.getOWLObjectSomeValuesFrom(op(df, 0), cls(df, 0)), cls(df, 3)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 2), ind(df, 1)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 2), ind(df, 0)));
            m.addAxiom(ont, df.getOWLDataPropertyAssertionAxiom(dp(df, 0), ind(df, 0), df.getOWLLiteral("h")));
        }
    }

    /**
     * Archetype 7: ReflexiveObjectProperty + cycle in ABox (so activeRollup == null)
     * + ObjectMinCardinality(2, r, C) query (hits R18 classAnswerForMinCardinality
     * and R13 objectValuesNow).
     */
    private static void buildReflexiveMinCardinality(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLReflexiveObjectPropertyAxiom(op(df, 0)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(cls(df, 0), cls(df, 1)));
        m.addAxiom(ont, df.getOWLDisjointClassesAxiom(cls(df, 1), cls(df, 2)));
        // Cycle 0 -> 1 -> 0 prevents ForestABoxRollup so activeRollup == null
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 1), ind(df, 0), ind(df, 1)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 1), ind(df, 1), ind(df, 0)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 1), ind(df, 0), ind(df, 2)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 1)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 2)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLDifferentIndividualsAxiom(ind(df, 1), ind(df, 2)));
        }
    }

    /**
     * Archetype 8: HasKey, ObjectOneOf, ObjectMaxCardinality, DifferentIndividuals
     * (hits R14, R15, R16, R19, R25).
     */
    private static void buildHasKeyAndNominals(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 2; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, 0)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLHasKeyAxiom(cls(df, 0), op(df, 0)));
        m.addAxiom(ont, df.getOWLDisjointObjectPropertiesAxiom(op(df, 0), op(df, 1)));
        m.addAxiom(ont, df.getOWLSubClassOfAxiom(
                cls(df, 1), df.getOWLObjectMaxCardinality(1, op(df, 0), cls(df, 2))));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 0), ind(df, 1)));
        m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 0), ind(df, 2)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLObjectPropertyAssertionAxiom(op(df, 0), ind(df, 1), ind(df, 2)));
        } else {
            m.addAxiom(ont, df.getOWLDifferentIndividualsAxiom(ind(df, 0), ind(df, 1)));
        }
    }

    /**
     * Archetype 9: General ALC/SROIQ mix with DisjointUnion, FunctionalObjectProperty,
     * InverseFunctionalObjectProperty, IrreflexiveObjectProperty, AsymmetricObjectProperty,
     * NegativeObjectPropertyAssertion, NegativeDataPropertyAssertion.
     */
    private static void buildGeneralMix(
            OWLOntologyManager m, OWLDataFactory df, OWLOntology ont, Random rnd) {
        for (int i = 0; i < 4; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(cls(df, i)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(op(df, i)));
        m.addAxiom(ont, df.getOWLDeclarationAxiom(dp(df, 0)));
        for (int i = 0; i < 3; i++) m.addAxiom(ont, df.getOWLDeclarationAxiom(ind(df, i)));

        m.addAxiom(ont, df.getOWLDisjointUnionAxiom(
                cls(df, 0), new LinkedHashSet<>(Arrays.asList(cls(df, 1), cls(df, 2)))));
        m.addAxiom(ont, df.getOWLFunctionalObjectPropertyAxiom(op(df, 0)));
        if (rnd.nextBoolean()) {
            m.addAxiom(ont, df.getOWLInverseFunctionalObjectPropertyAxiom(op(df, 1)));
        } else {
            m.addAxiom(ont, df.getOWLIrreflexiveObjectPropertyAxiom(op(df, 1)));
        }
        m.addAxiom(ont, df.getOWLAsymmetricObjectPropertyAxiom(op(df, 2)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 1), ind(df, 0)));
        m.addAxiom(ont, df.getOWLClassAssertionAxiom(cls(df, 2), ind(df, 1)));
        m.addAxiom(ont, df.getOWLNegativeObjectPropertyAssertionAxiom(op(df, 0), ind(df, 0), ind(df, 1)));
        m.addAxiom(ont, df.getOWLNegativeDataPropertyAssertionAxiom(
                dp(df, 0), ind(df, 0), df.getOWLLiteral("neg")));
    }

    private static void populateQueries(
            OWLDataFactory df, OWLOntology ont, Random rnd, int family, GeneratedOntology out) {
        OWLClass c0 = cls(df, 0);
        OWLClass c1 = cls(df, 1);
        OWLClass c2 = cls(df, 2);
        OWLObjectProperty r0 = op(df, 0);
        OWLObjectProperty r1 = op(df, 1);
        OWLDataProperty p0 = dp(df, 0);
        OWLNamedIndividual i0 = ind(df, 0);
        OWLNamedIndividual i1 = ind(df, 1);

        out.classExpressions.add(df.getOWLObjectComplementOf(c0));
        out.classExpressions.add(df.getOWLObjectIntersectionOf(c0, c1));
        out.classExpressions.add(df.getOWLObjectUnionOf(c0, c1));
        if (ont.containsObjectPropertyInSignature(r0.getIRI())) {
            out.classExpressions.add(df.getOWLObjectSomeValuesFrom(r0, c0));
            out.classExpressions.add(df.getOWLObjectAllValuesFrom(r0, c1));
        }
        if (family == 7 && ont.containsObjectPropertyInSignature(r1.getIRI())) {
            out.classExpressions.add(df.getOWLObjectMinCardinality(2, r1, c0));
        }
        if (ont.containsDataPropertyInSignature(p0.getIRI())) {
            out.classExpressions.add(df.getOWLDataSomeValuesFrom(p0, df.getTopDatatype()));
        }

        // Candidate entailments covering R21, R22, R23, R24, R25
        out.entailmentAxioms.add(df.getOWLSubClassOfAxiom(
                df.getOWLObjectIntersectionOf(c0, c1), c1));
        out.entailmentAxioms.add(df.getOWLSubClassOfAxiom(c0, df.getOWLObjectUnionOf(c0, c2)));
        out.entailmentAxioms.add(df.getOWLEquivalentClassesAxiom(
                c0, df.getOWLObjectIntersectionOf(c0, df.getOWLThing())));
        out.entailmentAxioms.add(df.getOWLDisjointClassesAxiom(
                c1, df.getOWLObjectComplementOf(c1)));
        out.entailmentAxioms.add(df.getOWLDisjointUnionAxiom(
                c0, new LinkedHashSet<>(Arrays.asList(c1, c2))));

        if (ont.containsObjectPropertyInSignature(r0.getIRI())) {
            out.entailmentAxioms.add(df.getOWLObjectPropertyDomainAxiom(
                    r0, df.getOWLObjectUnionOf(c0, df.getOWLObjectComplementOf(c0))));
            out.entailmentAxioms.add(df.getOWLObjectPropertyRangeAxiom(
                    r0, df.getOWLObjectUnionOf(c1, df.getOWLObjectComplementOf(c1))));
            out.entailmentAxioms.add(df.getOWLReflexiveObjectPropertyAxiom(r0));
            out.entailmentAxioms.add(df.getOWLFunctionalObjectPropertyAxiom(r0));
            if (ont.containsObjectPropertyInSignature(r1.getIRI())) {
                out.entailmentAxioms.add(df.getOWLDisjointObjectPropertiesAxiom(r0, r1));
                out.entailmentAxioms.add(df.getOWLSubPropertyChainOfAxiom(Arrays.asList(r0, r1), r1));
            }
        }
        if (ont.containsDataPropertyInSignature(p0.getIRI())) {
            out.entailmentAxioms.add(df.getOWLDataPropertyDomainAxiom(
                    p0, df.getOWLObjectUnionOf(c0, df.getOWLObjectComplementOf(c0))));
            out.entailmentAxioms.add(df.getOWLDataPropertyRangeAxiom(
                    p0, OWL2Datatype.XSD_STRING.getDatatype(df)));
            out.entailmentAxioms.add(df.getOWLFunctionalDataPropertyAxiom(p0));
        }
        if (ont.containsIndividualInSignature(i0.getIRI())) {
            out.entailmentAxioms.add(df.getOWLClassAssertionAxiom(
                    df.getOWLObjectUnionOf(c0, c1), i0));
            if (ont.containsIndividualInSignature(i1.getIRI())) {
                out.entailmentAxioms.add(df.getOWLDifferentIndividualsAxiom(i0, i1));
                if (ont.containsObjectPropertyInSignature(r0.getIRI())) {
                    out.entailmentAxioms.add(df.getOWLObjectPropertyAssertionAxiom(r0, i0, i1));
                    out.entailmentAxioms.add(df.getOWLNegativeObjectPropertyAssertionAxiom(r0, i0, i1));
                }
            }
            if (ont.containsDataPropertyInSignature(p0.getIRI())) {
                out.entailmentAxioms.add(df.getOWLDataPropertyAssertionAxiom(
                        p0, i0, df.getOWLLiteral("probe")));
                out.entailmentAxioms.add(df.getOWLNegativeDataPropertyAssertionAxiom(
                        p0, i0, df.getOWLLiteral("probe")));
            }
        }
        if (family == 8 && ont.containsObjectPropertyInSignature(r0.getIRI())) {
            out.entailmentAxioms.add(df.getOWLHasKeyAxiom(c0, r0));
        }
        if (family == 2 && ont.containsObjectPropertyInSignature(r0.getIRI())) {
            SWRLVariable vx = df.getSWRLVariable(IRI.create(NS + "vx"));
            SWRLVariable vy = df.getSWRLVariable(IRI.create(NS + "vy"));
            Set<SWRLAtom> body = new LinkedHashSet<>();
            body.add(df.getSWRLClassAtom(c0, vx));
            body.add(df.getSWRLClassAtom(c1, vy));
            body.add(df.getSWRLObjectPropertyAtom(r0, vx, vy));
            Set<SWRLAtom> head = Collections.singleton(df.getSWRLClassAtom(cls(df, 3), vx));
            out.entailmentAxioms.add(df.getSWRLRule(body, head));
        }
    }
}
