package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.vocab.OWL2Datatype;

import java.util.*;

/**
 * The candidate literals of {@code getDataPropertyValues} and the fragment in
 * which they are complete.
 *
 * <p>The plugin answers {@code getDataPropertyValues(a, p)} with the literals
 * {@code l} occurring in the ontology for which {@code a} is an instance of
 * {@code DataHasValue(p l)}. Infinitely many literals denote each value (for
 * example {@code "1"} and {@code "01"} as integers), so no reasoner lists all
 * entailed literals; the candidates are those of the ontology, and every
 * candidate whose value is entailed is returned, also when the same value is
 * written in another way.
 *
 * <p><b>When no other value can be entailed.</b> The candidates are complete
 * when every data value {@code v} that no literal of the ontology denotes is
 * never entailed as a value. That fails for data ranges with few elements:
 * {@code xsd:nonNegativeInteger} and {@code xsd:nonPositiveInteger} meet in
 * {@code 0}, a facet restriction such as {@code xsd:integer[> 4, < 6]} holds
 * one value, and {@code xsd:boolean} has two. The fragment admits only the
 * datatypes {@code rdfs:Literal}, {@code xsd:string}, {@code rdf:PlainLiteral},
 * {@code rdf:langString}, {@code xsd:integer}, {@code xsd:decimal},
 * {@code xsd:double}, {@code xsd:float}, {@code xsd:anyURI},
 * {@code xsd:dateTime} and the sign-restricted integer types (two or more
 * of those only with a literal for 0) (with {@code DataOneOf}, {@code DataIntersectionOf},
 * {@code DataUnionOf} and {@code DataComplementOf} over them), no facet
 * restriction, datatype definition, rule or axiom with
 * {@code owl:topDataProperty}, and data restrictions whose numbers (plus one
 * each) sum to less than 2^30. Argument: call two values equivalent when they belong to the
 * same admitted datatypes and neither is the value of a candidate. Every
 * class of this equivalence is empty or has at least 2^31 elements (the
 * admitted datatypes cut the value space into the integers, the decimals
 * that are not integers, the floats, the doubles, the strings, the
 * language-tagged strings, the URIs, the date-times and the rest; only the
 * floats and doubles are finite, with more than 2^31 elements). Suppose
 * {@code O ⊨ p(a, v)} for a value {@code v} of no candidate, and take a model.
 * Restrict the data values of every element to a finite set {@code K} that
 * keeps the candidates and, for every data restriction of the ontology the
 * element satisfies, as many witnesses as its number asks for: every class
 * membership and axiom is kept (sub-properties, keys, disjointness, maximum
 * cardinalities and universal restrictions only get easier with fewer values,
 * and the witnesses keep the existential and minimum restrictions and the
 * negated universal and maximum ones). For {@code a},
 * {@code K} is smaller than 2^31, so some {@code w} equivalent to {@code v}
 * is outside {@code K}. Swapping {@code v} and {@code w} in the whole model
 * preserves every admitted datatype and fixes every candidate, so it gives a
 * model of the ontology in which {@code v} is no value of {@code a}: a
 * contradiction. Outside the fragment the query throws.
 */
final class DataValues {

    private DataValues() {}

    private static final Set<IRI> ADMITTED = new HashSet<>(Arrays.asList(
            OWL2Datatype.RDFS_LITERAL.getIRI(),
            OWL2Datatype.XSD_STRING.getIRI(),
            OWL2Datatype.RDF_PLAIN_LITERAL.getIRI(),
            IRI.create("http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"),
            OWL2Datatype.XSD_INTEGER.getIRI(),
            OWL2Datatype.XSD_DECIMAL.getIRI(),
            OWL2Datatype.XSD_DOUBLE.getIRI(),
            OWL2Datatype.XSD_FLOAT.getIRI(),
            OWL2Datatype.XSD_ANY_URI.getIRI(),
            OWL2Datatype.XSD_DATE_TIME.getIRI()));

    /**
     * Integer types that split the integers by sign. One of them next to
     * xsd:integer and xsd:decimal cuts only infinite classes; two of them can
     * isolate 0 (nonNegative ∩ nonPositive, nonNegative minus positive,
     * the integers that are neither positive nor negative), so two or more are
     * admitted only when a literal of the ontology denotes 0.
     */
    private static final Set<IRI> SIGNED = new HashSet<>(Arrays.asList(
            OWL2Datatype.XSD_NON_NEGATIVE_INTEGER.getIRI(),
            OWL2Datatype.XSD_POSITIVE_INTEGER.getIRI(),
            OWL2Datatype.XSD_NON_POSITIVE_INTEGER.getIRI(),
            OWL2Datatype.XSD_NEGATIVE_INTEGER.getIRI()));

    private static final long CARDINALITY_BOUND = 1L << 30;

    /** The candidate literals and why the ontology is outside the fragment (null when inside). */
    static final class Candidates {
        final Set<OWLLiteral> literals = new LinkedHashSet<>();
        String outside;
        long cardinalities;
        final Set<IRI> signed = new HashSet<>();
    }

    static Candidates collect(OWLOntology snapshot) {
        Candidates out = new Candidates();
        for (OWLAxiom axiom : snapshot.getLogicalAxioms()) {
            for (OWLDataProperty p : axiom.getDataPropertiesInSignature()) {
                // The universal data property relates every element to every value,
                // which the restriction to finitely many values below would break.
                if (p.isOWLTopDataProperty()) out.outside = "owl:topDataProperty in an axiom";
            }
            if (axiom instanceof SWRLRule) {
                out.outside = "a rule";
            } else if (axiom instanceof OWLDatatypeDefinitionAxiom) {
                out.outside = "a datatype definition";
            } else if (axiom instanceof OWLDataPropertyAssertionAxiom) {
                out.literals.add(((OWLDataPropertyAssertionAxiom) axiom).getObject());
            } else if (axiom instanceof OWLNegativeDataPropertyAssertionAxiom) {
                out.literals.add(((OWLNegativeDataPropertyAssertionAxiom) axiom).getObject());
            } else if (axiom instanceof OWLDataPropertyRangeAxiom) {
                range(((OWLDataPropertyRangeAxiom) axiom).getRange(), out);
            }
            for (OWLClassExpression ce : axiom.getNestedClassExpressions()) {
                if (ce instanceof OWLDataHasValue) {
                    out.literals.add(((OWLDataHasValue) ce).getFiller());
                } else if (ce instanceof OWLDataSomeValuesFrom) {
                    range(((OWLDataSomeValuesFrom) ce).getFiller(), out);
                    out.cardinalities += 1;
                } else if (ce instanceof OWLDataAllValuesFrom) {
                    range(((OWLDataAllValuesFrom) ce).getFiller(), out);
                    out.cardinalities += 1; // a witness of the negation
                } else if (ce instanceof OWLDataCardinalityRestriction) {
                    OWLDataCardinalityRestriction r = (OWLDataCardinalityRestriction) ce;
                    range(r.getFiller(), out);
                    out.cardinalities += r.getCardinality() + 1L;
                }
            }
        }
        if (out.outside == null && out.signed.size() > 1 && !denotesZero(out.literals)) {
            out.outside = "two sign-restricted integer datatypes " + out.signed + " and no literal for 0";
        }
        if (out.outside == null && out.cardinalities + out.literals.size() >= CARDINALITY_BOUND) {
            out.outside = "data cardinalities too large for the completeness argument";
        }
        return out;
    }

    private static boolean denotesZero(Set<OWLLiteral> literals) {
        for (OWLLiteral l : literals) {
            String dt = l.getDatatype().getIRI().toString();
            if (!dt.startsWith("http://www.w3.org/2001/XMLSchema#") || !(dt.endsWith("nteger")
                    || dt.endsWith("#decimal") || dt.endsWith("#int") || dt.endsWith("#long")
                    || dt.endsWith("#short") || dt.endsWith("#byte"))) continue;
            try {
                if (new java.math.BigDecimal(l.getLiteral().trim()).signum() == 0) return true;
            } catch (NumberFormatException ignored) {
                // not a numeral
            }
        }
        return false;
    }

    private static void range(OWLDataRange range, Candidates out) {
        if (range instanceof OWLDatatype) {
            OWLDatatype dt = (OWLDatatype) range;
            if (SIGNED.contains(dt.getIRI())) out.signed.add(dt.getIRI());
            else if (!ADMITTED.contains(dt.getIRI())) out.outside = "the datatype " + dt.getIRI();
        } else if (range instanceof OWLDataOneOf) {
            out.literals.addAll(((OWLDataOneOf) range).getValues());
        } else if (range instanceof OWLDataIntersectionOf) {
            for (OWLDataRange r : ((OWLDataIntersectionOf) range).getOperands()) range(r, out);
        } else if (range instanceof OWLDataUnionOf) {
            for (OWLDataRange r : ((OWLDataUnionOf) range).getOperands()) range(r, out);
        } else if (range instanceof OWLDataComplementOf) {
            range(((OWLDataComplementOf) range).getDataRange(), out);
        } else {
            out.outside = "the data range " + range;
            if (range instanceof OWLDatatypeRestriction) {
                for (OWLFacetRestriction f : ((OWLDatatypeRestriction) range).getFacetRestrictions()) {
                    out.literals.add(f.getFacetValue());
                }
            }
        }
    }
}
