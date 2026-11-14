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
 * {@code xsd:dateTime}, the bounded and sign-restricted integer types
 * (as long as the intervals they cut out of the integers are unbounded,
 * covered by literals, or larger than the data restrictions can count) and {@code xsd:boolean} (only with
 * literals for both truth values) (with {@code DataOneOf}, {@code DataIntersectionOf},
 * {@code DataUnionOf} and {@code DataComplementOf} over them), no facet
 * restriction, datatype definition, rule or axiom with
 * {@code owl:topDataProperty}, and data restrictions whose numbers (plus one
 * each) sum to less than 2^30. Argument: call two values equivalent when they belong to the
 * same admitted datatypes and neither is the value of a candidate. Let
 * {@code N} be the number of candidates plus the sum of the restriction
 * numbers. Every class of this equivalence is empty or has more than
 * {@code N} elements: the admitted datatypes cut the value space into the
 * decimals that are not integers, the floats, the doubles (2^32 and 2^64
 * values, against {@code N < 2^30}), the strings, the language-tagged
 * strings, the URIs, the date-times, the rest, and intervals of integers
 * between the bounds of the integer types in use, which are checked one by
 * one ({@code integerCellsSafe}). Suppose
 * {@code O ⊨ p(a, v)} for a value {@code v} of no candidate, and take a model.
 * Restrict the data values of every element to a finite set {@code K} that
 * keeps the candidates and, for every data restriction of the ontology the
 * element satisfies, as many witnesses as its number asks for: every class
 * membership and axiom is kept (sub-properties, keys, disjointness, maximum
 * cardinalities and universal restrictions only get easier with fewer values,
 * and the witnesses keep the existential and minimum restrictions and the
 * negated universal and maximum ones). For {@code a},
 * {@code K} has at most {@code N} elements, so some {@code w} equivalent to {@code v}
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
     * The integer datatypes as intervals of integers (null: unbounded). Used
     * together they cut the integers into intervals between their bounds; such
     * an interval is a class of the completeness argument, and it must be
     * unbounded, hold no value outside the literals of the ontology, or hold
     * more values outside them than the data restrictions can ask for
     * (checked in {@link #integerCellsSafe}).
     */
    private static final Map<IRI, java.math.BigInteger[]> INTEGER_TYPES = new HashMap<>();
    static {
        java.math.BigInteger two = java.math.BigInteger.valueOf(2);
        java.math.BigInteger one = java.math.BigInteger.ONE;
        interval(OWL2Datatype.XSD_NON_NEGATIVE_INTEGER, java.math.BigInteger.ZERO, null);
        interval(OWL2Datatype.XSD_POSITIVE_INTEGER, one, null);
        interval(OWL2Datatype.XSD_NON_POSITIVE_INTEGER, null, java.math.BigInteger.ZERO);
        interval(OWL2Datatype.XSD_NEGATIVE_INTEGER, null, one.negate());
        for (Object[] t : new Object[][]{{OWL2Datatype.XSD_LONG, 63}, {OWL2Datatype.XSD_INT, 31},
                {OWL2Datatype.XSD_SHORT, 15}, {OWL2Datatype.XSD_BYTE, 7}}) {
            java.math.BigInteger m = two.pow((Integer) t[1]);
            interval((OWL2Datatype) t[0], m.negate(), m.subtract(one));
        }
        for (Object[] t : new Object[][]{{OWL2Datatype.XSD_UNSIGNED_LONG, 64}, {OWL2Datatype.XSD_UNSIGNED_INT, 32},
                {OWL2Datatype.XSD_UNSIGNED_SHORT, 16}, {OWL2Datatype.XSD_UNSIGNED_BYTE, 8}}) {
            interval((OWL2Datatype) t[0], java.math.BigInteger.ZERO, two.pow((Integer) t[1]).subtract(one));
        }
    }

    private static void interval(OWL2Datatype dt, java.math.BigInteger lo, java.math.BigInteger hi) {
        INTEGER_TYPES.put(dt.getIRI(), new java.math.BigInteger[]{lo, hi});
    }

    private static final long CARDINALITY_BOUND = 1L << 30;

    /** The candidate literals and why the ontology is outside the fragment (null when inside). */
    static final class Candidates {
        final Set<OWLLiteral> literals = new LinkedHashSet<>();
        String outside;
        long cardinalities;
        final Set<IRI> integerTypes = new HashSet<>();
        boolean booleans;
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
        // xsd:boolean has two values; with a literal for each, no unwritten
        // boolean value is left.
        if (out.outside == null && out.booleans && !(denotesBoolean(out.literals, true)
                && denotesBoolean(out.literals, false))) {
            out.outside = "xsd:boolean without literals for both truth values";
        }
        if (out.outside == null && !integerCellsSafe(out)) {
            out.outside = "the integer datatypes " + out.integerTypes
                    + " cut out a small set of integers that no literal of the ontology covers";
        }
        if (out.outside == null && out.cardinalities + out.literals.size() >= CARDINALITY_BOUND) {
            out.outside = "data cardinalities too large for the completeness argument";
        }
        return out;
    }

    private static boolean denotesBoolean(Set<OWLLiteral> literals, boolean value) {
        for (OWLLiteral l : literals) {
            if (!l.getDatatype().getIRI().equals(OWL2Datatype.XSD_BOOLEAN.getIRI())) continue;
            String t = l.getLiteral().trim();
            if (value ? (t.equals("true") || t.equals("1")) : (t.equals("false") || t.equals("0"))) return true;
        }
        return false;
    }

    /** The integer values of the candidate literals (integer types and integral decimals). */
    private static Set<java.math.BigInteger> integerValues(Set<OWLLiteral> literals) {
        Set<java.math.BigInteger> out = new HashSet<>();
        for (OWLLiteral l : literals) {
            String dt = l.getDatatype().getIRI().toString();
            boolean numeric = INTEGER_TYPES.containsKey(l.getDatatype().getIRI())
                    || dt.equals(OWL2Datatype.XSD_INTEGER.getIRI().toString())
                    || dt.equals(OWL2Datatype.XSD_DECIMAL.getIRI().toString());
            if (!numeric) continue;
            try {
                java.math.BigDecimal v = new java.math.BigDecimal(l.getLiteral().trim().replaceFirst("^\\+", ""));
                if (v.signum() == 0 || v.stripTrailingZeros().scale() <= 0) out.add(v.toBigIntegerExact());
            } catch (NumberFormatException | ArithmeticException ignored) {
                // not an integral numeral
            }
        }
        return out;
    }

    /**
     * Every interval between consecutive bounds of the integer types in use is
     * unbounded, or all its values are candidate values, or it keeps more than
     * the bound of the completeness argument outside the candidates.
     */
    private static boolean integerCellsSafe(Candidates out) {
        if (out.integerTypes.isEmpty()) return true;
        TreeSet<java.math.BigInteger> cuts = new TreeSet<>();
        for (IRI t : out.integerTypes) {
            java.math.BigInteger[] b = INTEGER_TYPES.get(t);
            if (b[0] != null) cuts.add(b[0]);
            if (b[1] != null) cuts.add(b[1].add(java.math.BigInteger.ONE));
        }
        Set<java.math.BigInteger> values = integerValues(out.literals);
        java.math.BigInteger need = java.math.BigInteger.valueOf(out.cardinalities + out.literals.size() + 1);
        java.math.BigInteger previous = null;
        for (java.math.BigInteger cut : cuts) {
            if (previous != null) {
                // the interval [previous, cut - 1]
                java.math.BigInteger size = cut.subtract(previous);
                java.math.BigInteger covered = java.math.BigInteger.ZERO;
                for (java.math.BigInteger v : values) {
                    if (v.compareTo(previous) >= 0 && v.compareTo(cut) < 0) covered = covered.add(java.math.BigInteger.ONE);
                }
                java.math.BigInteger left = size.subtract(covered);
                if (left.signum() > 0 && left.compareTo(need) <= 0) return false;
            }
            previous = cut;
        }
        return true;
    }

    private static void range(OWLDataRange range, Candidates out) {
        if (range instanceof OWLDatatype) {
            OWLDatatype dt = (OWLDatatype) range;
            if (INTEGER_TYPES.containsKey(dt.getIRI())) out.integerTypes.add(dt.getIRI());
            else if (dt.getIRI().equals(OWL2Datatype.XSD_BOOLEAN.getIRI())) out.booleans = true;
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
