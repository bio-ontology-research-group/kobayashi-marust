import java.io.File;
import java.util.*;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;

/**
 * Print HermiT's object property hierarchy, bottom properties, domains and
 * ranges in the canonical row form of `km classify --lines --properties`:
 *
 *   SUBPROP r f   r named, f a named property or ObjectInverseOf(s), r != f,
 *                 O |= r SubPropertyOf f (owl:topObjectProperty is never listed)
 *   TOPPROP r     r is equivalent to owl:topObjectProperty
 *   BOTPROP r     r is equivalent to owl:bottomObjectProperty (no SUBPROP,
 *                 DOMAIN or RANGE rows)
 *   DOMAIN r C    O |= ObjectPropertyDomain(r C), C named, not owl:Thing
 *   RANGE r C     O |= ObjectPropertyRange(r C), C named, not owl:Thing
 *
 * Every row is decided by isEntailed / the hierarchy queries, then sorted.
 * Usage: HermitProps <ontology> [--entail]  (--entail decides SUBPROP by
 * isEntailed for every pair, otherwise by getSuperObjectProperties).
 */
public class HermitProps {
    static String name(OWLObjectPropertyExpression e) {
        if (e.isAnonymous()) {
            return "ObjectInverseOf(" + e.getNamedProperty().getIRI().toString() + ")";
        }
        return e.asOWLObjectProperty().getIRI().toString();
    }

    public static void main(String[] args) throws Exception {
        boolean entail = args.length > 1 && args[1].equals("--entail");
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLOntology o = m.loadOntologyFromOntologyDocument(new File(args[0]));
        OWLDataFactory df = m.getOWLDataFactory();
        Configuration c = new Configuration();
        c.ignoreUnsupportedDatatypes = false;
        Reasoner r = new Reasoner(c, o);
        TreeSet<String> rows = new TreeSet<>();
        if (!r.isConsistent()) {
            System.out.println("CONSISTENT 0");
            return;
        }
        System.out.println("CONSISTENT 1");
        r.precomputeInferences(InferenceType.CLASS_HIERARCHY, InferenceType.OBJECT_PROPERTY_HIERARCHY);
        OWLObjectProperty top = df.getOWLTopObjectProperty();
        OWLObjectProperty bot = df.getOWLBottomObjectProperty();
        OWLClass thing = df.getOWLThing();
        List<OWLObjectProperty> named = new ArrayList<>();
        for (OWLObjectProperty p : o.getObjectPropertiesInSignature(org.semanticweb.owlapi.model.parameters.Imports.INCLUDED)) {
            if (!p.equals(top) && !p.equals(bot)) named.add(p);
        }
        Set<OWLObjectPropertyExpression> namedSet = new HashSet<>(named);
        Set<OWLObjectPropertyExpression> bottom = new HashSet<>(r.getEquivalentObjectProperties(bot).getEntities());
        Set<OWLObjectPropertyExpression> topNode = new HashSet<>(r.getEquivalentObjectProperties(top).getEntities());
        Set<OWLClass> thingNode = new HashSet<>(r.getEquivalentClasses(thing).getEntities());
        for (OWLObjectProperty p : named) {
            String pn = name(p);
            if (topNode.contains(p)) rows.add("TOPPROP\t" + pn);
            if (bottom.contains(p)) {
                rows.add("BOTPROP\t" + pn);
                continue;
            }
            Set<OWLObjectPropertyExpression> sups = new HashSet<>();
            if (entail) {
                for (OWLObjectProperty q : named) {
                    for (OWLObjectPropertyExpression f : new OWLObjectPropertyExpression[]{q, q.getInverseProperty()}) {
                        if (f.equals(p)) continue;
                        if (r.isEntailed(df.getOWLSubObjectPropertyOfAxiom(p, f))) sups.add(f);
                    }
                }
            } else {
                sups.addAll(r.getSuperObjectProperties(p, false).getFlattened());
                sups.addAll(r.getEquivalentObjectProperties(p).getEntities());
            }
            for (OWLObjectPropertyExpression f : sups) {
                OWLObjectPropertyExpression simple = f.getSimplified();
                if (simple.equals(p) || simple.equals(top) || simple.equals(bot)) continue;
                if (!namedSet.contains(simple.getNamedProperty())) continue;
                rows.add("SUBPROP\t" + pn + "\t" + name(simple));
            }
            for (OWLClass d : r.getObjectPropertyDomains(p, false).getFlattened()) {
                if (!d.equals(thing) && !d.isOWLNothing()) rows.add("DOMAIN\t" + pn + "\t" + d.getIRI());
            }
            for (OWLClass d : r.getObjectPropertyRanges(p, false).getFlattened()) {
                if (!d.equals(thing) && !d.isOWLNothing()) rows.add("RANGE\t" + pn + "\t" + d.getIRI());
            }
            // getObjectPropertyDomains(p, false) omits the equivalents of the
            // domain itself; add the classes equivalent to the exact domain.
            OWLClassExpression dom = df.getOWLObjectSomeValuesFrom(p, thing);
            for (OWLClass d : r.getEquivalentClasses(dom).getEntities()) {
                if (!d.equals(thing) && !d.isOWLNothing()) rows.add("DOMAIN\t" + pn + "\t" + d.getIRI());
            }
            OWLClassExpression ran = df.getOWLObjectSomeValuesFrom(p.getInverseProperty(), thing);
            for (OWLClass d : r.getEquivalentClasses(ran).getEntities()) {
                if (!d.equals(thing) && !d.isOWLNothing()) rows.add("RANGE\t" + pn + "\t" + d.getIRI());
            }
        }
        for (String row : rows) System.out.println(row);
        r.dispose();
    }
}
