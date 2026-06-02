import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

/**
 * Validation oracle: classify an ontology with HermiT and emit JSON describing
 *   - whether the ontology is consistent,
 *   - all entailed atomic subsumptions A &sqsubseteq; B over named classes,
 *   - which named classes are unsatisfiable (equivalent to owl:Nothing).
 *
 * Usage: java -cp <classpath> Oracle <ontology-file>
 * Output: a single JSON object on stdout.
 */
public class Oracle {

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            System.err.println("Usage: Oracle <ontology-file>");
            System.exit(2);
        }
        File file = new File(args[0]);
        if (!file.exists()) {
            System.err.println("File not found: " + file.getAbsolutePath());
            System.exit(2);
        }

        OWLOntologyManager man = OWLManager.createOWLOntologyManager();
        OWLDataFactory df = man.getOWLDataFactory();
        OWLOntology ont = man.loadOntologyFromOntologyDocument(file);

        OWLReasoner reasoner = new ReasonerFactory().createReasoner(ont);

        boolean consistent = reasoner.isConsistent();

        OWLClass owlThing = df.getOWLThing();
        OWLClass owlNothing = df.getOWLNothing();

        // Unsatisfiable named classes = classes equivalent to owl:Nothing.
        Set<String> unsat = new TreeSet<>();
        if (consistent) {
            Node<OWLClass> bottom = reasoner.getEquivalentClasses(owlNothing);
            for (OWLClass c : bottom.getEntities()) {
                if (!c.isOWLNothing()) {
                    unsat.add(frag(c.getIRI()));
                }
            }
        }

        // Subsumptions over named classes.
        // For each named class A (satisfiable), record A SubClassOf B for every
        // named class B that strictly subsumes A (direct or indirect), plus
        // equivalences as mutual subsumptions. We skip X SubClassOf X and
        // X SubClassOf owl:Thing.
        Set<String> pairs = new TreeSet<>(); // serialized "A\tB" to dedupe
        if (consistent) {
            for (OWLClass a : ont.getClassesInSignature()) {
                if (a.isOWLThing() || a.isOWLNothing()) {
                    continue;
                }
                // Skip unsatisfiable classes (they subsume nothing meaningful;
                // they are equivalent to owl:Nothing and reported separately).
                if (!reasoner.isSatisfiable(a)) {
                    continue;
                }
                String af = frag(a.getIRI());

                // Equivalent named classes -> mutual subsumptions.
                Node<OWLClass> eq = reasoner.getEquivalentClasses(a);
                for (OWLClass e : eq.getEntities()) {
                    if (e.isOWLThing() || e.isOWLNothing() || e.equals(a)) {
                        continue;
                    }
                    String ef = frag(e.getIRI());
                    addPair(pairs, af, ef);
                    addPair(pairs, ef, af);
                }

                // All superclasses (direct + indirect), excluding owl:Thing.
                NodeSet<OWLClass> supers = reasoner.getSuperClasses(a, false);
                for (Node<OWLClass> node : supers) {
                    for (OWLClass s : node.getEntities()) {
                        if (s.isOWLThing() || s.isOWLNothing() || s.equals(a)) {
                            continue;
                        }
                        addPair(pairs, af, frag(s.getIRI()));
                    }
                }
            }
        }

        // Convert dedup set into ordered list of [sub, sup].
        List<String[]> subs = new ArrayList<>();
        for (String p : pairs) {
            int idx = p.indexOf('\t');
            subs.add(new String[]{p.substring(0, idx), p.substring(idx + 1)});
        }

        // Emit JSON.
        StringBuilder sb = new StringBuilder();
        sb.append("{\n");
        sb.append("  \"ontology\": ").append(jstr(file.getName())).append(",\n");
        sb.append("  \"consistent\": ").append(consistent).append(",\n");

        sb.append("  \"subsumptions\": [");
        for (int i = 0; i < subs.size(); i++) {
            String[] pr = subs.get(i);
            if (i > 0) sb.append(",");
            sb.append("\n    [").append(jstr(pr[0])).append(", ").append(jstr(pr[1])).append("]");
        }
        if (!subs.isEmpty()) sb.append("\n  ");
        sb.append("],\n");

        sb.append("  \"unsatisfiable\": [");
        boolean first = true;
        for (String u : unsat) {
            if (!first) sb.append(",");
            sb.append("\n    ").append(jstr(u));
            first = false;
        }
        if (!unsat.isEmpty()) sb.append("\n  ");
        sb.append("]\n");

        sb.append("}\n");

        reasoner.dispose();
        System.out.print(sb.toString());
    }

    private static void addPair(Set<String> pairs, String sub, String sup) {
        if (!sub.equals(sup)) {
            pairs.add(sub + "\t" + sup);
        }
    }

    /** Short fragment after '#', or after last '/' if no '#'. Falls back to full IRI. */
    private static String frag(IRI iri) {
        String s = iri.toString();
        int h = s.lastIndexOf('#');
        if (h >= 0 && h < s.length() - 1) {
            return s.substring(h + 1);
        }
        int sl = s.lastIndexOf('/');
        if (sl >= 0 && sl < s.length() - 1) {
            return s.substring(sl + 1);
        }
        return s;
    }

    private static String jstr(String s) {
        StringBuilder b = new StringBuilder("\"");
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"': b.append("\\\""); break;
                case '\\': b.append("\\\\"); break;
                case '\n': b.append("\\n"); break;
                case '\r': b.append("\\r"); break;
                case '\t': b.append("\\t"); break;
                default:
                    if (c < 0x20) b.append(String.format("\\u%04x", (int) c));
                    else b.append(c);
            }
        }
        b.append("\"");
        return b.toString();
    }
}
