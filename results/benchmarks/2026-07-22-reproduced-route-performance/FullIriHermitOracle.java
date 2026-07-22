import java.io.BufferedWriter;
import java.io.File;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.Node;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

/** Classify named classes with HermiT and retain complete class IRIs. */
public final class FullIriHermitOracle {
    private FullIriHermitOracle() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            System.err.println("Usage: FullIriHermitOracle <ontology-file>");
            System.exit(2);
        }
        File file = new File(args[0]);
        if (!file.isFile()) {
            System.err.println("File not found: " + file.getAbsolutePath());
            System.exit(2);
        }

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(file);
        OWLReasoner reasoner = new ReasonerFactory().createReasoner(ontology);
        boolean consistent = reasoner.isConsistent();
        OWLClass bottom = factory.getOWLNothing();

        Set<String> unsatisfiable = new TreeSet<>();
        Set<String> pairs = new TreeSet<>();
        if (consistent) {
            for (OWLClass cls : reasoner.getEquivalentClasses(bottom).getEntities()) {
                if (!cls.isOWLNothing()) {
                    unsatisfiable.add(cls.getIRI().toString());
                }
            }
            for (OWLClass sub : ontology.getClassesInSignature()) {
                if (sub.isOWLThing() || sub.isOWLNothing() || !reasoner.isSatisfiable(sub)) {
                    continue;
                }
                String subIri = sub.getIRI().toString();
                Node<OWLClass> equivalent = reasoner.getEquivalentClasses(sub);
                for (OWLClass other : equivalent.getEntities()) {
                    if (other.isOWLThing()) {
                        addPair(pairs, factory.getOWLThing().getIRI().toString(), subIri);
                    } else if (!other.isOWLNothing() && !other.equals(sub)) {
                        addPair(pairs, subIri, other.getIRI().toString());
                    }
                }
                NodeSet<OWLClass> supers = reasoner.getSuperClasses(sub, false);
                for (Node<OWLClass> node : supers) {
                    for (OWLClass sup : node.getEntities()) {
                        if (!sup.isOWLThing() && !sup.isOWLNothing() && !sup.equals(sub)) {
                            addPair(pairs, subIri, sup.getIRI().toString());
                        }
                    }
                }
            }
        }

        reasoner.dispose();
        PrintWriter output = new PrintWriter(
            new BufferedWriter(
                new OutputStreamWriter(System.out, StandardCharsets.UTF_8),
                1 << 16
            )
        );
        output.println("{");
        output.println("  \"ontology\": " + json(file.getName()) + ",");
        output.println("  \"consistent\": " + consistent + ",");
        output.print("  \"subsumptions\": [");
        boolean first = true;
        for (String pair : pairs) {
            int separator = pair.indexOf('\t');
            if (!first) output.print(',');
            output.print("\n    [");
            output.print(json(pair.substring(0, separator)));
            output.print(", ");
            output.print(json(pair.substring(separator + 1)));
            output.print(']');
            first = false;
        }
        if (!pairs.isEmpty()) output.print("\n  ");
        output.print("],\n  \"unsatisfiable\": [");
        first = true;
        for (String iri : unsatisfiable) {
            if (!first) output.print(',');
            output.print("\n    ");
            output.print(json(iri));
            first = false;
        }
        if (!unsatisfiable.isEmpty()) output.print("\n  ");
        output.print("]\n}\n");
        output.flush();
    }

    private static void addPair(Set<String> pairs, String sub, String sup) {
        if (!sub.equals(sup)) pairs.add(sub + "\t" + sup);
    }

    private static String json(String value) {
        StringBuilder output = new StringBuilder("\"");
        for (int index = 0; index < value.length(); index++) {
            char character = value.charAt(index);
            switch (character) {
                case '"': output.append("\\\""); break;
                case '\\': output.append("\\\\"); break;
                case '\n': output.append("\\n"); break;
                case '\r': output.append("\\r"); break;
                case '\t': output.append("\\t"); break;
                default:
                    if (character < 0x20) {
                        output.append(String.format("\\u%04x", (int) character));
                    } else {
                        output.append(character);
                    }
            }
        }
        return output.append('"').toString();
    }
}
