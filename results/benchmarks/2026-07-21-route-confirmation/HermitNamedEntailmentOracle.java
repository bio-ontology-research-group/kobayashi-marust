import java.io.File;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

/**
 * Source-bound diagnostic oracle for one named-class subsumption.
 *
 * Usage:
 *   HermitNamedEntailmentOracle ONTOLOGY SUB_IRI SUPER_IRI
 *
 * The counterexample query asks whether SUB and not SUPER is satisfiable.
 * Under OWL direct semantics it is the exact negation of SUB subClassOf SUPER.
 */
public final class HermitNamedEntailmentOracle {
    private HermitNamedEntailmentOracle() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println(
                "Usage: HermitNamedEntailmentOracle ONTOLOGY SUB_IRI SUPER_IRI"
            );
            System.exit(2);
        }

        File ontologyFile = new File(args[0]);
        if (!ontologyFile.isFile()) {
            System.err.println("Ontology not found: " + ontologyFile.getAbsolutePath());
            System.exit(2);
        }

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontologyFile);
        OWLClass sub = factory.getOWLClass(IRI.create(args[1]));
        OWLClass sup = factory.getOWLClass(IRI.create(args[2]));
        OWLReasoner reasoner = new ReasonerFactory().createReasoner(ontology);

        boolean consistent = reasoner.isConsistent();
        boolean subSatisfiable = consistent && reasoner.isSatisfiable(sub);
        boolean entailed = consistent
            && reasoner.isEntailed(factory.getOWLSubClassOfAxiom(sub, sup));
        OWLClassExpression counterexample = factory.getOWLObjectIntersectionOf(
            sub,
            factory.getOWLObjectComplementOf(sup)
        );
        boolean counterexampleSatisfiable = consistent
            && reasoner.isSatisfiable(counterexample);

        StringBuilder output = new StringBuilder();
        output.append("{\n");
        output.append("  \"ontology\": ").append(json(ontologyFile.getName())).append(",\n");
        output.append("  \"sub\": ").append(json(args[1])).append(",\n");
        output.append("  \"super\": ").append(json(args[2])).append(",\n");
        output.append("  \"consistent\": ").append(consistent).append(",\n");
        output.append("  \"sub_satisfiable\": ").append(subSatisfiable).append(",\n");
        output.append("  \"subclass_entailed\": ").append(entailed).append(",\n");
        output.append("  \"counterexample_satisfiable\": ")
            .append(counterexampleSatisfiable).append("\n");
        output.append("}\n");

        reasoner.dispose();
        System.out.print(output.toString());
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
