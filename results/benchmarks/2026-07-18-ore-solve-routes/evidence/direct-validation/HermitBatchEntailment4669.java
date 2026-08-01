import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;

import org.semanticweb.HermiT.ReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

/** Adjudicate a TSV batch of named subsumptions against one HermiT instance. */
public final class HermitBatchEntailment4669 {
    private HermitBatchEntailment4669() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("Usage: HermitBatchEntailment4669 ONTOLOGY PAIRS.tsv");
            System.exit(2);
        }
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLDataFactory factory = manager.getOWLDataFactory();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(args[0]));
        OWLReasoner reasoner = new ReasonerFactory().createReasoner(ontology);
        if (!reasoner.isConsistent()) {
            throw new IllegalStateException("projected ontology is inconsistent");
        }
        try (BufferedReader input = new BufferedReader(new FileReader(args[1]))) {
            String header = input.readLine();
            if (!"sub_iri\tsuper_iri".equals(header)) {
                throw new IllegalArgumentException("unexpected pairs header: " + header);
            }
            String line;
            int index = 0;
            while ((line = input.readLine()) != null) {
                String[] fields = line.split("\\t", -1);
                if (fields.length != 2) {
                    throw new IllegalArgumentException("invalid pair row: " + line);
                }
                OWLClass sub = factory.getOWLClass(IRI.create(fields[0]));
                OWLClass sup = factory.getOWLClass(IRI.create(fields[1]));
                boolean entailed = reasoner.isEntailed(factory.getOWLSubClassOfAxiom(sub, sup));
                OWLClassExpression counterexample = factory.getOWLObjectIntersectionOf(
                    sub, factory.getOWLObjectComplementOf(sup));
                boolean counterexampleSatisfiable = reasoner.isSatisfiable(counterexample);
                if (entailed == counterexampleSatisfiable) {
                    throw new IllegalStateException("entailment/counterexample mismatch at row " + index);
                }
                System.out.println(
                    "{\"index\":" + index
                    + ",\"sub\":" + json(fields[0])
                    + ",\"super\":" + json(fields[1])
                    + ",\"entailed\":" + entailed
                    + ",\"counterexample_satisfiable\":" + counterexampleSatisfiable + "}"
                );
                System.out.flush();
                index++;
            }
        } finally {
            reasoner.dispose();
        }
    }

    private static String json(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }
}
