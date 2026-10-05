package org.kmbenchmark;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/** Independently verify one source-axiom subset-minimal subclass justification. */
public final class VerifyJustification {
    private VerifyJustification() {}
    private static boolean entails(OWLReasonerFactory factory, Set<OWLAxiom> axioms, OWLAxiom query)
            throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology ontology = manager.createOntology(axioms);
        OWLReasoner reasoner = factory.createReasoner(ontology);
        try {
            return !reasoner.isConsistent() || reasoner.isEntailed(query);
        } finally { reasoner.dispose(); }
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 6) throw new IllegalArgumentException(
            "factory source.ofn justification.ofn sub-iri super-iri receipt.tsv");
        OWLReasonerFactory factory = (OWLReasonerFactory) Class.forName(args[0])
            .getDeclaredConstructor().newInstance();
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology source = manager.loadOntologyFromOntologyDocument(new File(args[1]));
        OWLOntology justification = manager.loadOntologyFromOntologyDocument(new File(args[2]));
        if (!source.getImportsDeclarations().isEmpty() || !justification.getImportsDeclarations().isEmpty())
            throw new IllegalArgumentException("imports must be frozen before verification");
        Set<OWLAxiom> sourceLogical = new HashSet<>();
        for (OWLAxiom a : source.getLogicalAxioms()) sourceLogical.add(a.getAxiomWithoutAnnotations());
        Set<OWLAxiom> logical = new HashSet<>();
        for (OWLAxiom a : justification.getLogicalAxioms()) logical.add(a.getAxiomWithoutAnnotations());
        if (!sourceLogical.containsAll(logical)) throw new IllegalStateException("not a source subset");
        // Only source declarations are background; arbitrary annotation content is irrelevant.
        Set<OWLAxiom> background = new HashSet<>();
        for (OWLAxiom a : source.getAxioms())
            if (a.isOfType(org.semanticweb.owlapi.model.AxiomType.DECLARATION)) background.add(a);
        OWLDataFactory data = manager.getOWLDataFactory();
        OWLAxiom query = data.getOWLSubClassOfAxiom(data.getOWLClass(IRI.create(args[3])),
            data.getOWLClass(IRI.create(args[4])));
        Set<OWLAxiom> candidate = new HashSet<>(background);candidate.addAll(logical);
        if (!entails(factory, candidate, query)) throw new IllegalStateException("does not entail query");
        int checks = 1;
        for (OWLAxiom axiom : logical) {
            Set<OWLAxiom> reduced = new HashSet<>(candidate);reduced.remove(axiom);checks++;
            if (entails(factory, reduced, query)) throw new IllegalStateException("not subset-minimal");
        }
        Path output = Paths.get(args[5]);Files.createDirectories(output.toAbsolutePath().getParent());
        Files.write(output, ("M\tsource_subset\ttrue\nM\tentailed\ttrue\nM\tsubset_minimal\ttrue\nM\tchecks\t"
            + checks + "\nM\tlogical_axioms\t" + logical.size() + "\nZ\tcomplete\n").getBytes(StandardCharsets.UTF_8));
    }
}
