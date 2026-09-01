package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

import com.clarkparsia.owlapi.explanation.BlackBoxExplanation;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

/** Extract a STAR module and one black-box justification for A subclass B. */
public final class EntailmentExplanation {
    private EntailmentExplanation() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 6) {
            System.err.println("Usage: EntailmentExplanation <factory> <ontology> "
                + "<sub-iri> <super-iri> <module.ofn> <explanation.tsv>");
            System.exit(2);
        }
        Path ontologyPath = new File(args[1]).toPath().toAbsolutePath();
        Path modulePath = new File(args[4]).toPath().toAbsolutePath();
        Path explanationPath = new File(args[5]).toPath().toAbsolutePath();
        Files.createDirectories(modulePath.getParent());
        Files.createDirectories(explanationPath.getParent());

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontologyPath.toFile());
        OWLDataFactory data = manager.getOWLDataFactory();
        OWLClass sub = data.getOWLClass(IRI.create(args[2]));
        OWLClass sup = data.getOWLClass(IRI.create(args[3]));
        Set<org.semanticweb.owlapi.model.OWLEntity> signature =
            new HashSet<>(Arrays.asList(sub, sup));
        SyntacticLocalityModuleExtractor extractor =
            new SyntacticLocalityModuleExtractor(manager, ontology, ModuleType.STAR);
        OWLOntology module = extractor.extractAsOntology(
            signature, IRI.create("urn:km:disagreement-module"));
        manager.saveOntology(module, new FunctionalSyntaxDocumentFormat(),
                             IRI.create(modulePath.toUri()));

        Object instance = Class.forName(args[0]).getDeclaredConstructor().newInstance();
        if (!(instance instanceof OWLReasonerFactory)) {
            throw new IllegalArgumentException("factory is not an OWLReasonerFactory");
        }
        OWLReasonerFactory factory = (OWLReasonerFactory) instance;
        OWLAxiom query = data.getOWLSubClassOfAxiom(sub, sup);
        OWLReasoner reasoner = factory.createReasoner(module);
        boolean entailed = reasoner.isEntailed(query);
        Set<OWLAxiom> explanation = new HashSet<>();
        if (entailed) {
            OWLClassExpression witness = data.getOWLObjectIntersectionOf(
                sub, data.getOWLObjectComplementOf(sup));
            BlackBoxExplanation generator =
                new BlackBoxExplanation(module, factory, reasoner);
            try {
                explanation.addAll(generator.getExplanation(witness));
            } finally {
                generator.dispose();
            }
        } else {
            reasoner.dispose();
        }

        TreeSet<String> rendered = new TreeSet<>();
        for (OWLAxiom axiom : explanation) rendered.add(axiom.toString());
        try (BufferedWriter out = Files.newBufferedWriter(
                explanationPath, StandardCharsets.UTF_8)) {
            out.write("M\tmodule_logical_axioms\t" + module.getLogicalAxiomCount() + "\n");
            out.write("M\tmodule_axioms\t" + module.getAxiomCount() + "\n");
            out.write("M\tentailed\t" + entailed + "\n");
            out.write("M\texplanation_axioms\t" + rendered.size() + "\n");
            for (String axiom : rendered) out.write("A\t" + clean(axiom) + "\n");
            out.write("Z\tcomplete\n");
        }
    }

    private static String clean(String value) {
        return value.replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
    }
}
