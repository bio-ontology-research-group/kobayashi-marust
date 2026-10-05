package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
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
    private static void preserveAnonymousIds(OWLOntologyManager manager) throws Exception {
        try {
            Object configurator = OWLOntologyManager.class.getMethod("getOntologyConfigurator").invoke(manager);
            configurator.getClass().getMethod("withRemapAllAnonymousIndividualsIds", boolean.class)
                .invoke(configurator, false);
        } catch (NoSuchMethodException legacyApi) {
            Class.forName("org.semanticweb.owlapi.io.AnonymousIndividualProperties")
                .getMethod("setRemapAllAnonymousIndividualsIds", boolean.class).invoke(null, false);
        }
    }


    public static void main(String[] args) throws Exception {
        if (args.length < 6 || args.length > 8) {
            System.err.println("Usage: EntailmentExplanation <factory> <ontology> "
                + "<sub-iri> <super-iri> <module.ofn> <explanation.tsv> [hierarchy-deletion] [frozen-module]");
            System.exit(2);
        }
        Set<String> options = new HashSet<>();
        for (int i = 6; i < args.length; i++) {
            if (!(args[i].equals("hierarchy-deletion") || args[i].equals("frozen-module"))
                    || !options.add(args[i])) throw new IllegalArgumentException("unknown or duplicate option");
        }
        boolean hierarchyDeletion = options.contains("hierarchy-deletion");
        boolean frozenModule = options.contains("frozen-module");
        Path ontologyPath = new File(args[1]).toPath().toAbsolutePath();
        Path modulePath = new File(args[4]).toPath().toAbsolutePath();
        Path explanationPath = new File(args[5]).toPath().toAbsolutePath();
        Files.createDirectories(modulePath.getParent());
        Files.createDirectories(explanationPath.getParent());

        long started = System.nanoTime();
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        preserveAnonymousIds(manager);
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontologyPath.toFile());
        if (!ontology.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        OWLDataFactory data = manager.getOWLDataFactory();
        OWLClass sub = data.getOWLClass(IRI.create(args[2]));
        OWLClass sup = data.getOWLClass(IRI.create(args[3]));
        Set<org.semanticweb.owlapi.model.OWLEntity> signature =
            new HashSet<>(Arrays.asList(sub, sup));
        OWLOntology module;
        if (frozenModule) {
            module = ontology;
            if (!ontologyPath.normalize().equals(modulePath.normalize()))
                Files.copy(ontologyPath, modulePath, java.nio.file.StandardCopyOption.REPLACE_EXISTING);
        } else {
            SyntacticLocalityModuleExtractor extractor =
                new SyntacticLocalityModuleExtractor(manager, ontology, ModuleType.STAR);
            module = extractor.extractAsOntology(signature, IRI.create("urn:km:disagreement-module"));
            manager.saveOntology(module, new FunctionalSyntaxDocumentFormat(), IRI.create(modulePath.toUri()));
        }

        long prepared = System.nanoTime();
        Object instance = Class.forName(args[0]).getDeclaredConstructor().newInstance();
        if (!(instance instanceof OWLReasonerFactory)) {
            throw new IllegalArgumentException("factory is not an OWLReasonerFactory");
        }
        OWLReasonerFactory factory = (OWLReasonerFactory) instance;
        OWLAxiom query = data.getOWLSubClassOfAxiom(sub, sup);
        Set<OWLAxiom> explanation = new HashSet<>();
        boolean entailed;
        if (hierarchyDeletion) {
            Set<OWLAxiom> retained = new HashSet<>(module.getAxioms());
            entailed = hierarchyEntails(factory, retained, sub, sup);
            if (entailed) {
                List<OWLAxiom> candidates = new ArrayList<>(module.getLogicalAxioms());
                candidates.sort(Comparator.comparing(Object::toString));
                for (OWLAxiom axiom : candidates) {
                    retained.remove(axiom);
                    if (!hierarchyEntails(factory, retained, sub, sup)) retained.add(axiom);
                }
                for (OWLAxiom axiom : retained) if (axiom.isLogicalAxiom()) explanation.add(axiom);
            }
        } else {
            OWLReasoner reasoner = factory.createReasoner(module);
            try {
                entailed = reasoner.isEntailed(query);
                if (entailed) {
                    OWLClassExpression witness = data.getOWLObjectIntersectionOf(
                        sub, data.getOWLObjectComplementOf(sup));
                    BlackBoxExplanation generator = new BlackBoxExplanation(module, factory, reasoner);
                    try { explanation.addAll(generator.getExplanation(witness)); }
                    finally { generator.dispose(); }
                }
            } finally { reasoner.dispose(); }
        }

        long explained = System.nanoTime();
        Set<OWLAxiom> published = new HashSet<>(explanation);
        for (OWLAxiom axiom : ontology.getAxioms()) {
            if (!axiom.isLogicalAxiom()) published.add(axiom);
        }
        OWLOntology justification = manager.createOntology(published);
        manager.saveOntology(justification, new FunctionalSyntaxDocumentFormat(),
            IRI.create(explanationPath.resolveSibling(explanationPath.getFileName() + ".ofn").toUri()));

        TreeSet<String> rendered = new TreeSet<>();
        for (OWLAxiom axiom : explanation) rendered.add(axiom.toString());
        try (BufferedWriter out = Files.newBufferedWriter(
                explanationPath, StandardCharsets.UTF_8)) {
            out.write("M\tmethod\t" + (hierarchyDeletion ? "hierarchy-source-deletion" : "owlapi-black-box") + "\n");
            out.write("M\tmodule_preparation\t" + (frozenModule ? "frozen-input" : "star-extraction") + "\n");
            out.write("M\tprepare_ns\t" + (prepared - started) + "\n");
            out.write("M\texplain_ns\t" + (explained - prepared) + "\n");
            out.write("M\tmodule_logical_axioms\t" + module.getLogicalAxiomCount() + "\n");
            out.write("M\tmodule_axioms\t" + module.getAxiomCount() + "\n");
            out.write("M\tentailed\t" + entailed + "\n");
            out.write("M\texplanation_axioms\t" + rendered.size() + "\n");
            for (String axiom : rendered) out.write("A\t" + clean(axiom) + "\n");
            out.write("Z\tcomplete\n");
        }
    }

    private static boolean hierarchyEntails(OWLReasonerFactory factory, Set<OWLAxiom> axioms,
            OWLClass sub, OWLClass sup) throws Exception {
        if (sub.equals(sup) || sub.isOWLNothing() || sup.isOWLThing()) return true;
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        preserveAnonymousIds(manager);
        OWLOntology ontology = manager.createOntology(axioms);
        OWLReasoner reasoner = factory.createReasoner(ontology);
        try {
            if (!reasoner.isConsistent()) return true;
            return reasoner.getUnsatisfiableClasses().contains(sub)
                || reasoner.getEquivalentClasses(sub).contains(sup)
                || reasoner.getSuperClasses(sub, false).containsEntity(sup);
        } finally { reasoner.dispose(); }
    }

    private static String clean(String value) {
        return value.replace('\t', ' ').replace('\n', ' ').replace('\r', ' ');
    }
}
