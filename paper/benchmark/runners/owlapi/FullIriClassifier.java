package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/**
 * Common OWLAPI classification runner for the paper baselines.
 *
 * The output is written atomically and is valid only when its final record is
 * {@code Z\tcomplete}. Pair records use {@code S\t<sub>\t<super>} and
 * unsatisfiable-class records use {@code U\t<iri>}. IRIs are complete and the
 * records are sorted, making the file directly comparable by digest.
 */
public final class FullIriClassifier {
    private FullIriClassifier() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("Usage: FullIriClassifier <factory-class> <ontology> <output>");
            System.exit(2);
        }
        String factoryClass = args[0];
        Path ontologyPath = new File(args[1]).toPath().toAbsolutePath();
        Path outputPath = new File(args[2]).toPath().toAbsolutePath();
        if (!Files.isRegularFile(ontologyPath) || Files.size(ontologyPath) == 0) {
            throw new IllegalArgumentException("missing or empty ontology: " + ontologyPath);
        }
        Files.createDirectories(outputPath.getParent());
        Path temporary = outputPath.resolveSibling(outputPath.getFileName() + ".part");
        Files.deleteIfExists(temporary);

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(ontologyPath.toFile());
        Object instance = Class.forName(factoryClass).getDeclaredConstructor().newInstance();
        if (!(instance instanceof OWLReasonerFactory)) {
            throw new IllegalArgumentException(factoryClass + " is not an OWLReasonerFactory");
        }
        OWLReasonerFactory reasonerFactory = (OWLReasonerFactory) instance;
        OWLReasoner reasoner = reasonerFactory.createReasoner(ontology);
        boolean consistent;
        Set<String> pairs = new TreeSet<>();
        Set<String> unsatisfiable = new TreeSet<>();
        try {
            consistent = reasoner.isConsistent();
            if (consistent) {
                reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);
                for (OWLClass cls : reasoner.getUnsatisfiableClasses().getEntitiesMinusBottom()) {
                    unsatisfiable.add(cls.getIRI().toString());
                }
                for (OWLClass sub : ontology.getClassesInSignature(Imports.INCLUDED)) {
                    if (sub.isOWLThing() || sub.isOWLNothing() || unsatisfiable.contains(sub.getIRI().toString())) {
                        continue;
                    }
                    String subIri = sub.getIRI().toString();
                    for (OWLClass equivalent : reasoner.getEquivalentClasses(sub).getEntities()) {
                        addPair(pairs, subIri, equivalent);
                    }
                    for (OWLClass sup : reasoner.getSuperClasses(sub, false).getFlattened()) {
                        addPair(pairs, subIri, sup);
                    }
                }
            }
        } finally {
            reasoner.dispose();
        }

        try (BufferedWriter out = Files.newBufferedWriter(temporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\tfactory\t" + clean(factoryClass) + "\n");
            String reasonerName = reasonerFactory.getReasonerName();
            out.write("M\treasoner\t" + clean(reasonerName == null ? factoryClass : reasonerName) + "\n");
            out.write("C\t" + consistent + "\n");
            for (String iri : unsatisfiable) out.write("U\t" + clean(iri) + "\n");
            for (String pair : pairs) out.write("S\t" + pair + "\n");
            out.write("M\tclasses\t" + ontology.getClassesInSignature(Imports.INCLUDED).size() + "\n");
            out.write("M\tunsatisfiable\t" + unsatisfiable.size() + "\n");
            out.write("M\tsubsumptions\t" + pairs.size() + "\n");
            out.write("Z\tcomplete\n");
        }
        try {
            Files.move(temporary, outputPath, StandardCopyOption.ATOMIC_MOVE, StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException ignored) {
            Files.move(temporary, outputPath, StandardCopyOption.REPLACE_EXISTING);
        }
    }

    private static void addPair(Set<String> pairs, String sub, OWLClass sup) {
        if (!sup.isOWLThing() && !sup.isOWLNothing()) {
            String supIri = sup.getIRI().toString();
            if (!sub.equals(supIri)) pairs.add(clean(sub) + "\t" + clean(supIri));
        }
    }

    private static String clean(String value) {
        if (value.indexOf('\t') >= 0 || value.indexOf('\n') >= 0 || value.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("record field contains a control separator");
        }
        return value;
    }
}
