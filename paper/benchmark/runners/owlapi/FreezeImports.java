package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubPropertyChainOfAxiom;

/** Resolve and materialize one fail-closed import closure for all reasoners. */
public final class FreezeImports {
    private FreezeImports() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("Usage: FreezeImports <source> <merged-output> <receipt-output>");
            System.exit(2);
        }
        Path source = new File(args[0]).toPath().toAbsolutePath();
        Path destination = new File(args[1]).toPath().toAbsolutePath();
        Path receipt = new File(args[2]).toPath().toAbsolutePath();
        if (!Files.isRegularFile(source) || Files.size(source) == 0) throw new IllegalArgumentException("missing source");
        Files.createDirectories(destination.getParent());
        Files.createDirectories(receipt.getParent());
        Path temporary = destination.resolveSibling(destination.getFileName() + ".part");
        Path receiptTemporary = receipt.resolveSibling(receipt.getFileName() + ".part");
        Files.deleteIfExists(temporary);
        Files.deleteIfExists(receiptTemporary);

        OWLOntologyLoaderConfiguration configuration = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.THROW_EXCEPTION);
        OWLOntologyManager loader = OWLManager.createOWLOntologyManager();
        OWLOntology root = loader.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(source.toFile()), configuration);
        List<OWLOntology> closure = new ArrayList<>(root.getImportsClosure());
        closure.sort(Comparator.comparing(o -> o.getOntologyID().toString()));

        OWLOntologyManager outputManager = OWLManager.createOWLOntologyManager();
        OWLOntology merged = outputManager.createOntology();
        for (OWLOntology ontology : closure) outputManager.addAxioms(merged, ontology.getAxioms());
        int normalizedInverseChainMembers = normalizeInverseChainMembers(outputManager, merged);
        outputManager.saveOntology(merged, new FunctionalSyntaxDocumentFormat(), IRI.create(temporary.toUri()));
        String mergedDigest = sha256(temporary);

        try (BufferedWriter out = Files.newBufferedWriter(receiptTemporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\tsource\t" + clean(source.toString()) + "\n");
            out.write("M\tsource_sha256\t" + sha256(source) + "\n");
            out.write("M\tclosure_size\t" + closure.size() + "\n");
            out.write("M\tmerged_axioms\t" + merged.getAxiomCount() + "\n");
            out.write("M\tnormalization\tinverse-chain-members-to-defined-named-roles-v1\n");
            out.write("M\tnormalized_inverse_chain_members\t" + normalizedInverseChainMembers + "\n");
            out.write("M\tmerged_sha256\t" + mergedDigest + "\n");
            for (OWLOntology ontology : closure) {
                IRI document = loader.getOntologyDocumentIRI(ontology);
                out.write("I\t" + clean(ontology.getOntologyID().toString()) + "\t"
                        + clean(document.toString()) + "\t" + ontology.getAxiomCount() + "\n");
            }
            out.write("Z\tcomplete\n");
        }
        Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
        Files.move(receiptTemporary, receipt, StandardCopyOption.REPLACE_EXISTING);
    }

    /**
     * Replace anonymous inverse expressions in property chains by deterministic
     * fresh role names and define each fresh role as the inverse of its base.
     * This is a conservative extension: replacing R^- by q together with
     * InverseObjectProperties(R q) preserves all entailments over the original
     * signature. Every benchmarked reasoner receives this same document.
     */
    private static int normalizeInverseChainMembers(OWLOntologyManager manager, OWLOntology ontology)
            throws Exception {
        OWLDataFactory dataFactory = manager.getOWLDataFactory();
        Map<OWLObjectProperty, OWLObjectProperty> helpers = new HashMap<>();
        List<OWLSubPropertyChainOfAxiom> remove = new ArrayList<>();
        List<OWLSubPropertyChainOfAxiom> add = new ArrayList<>();
        List<OWLInverseObjectPropertiesAxiom> definitions = new ArrayList<>();
        int replacements = 0;
        for (OWLSubPropertyChainOfAxiom axiom : ontology.getAxioms(AxiomType.SUB_PROPERTY_CHAIN_OF)) {
            List<OWLObjectPropertyExpression> rewritten = new ArrayList<>();
            boolean changed = false;
            for (OWLObjectPropertyExpression expression : axiom.getPropertyChain()) {
                if (!expression.isAnonymous()) {
                    rewritten.add(expression);
                    continue;
                }
                OWLObjectProperty base = expression.getNamedProperty();
                OWLObjectProperty helper = helpers.get(base);
                if (helper == null) {
                    String suffix = sha256Text(base.getIRI().toString());
                    helper = dataFactory.getOWLObjectProperty(
                            IRI.create("urn:km-paper:inverse-role:" + suffix));
                    if (ontology.containsObjectPropertyInSignature(helper.getIRI())) {
                        throw new IllegalArgumentException("inverse-chain helper IRI collision: " + helper.getIRI());
                    }
                    helpers.put(base, helper);
                    definitions.add(dataFactory.getOWLInverseObjectPropertiesAxiom(base, helper));
                }
                rewritten.add(helper);
                replacements++;
                changed = true;
            }
            if (changed) {
                remove.add(axiom);
                add.add(dataFactory.getOWLSubPropertyChainOfAxiom(
                        rewritten, axiom.getSuperProperty(), axiom.getAnnotations()));
            }
        }
        manager.removeAxioms(ontology, new java.util.HashSet<>(remove));
        manager.addAxioms(ontology, new java.util.HashSet<>(add));
        manager.addAxioms(ontology, new java.util.HashSet<>(definitions));
        return replacements;
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (java.io.InputStream stream = Files.newInputStream(path)) {
            byte[] buffer = new byte[8 * 1024 * 1024];
            int count;
            while ((count = stream.read(buffer)) >= 0) if (count > 0) digest.update(buffer, 0, count);
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) result.append(String.format("%02x", value & 0xff));
        return result.toString();
    }

    private static String sha256Text(String value) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] encoded = digest.digest(value.getBytes(StandardCharsets.UTF_8));
        StringBuilder result = new StringBuilder();
        for (byte element : encoded) result.append(String.format("%02x", element & 0xff));
        return result.toString();
    }

    private static String clean(String value) {
        if (value.indexOf('\t') >= 0 || value.indexOf('\n') >= 0 || value.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("receipt field contains a control separator");
        }
        return value;
    }
}
