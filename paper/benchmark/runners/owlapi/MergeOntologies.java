package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/** Deterministically union the axioms of two import-free frozen OWL documents. */
public final class MergeOntologies {
    private MergeOntologies() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 4) {
            System.err.println("Usage: MergeOntologies <left> <right> <merged-output> <receipt-output>");
            System.exit(2);
        }
        Path leftPath = new File(args[0]).toPath().toAbsolutePath();
        Path rightPath = new File(args[1]).toPath().toAbsolutePath();
        Path destination = new File(args[2]).toPath().toAbsolutePath();
        Path receipt = new File(args[3]).toPath().toAbsolutePath();
        requireInput(leftPath);
        requireInput(rightPath);
        Files.createDirectories(destination.getParent());
        Files.createDirectories(receipt.getParent());
        Path temporary = destination.resolveSibling(destination.getFileName() + ".part");
        Path receiptTemporary = receipt.resolveSibling(receipt.getFileName() + ".part");
        Files.deleteIfExists(temporary);
        Files.deleteIfExists(receiptTemporary);

        OWLOntologyLoaderConfiguration configuration = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.THROW_EXCEPTION);
        OWLOntologyManager leftManager = OWLManager.createOWLOntologyManager();
        OWLOntology left = leftManager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(leftPath.toFile()), configuration);
        OWLOntologyManager rightManager = OWLManager.createOWLOntologyManager();
        OWLOntology right = rightManager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(rightPath.toFile()), configuration);
        requireFrozen(left, "left");
        requireFrozen(right, "right");

        OWLOntologyManager outputManager = OWLManager.createOWLOntologyManager();
        OWLOntology merged = outputManager.createOntology();
        outputManager.addAxioms(merged, left.getAxioms());
        outputManager.addAxioms(merged, right.getAxioms());
        outputManager.saveOntology(merged, new FunctionalSyntaxDocumentFormat(), IRI.create(temporary.toUri()));

        try (BufferedWriter out = Files.newBufferedWriter(receiptTemporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\ttransformation\taxiom-union-v1\n");
            out.write("M\tleft\t" + clean(leftPath.toString()) + "\n");
            out.write("M\tleft_sha256\t" + sha256(leftPath) + "\n");
            out.write("M\tleft_axioms\t" + left.getAxiomCount() + "\n");
            out.write("M\tright\t" + clean(rightPath.toString()) + "\n");
            out.write("M\tright_sha256\t" + sha256(rightPath) + "\n");
            out.write("M\tright_axioms\t" + right.getAxiomCount() + "\n");
            out.write("M\tmerged_axioms\t" + merged.getAxiomCount() + "\n");
            out.write("M\tmerged_sha256\t" + sha256(temporary) + "\n");
            out.write("Z\tcomplete\n");
        }
        Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
        Files.move(receiptTemporary, receipt, StandardCopyOption.REPLACE_EXISTING);
    }

    private static void requireInput(Path path) throws Exception {
        if (!Files.isRegularFile(path) || Files.size(path) == 0) {
            throw new IllegalArgumentException("missing input: " + path);
        }
    }

    private static void requireFrozen(OWLOntology ontology, String label) {
        if (!ontology.getImportsDeclarations().isEmpty() || ontology.getImportsClosure().size() != 1) {
            throw new IllegalArgumentException(label + " input is not an import-free frozen closure");
        }
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (java.io.InputStream stream = Files.newInputStream(path)) {
            byte[] buffer = new byte[8 * 1024 * 1024];
            int count;
            while ((count = stream.read(buffer)) >= 0) {
                if (count > 0) digest.update(buffer, 0, count);
            }
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) result.append(String.format("%02x", value & 0xff));
        return result.toString();
    }

    private static String clean(String value) {
        if (value.indexOf('\t') >= 0 || value.indexOf('\n') >= 0 || value.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("receipt field contains a control separator");
        }
        return value;
    }
}
