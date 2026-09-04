package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.profiles.OWL2ELProfile;
import org.semanticweb.owlapi.profiles.OWLProfileReport;
import org.semanticweb.owlapi.profiles.OWLProfileViolation;

/**
 * Make an explicitly labelled OWL 2 EL axiom-deletion projection.
 *
 * <p>The input must already have a frozen import closure.  In each round the
 * tool removes every complete axiom to which OWLAPI attaches an EL-profile
 * violation.  It never rewrites a class expression and fails if a violation
 * cannot be attributed to an axiom.  The result is therefore a deterministic
 * axiom subset of the supplied document, not an approximation whose
 * consequences may be described as consequences of the original ontology.</p>
 */
public final class MakeELProjection {
    private MakeELProjection() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("Usage: MakeELProjection <frozen-merged-input> <el-output> <receipt-output>");
            System.exit(2);
        }
        Path source = new File(args[0]).toPath().toAbsolutePath();
        Path destination = new File(args[1]).toPath().toAbsolutePath();
        Path receipt = new File(args[2]).toPath().toAbsolutePath();
        if (!Files.isRegularFile(source) || Files.size(source) == 0) {
            throw new IllegalArgumentException("missing frozen input");
        }
        Files.createDirectories(destination.getParent());
        Files.createDirectories(receipt.getParent());
        Path temporary = destination.resolveSibling(destination.getFileName() + ".part");
        Path receiptTemporary = receipt.resolveSibling(receipt.getFileName() + ".part");
        Files.deleteIfExists(temporary);
        Files.deleteIfExists(receiptTemporary);

        OWLOntologyLoaderConfiguration configuration = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.THROW_EXCEPTION);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(source.toFile()), configuration);
        if (!ontology.getImportsDeclarations().isEmpty() || ontology.getImportsClosure().size() != 1) {
            throw new IllegalArgumentException("input is not an import-free frozen closure");
        }

        int sourceAxioms = ontology.getAxiomCount();
        int sourceLogicalAxioms = ontology.getLogicalAxiomCount();
        int initialViolations = new OWL2ELProfile().checkOntology(ontology).getViolations().size();
        Set<OWLAxiom> removed = new HashSet<>();
        int rounds = 0;
        while (true) {
            OWLProfileReport report = new OWL2ELProfile().checkOntology(ontology);
            if (report.isInProfile()) break;
            Set<OWLAxiom> round = new HashSet<>();
            List<String> unattributed = new ArrayList<>();
            for (OWLProfileViolation violation : report.getViolations()) {
                OWLAxiom axiom = violation.getAxiom();
                if (axiom == null) unattributed.add(violation.toString());
                else round.add(axiom);
            }
            if (!unattributed.isEmpty()) {
                unattributed.sort(Comparator.naturalOrder());
                throw new IllegalArgumentException(
                        "EL violation without removable source axiom: " + unattributed.get(0));
            }
            round.removeAll(removed);
            if (round.isEmpty()) {
                throw new IllegalStateException("EL projection made no progress");
            }
            manager.removeAxioms(ontology, round);
            removed.addAll(round);
            rounds++;
        }

        manager.saveOntology(ontology, new FunctionalSyntaxDocumentFormat(), IRI.create(temporary.toUri()));
        OWLProfileReport finalReport = new OWL2ELProfile().checkOntology(ontology);
        if (!finalReport.isInProfile()) throw new IllegalStateException("output is not OWL 2 EL");

        List<String> removedRenderings = new ArrayList<>();
        for (OWLAxiom axiom : removed) removedRenderings.add(axiom.toString());
        removedRenderings.sort(Comparator.naturalOrder());
        MessageDigest removedDigest = MessageDigest.getInstance("SHA-256");
        for (String rendering : removedRenderings) {
            removedDigest.update(rendering.getBytes(StandardCharsets.UTF_8));
            removedDigest.update((byte) '\n');
        }

        try (BufferedWriter out = Files.newBufferedWriter(receiptTemporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\ttransformation\towl2el-whole-violating-axiom-deletion-v1\n");
            out.write("M\tsource\t" + clean(source.toString()) + "\n");
            out.write("M\tsource_sha256\t" + sha256(source) + "\n");
            out.write("M\tsource_axioms\t" + sourceAxioms + "\n");
            out.write("M\tsource_logical_axioms\t" + sourceLogicalAxioms + "\n");
            out.write("M\tinitial_el_violations\t" + initialViolations + "\n");
            out.write("M\tprojection_rounds\t" + rounds + "\n");
            out.write("M\tremoved_axioms\t" + removed.size() + "\n");
            out.write("M\tremoved_axioms_sha256\t" + hex(removedDigest.digest()) + "\n");
            out.write("M\toutput_axioms\t" + ontology.getAxiomCount() + "\n");
            out.write("M\toutput_logical_axioms\t" + ontology.getLogicalAxiomCount() + "\n");
            out.write("M\toutput_sha256\t" + sha256(temporary) + "\n");
            out.write("P\tOWL2EL\ttrue\t0\n");
            for (String rendering : removedRenderings) {
                byte[] encoded = rendering.getBytes(StandardCharsets.UTF_8);
                out.write("R\t" + hex(MessageDigest.getInstance("SHA-256").digest(encoded))
                        + "\t" + Base64.getEncoder().encodeToString(encoded) + "\n");
            }
            out.write("Z\tcomplete\n");
        }
        Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
        Files.move(receiptTemporary, receipt, StandardCopyOption.REPLACE_EXISTING);
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
        return hex(digest.digest());
    }

    private static String hex(byte[] bytes) {
        StringBuilder result = new StringBuilder();
        for (byte value : bytes) result.append(String.format("%02x", value & 0xff));
        return result.toString();
    }

    private static String clean(String value) {
        if (value.indexOf('\t') >= 0 || value.indexOf('\n') >= 0 || value.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("receipt field contains a control separator");
        }
        return value;
    }
}
