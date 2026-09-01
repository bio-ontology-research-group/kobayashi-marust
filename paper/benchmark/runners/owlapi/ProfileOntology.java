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
import java.util.List;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.profiles.OWL2DLProfile;
import org.semanticweb.owlapi.profiles.OWL2ELProfile;
import org.semanticweb.owlapi.profiles.OWL2Profile;
import org.semanticweb.owlapi.profiles.OWL2QLProfile;
import org.semanticweb.owlapi.profiles.OWL2RLProfile;
import org.semanticweb.owlapi.profiles.OWLProfile;
import org.semanticweb.owlapi.profiles.OWLProfileReport;
import org.semanticweb.owlapi.profiles.OWLProfileViolation;

/** Produce an atomic, machine-readable OWL profile receipt for a frozen input. */
public final class ProfileOntology {
    private ProfileOntology() {}

    private static final class Result {
        final String id;
        final OWLProfileReport report;
        Result(String id, OWLProfileReport report) { this.id = id; this.report = report; }
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 2) {
            System.err.println("Usage: ProfileOntology <merged-ontology> <receipt-output>");
            System.exit(2);
        }
        Path source = new File(args[0]).toPath().toAbsolutePath();
        Path receipt = new File(args[1]).toPath().toAbsolutePath();
        if (!Files.isRegularFile(source) || Files.size(source) == 0) {
            throw new IllegalArgumentException("missing merged ontology");
        }
        Files.createDirectories(receipt.getParent());
        Path temporary = receipt.resolveSibling(receipt.getFileName() + ".part");
        Files.deleteIfExists(temporary);

        OWLOntologyLoaderConfiguration configuration = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.THROW_EXCEPTION);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(source.toFile()), configuration);

        List<Result> results = new ArrayList<>();
        results.add(check("OWL2", new OWL2Profile(), ontology));
        results.add(check("OWL2DL", new OWL2DLProfile(), ontology));
        results.add(check("OWL2EL", new OWL2ELProfile(), ontology));
        results.add(check("OWL2QL", new OWL2QLProfile(), ontology));
        results.add(check("OWL2RL", new OWL2RLProfile(), ontology));

        try (BufferedWriter out = Files.newBufferedWriter(temporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\tsource\t" + clean(source.toString()) + "\n");
            out.write("M\tsource_sha256\t" + sha256(source) + "\n");
            out.write("M\taxioms\t" + ontology.getAxiomCount() + "\n");
            out.write("M\tlogical_axioms\t" + ontology.getLogicalAxiomCount() + "\n");
            out.write("M\tclasses\t" + ontology.getClassesInSignature().size() + "\n");
            out.write("M\tobject_properties\t" + ontology.getObjectPropertiesInSignature().size() + "\n");
            out.write("M\tdata_properties\t" + ontology.getDataPropertiesInSignature().size() + "\n");
            out.write("M\tindividuals\t" + ontology.getIndividualsInSignature().size() + "\n");
            for (Result result : results) {
                List<String> violations = new ArrayList<>();
                for (OWLProfileViolation violation : result.report.getViolations()) {
                    violations.add(clean(violation.getClass().getSimpleName()));
                }
                violations.sort(Comparator.naturalOrder());
                out.write("P\t" + result.id + "\t" + result.report.isInProfile()
                        + "\t" + violations.size() + "\n");
                String previous = null;
                int count = 0;
                for (String violation : violations) {
                    if (previous != null && !previous.equals(violation)) {
                        out.write("V\t" + result.id + "\t" + previous + "\t" + count + "\n");
                        count = 0;
                    }
                    previous = violation;
                    count++;
                }
                if (previous != null) {
                    out.write("V\t" + result.id + "\t" + previous + "\t" + count + "\n");
                }
            }
            out.write("Z\tcomplete\n");
        }
        Files.move(temporary, receipt, StandardCopyOption.REPLACE_EXISTING);
    }

    private static Result check(String id, OWLProfile profile, OWLOntology ontology) {
        return new Result(id, profile.checkOntology(ontology));
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
