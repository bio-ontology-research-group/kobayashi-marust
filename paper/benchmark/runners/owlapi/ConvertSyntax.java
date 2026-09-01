package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.formats.OWLXMLDocumentFormat;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.MissingImportHandlingStrategy;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/** Prepare one frozen ontology for Konclude and prove equality by reloading it. */
public final class ConvertSyntax {
    private ConvertSyntax() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 4 || !(args[3].equals("rdfxml") || args[3].equals("owlxml")
                || args[3].equals("functional"))) {
            System.err.println("Usage: ConvertSyntax <source> <output> <receipt-output> "
                    + "<rdfxml|owlxml|functional>");
            System.exit(2);
        }
        String serialization = args[3];
        String converterSha256 = System.getProperty("km.converter.sha256", "");
        if (!converterSha256.matches("[0-9a-f]{64}")) {
            throw new IllegalArgumentException("missing km.converter.sha256 artifact binding");
        }
        Path source = new File(args[0]).toPath().toAbsolutePath();
        Path destination = new File(args[1]).toPath().toAbsolutePath();
        Path receipt = new File(args[2]).toPath().toAbsolutePath();
        if (!Files.isRegularFile(source) || Files.size(source) == 0) {
            throw new IllegalArgumentException("missing source");
        }
        Files.createDirectories(destination.getParent());
        Files.createDirectories(receipt.getParent());
        Path temporary = destination.resolveSibling(destination.getFileName() + ".part");
        Path receiptTemporary = receipt.resolveSibling(receipt.getFileName() + ".part");
        Files.deleteIfExists(temporary);
        Files.deleteIfExists(receiptTemporary);

        OWLOntologyLoaderConfiguration configuration = new OWLOntologyLoaderConfiguration()
                .setMissingImportHandlingStrategy(MissingImportHandlingStrategy.THROW_EXCEPTION);
        OWLOntologyManager sourceManager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = sourceManager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(source.toFile()), configuration);
        if (serialization.equals("functional")) {
            Files.copy(source, temporary, StandardCopyOption.REPLACE_EXISTING);
        } else {
            sourceManager.saveOntology(ontology,
                    serialization.equals("rdfxml")
                            ? new RDFXMLDocumentFormat() : new OWLXMLDocumentFormat(),
                    IRI.create(temporary.toUri()));
        }

        OWLOntologyManager checkManager = OWLManager.createOWLOntologyManager();
        OWLOntology reloaded = checkManager.loadOntologyFromOntologyDocument(
                new org.semanticweb.owlapi.io.FileDocumentSource(temporary.toFile()), configuration);
        int alphaRenamedRules = 0;
        java.util.Set<org.semanticweb.owlapi.model.OWLAxiom> sourceLogical =
                new java.util.HashSet<>(ontology.getLogicalAxioms());
        java.util.Set<org.semanticweb.owlapi.model.OWLAxiom> reloadedLogical =
                new java.util.HashSet<>(reloaded.getLogicalAxioms());
        if (!sourceLogical.equals(reloadedLogical)) {
            java.util.Set<org.semanticweb.owlapi.model.OWLAxiom> missing =
                    new java.util.HashSet<>(sourceLogical);
            missing.removeAll(reloadedLogical);
            java.util.Set<org.semanticweb.owlapi.model.OWLAxiom> added =
                    new java.util.HashSet<>(reloadedLogical);
            added.removeAll(sourceLogical);
            boolean rulesOnly = missing.stream().allMatch(ax -> ax.isOfType(AxiomType.SWRL_RULE))
                    && added.stream().allMatch(ax -> ax.isOfType(AxiomType.SWRL_RULE));
            java.util.Set<String> canonicalMissingRules = new java.util.HashSet<>();
            java.util.Set<String> canonicalAddedRules = new java.util.HashSet<>();
            missing.forEach(ax -> canonicalMissingRules.add(canonicalRuleVariables(ax)));
            added.forEach(ax -> canonicalAddedRules.add(canonicalRuleVariables(ax)));
            if (!rulesOnly || missing.size() != added.size()
                    || ontology.getAxiomCount(AxiomType.SWRL_RULE)
                    != reloaded.getAxiomCount(AxiomType.SWRL_RULE)
                    || !canonicalMissingRules.equals(canonicalAddedRules)) {
                throw new IllegalStateException(serialization + " round trip changed logical axioms: missing="
                        + missing.size() + " added=" + added.size()
                        + " first_missing=" + missing.stream().findFirst().orElse(null)
                        + " first_added=" + added.stream().findFirst().orElse(null));
            }
            // OWLAPI may canonicalise SWRL variable IRIs while serialising RDF/XML.
            // Variables are bound within a rule, so this is alpha-renaming.
            alphaRenamedRules = missing.size();
        }
        if (!ontology.getSignature().equals(reloaded.getSignature())) {
            throw new IllegalStateException("OWL/XML round trip changed the signature");
        }

        try (BufferedWriter out = Files.newBufferedWriter(receiptTemporary, StandardCharsets.UTF_8)) {
            out.write("M\tschema\t1\n");
            out.write("M\tconversion\tkonclude-compatible-serialization-v2\n");
            out.write("M\tconverter_sha256\t" + converterSha256 + "\n");
            out.write("M\tserialization\t" + serialization + "\n");
            out.write("M\tsource\t" + source + "\n");
            out.write("M\tsource_sha256\t" + sha256(source) + "\n");
            out.write("M\toutput_sha256\t" + sha256(temporary) + "\n");
            out.write("M\taxioms\t" + ontology.getAxiomCount() + "\n");
            out.write("M\tlogical_axioms\t" + ontology.getLogicalAxiomCount() + "\n");
            out.write("M\tsignature_entities\t" + ontology.getSignature().size() + "\n");
            out.write("M\troundtrip_logical_axioms_equal\ttrue\n");
            out.write("M\troundtrip_alpha_renamed_rules\t" + alphaRenamedRules + "\n");
            out.write("M\troundtrip_annotation_axiom_delta\t"
                    + (reloaded.getAxiomCount(AxiomType.ANNOTATION_ASSERTION)
                    - ontology.getAxiomCount(AxiomType.ANNOTATION_ASSERTION)) + "\n");
            out.write("M\troundtrip_signature_equal\ttrue\n");
            out.write("Z\tcomplete\n");
        }
        Files.move(temporary, destination, StandardCopyOption.REPLACE_EXISTING);
        Files.move(receiptTemporary, receipt, StandardCopyOption.REPLACE_EXISTING);
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (java.io.InputStream input = Files.newInputStream(path)) {
            byte[] buffer = new byte[8 * 1024 * 1024];
            for (int length; (length = input.read(buffer)) >= 0;) {
                if (length > 0) digest.update(buffer, 0, length);
            }
        }
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest()) result.append(String.format("%02x", value & 0xff));
        return result.toString();
    }

    private static String canonicalRuleVariables(org.semanticweb.owlapi.model.OWLAxiom axiom) {
        // OWLAPI 5.1.9's OWL/XML parser rewrites urn:swrl#X to
        // urn:swrl:var#X. Accept exactly that bound-variable renaming, not an
        // arbitrary same-count replacement of rule axioms.
        return axiom.toString().replace("Variable(<urn:swrl#", "Variable(<urn:swrl:var#");
    }
}
