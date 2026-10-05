package org.kmbenchmark;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/** Source signature and prefix bindings for full-IRI output validation. */
public final class SourceSignature {
    private static String field(String value) {
        if (value.contains("\t") || value.contains("\n") || value.contains("\r"))
            throw new IllegalArgumentException("control separator in IRI or prefix");
        return value;
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 2) throw new IllegalArgumentException("source output.tsv");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology source = manager.loadOntologyFromOntologyDocument(Paths.get(args[0]).toFile());
        if (!source.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        Path output = Paths.get(args[1]);
        java.security.MessageDigest digest = java.security.MessageDigest.getInstance("SHA-256");
        try (java.io.InputStream input = Files.newInputStream(Paths.get(args[0]))) {
            byte[] buffer = new byte[1048576]; int count;
            while ((count = input.read(buffer)) != -1) digest.update(buffer, 0, count);
        }
        StringBuilder sourceHash = new StringBuilder();
        for (byte b : digest.digest()) sourceHash.append(String.format("%02x", b & 255));
        try (java.io.BufferedWriter writer = Files.newBufferedWriter(output, StandardCharsets.UTF_8)) {
            writer.write("M\tschema\t1\n");
            writer.write("M\tsource_sha256\t" + sourceHash + "\n");
            org.semanticweb.owlapi.model.OWLDocumentFormat format = manager.getOntologyFormat(source);
            if (format.isPrefixOWLDocumentFormat()) {
                Map<String, String> prefixes = new TreeMap<>(format.asPrefixOWLDocumentFormat().getPrefixName2PrefixMap());
                for (Map.Entry<String, String> entry : prefixes.entrySet())
                    writer.write("P\t" + field(entry.getKey()) + "\t" + field(entry.getValue()) + "\n");
            }
            TreeSet<String> classes = new TreeSet<>();
            source.getClassesInSignature().forEach(c -> classes.add(c.getIRI().toString()));
            for (String iri : classes) writer.write("C\t" + field(iri) + "\n");
            writer.write("Z\tcomplete\n");
        }
    }
}
