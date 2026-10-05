package org.kmbenchmark;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/** Reload prepared files and compare them with independently reconstructed views. */
public final class VerifyUpdates {
    private static String rank(OWLAxiom axiom) throws Exception {
        byte[] digest = MessageDigest.getInstance("SHA-256").digest(
            ("km-v145-updates-v1\n" + axiom.toString()).getBytes(StandardCharsets.UTF_8));
        StringBuilder value = new StringBuilder();
        for (byte b : digest) value.append(String.format("%02x", b & 255));
        return value.toString();
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 3) throw new IllegalArgumentException("source revisions-directory receipt.tsv");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology source = manager.loadOntologyFromOntologyDocument(Paths.get(args[0]).toFile());
        if (!source.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        List<OWLAxiom> ranked = new ArrayList<>(source.getLogicalAxioms());
        Map<OWLAxiom, String> ranks = new HashMap<>();
        for (OWLAxiom axiom : ranked) ranks.put(axiom, rank(axiom));
        ranked.sort(Comparator.comparing((OWLAxiom a) -> ranks.get(a)).thenComparing(Object::toString));
        int batch = Math.min(ranked.size(), Math.min(32, (ranked.size() + 99) / 100));
        int[] removed = {0, Math.min(1, ranked.size()), 0, batch, 0};
        StringBuilder result = new StringBuilder("revision\tmissing_axioms\textra_axioms\tontology_annotations_equal\n");
        boolean passed = true;
        for (int i = 0; i < 5; i++) {
            Set<OWLAxiom> expected = new HashSet<>(source.getAxioms());
            for (int j = 0; j < removed[i]; j++) expected.remove(ranked.get(j));
            OWLOntologyManager loader = OWLManager.createOWLOntologyManager();
            loader.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
            Path path = Paths.get(args[1], String.format("%03d.ofn", i));
            OWLOntology actual = loader.loadOntologyFromOntologyDocument(path.toFile());
            Set<OWLAxiom> missing = new HashSet<>(expected); missing.removeAll(actual.getAxioms());
            Set<OWLAxiom> extra = new HashSet<>(actual.getAxioms()); extra.removeAll(expected);
            boolean annotationsEqual = source.getAnnotations().equals(actual.getAnnotations());
            passed &= missing.isEmpty() && extra.isEmpty() && annotationsEqual;
            result.append(i).append('\t').append(missing.size()).append('\t').append(extra.size())
                  .append('\t').append(annotationsEqual).append('\n');
            if (!missing.isEmpty()) result.append("missing_example\t").append(missing.iterator().next()).append('\n');
            if (!extra.isEmpty()) result.append("extra_example\t").append(extra.iterator().next()).append('\n');
            loader.removeOntology(actual);
        }
        result.append("source_ontology_annotations\t").append(source.getAnnotations().size()).append('\n');
        result.append("status\t").append(passed ? "passed" : "failed").append('\n');
        Files.write(Paths.get(args[2]), result.toString().getBytes(StandardCharsets.UTF_8));
        if (!passed) throw new IllegalStateException("prepared updates differ from intended source views");
    }
}
