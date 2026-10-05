package org.kmbenchmark;

import java.io.BufferedReader;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

/** Freeze three hash-ranked inferred subclass queries and shared STAR modules. */
public final class PrepareQueries {
    private PrepareQueries() {}
    private static String hex(byte[] bytes) {
        StringBuilder s = new StringBuilder();
        for (byte b : bytes) s.append(String.format("%02x", b & 255));
        return s.toString();
    }
    private static String hashFile(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream in = Files.newInputStream(path)) {
            byte[] block = new byte[1048576]; int n;
            while ((n = in.read(block)) != -1) digest.update(block, 0, n);
        }
        return hex(digest.digest());
    }
    private static String rank(String sourceHash, String sub, String sup) throws Exception {
        return hex(MessageDigest.getInstance("SHA-256").digest(
            ("km-v145-queries-v1\n" + sourceHash + "\n" + sub + "\n" + sup)
                .getBytes(StandardCharsets.UTF_8)));
    }
    private static boolean builtin(String iri) {
        return iri.equals("http://www.w3.org/2002/07/owl#Thing")
            || iri.equals("http://www.w3.org/2002/07/owl#Nothing");
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 3) throw new IllegalArgumentException("source taxonomy.tsv output-directory");
        long start = System.nanoTime();
        Path sourcePath = Paths.get(args[0]), taxonomy = Paths.get(args[1]), output = Paths.get(args[2]);
        Files.createDirectories(output);
        if (Files.exists(output.resolve("COMPLETE"))) throw new IllegalArgumentException("already prepared");
        String sourceHash = hashFile(sourcePath), taxonomyHash = hashFile(taxonomy);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology source = manager.loadOntologyFromOntologyDocument(sourcePath.toFile());
        if (!source.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        Set<String> unsat = new HashSet<>(); boolean consistent = false, complete = false;
        String last = null;
        try (BufferedReader reader = Files.newBufferedReader(taxonomy)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.equals("C\ttrue")) consistent = true;
                if (line.startsWith("U\t")) unsat.add(line.substring(2));
                last = line;
            }
        }
        complete = "Z\tcomplete".equals(last);
        if (!complete || !consistent) throw new IllegalArgumentException("reference must be complete and consistent");
        List<String[]> selected = new ArrayList<>(); long candidates = 0;
        Set<String> signature = new HashSet<>();
        source.getClassesInSignature().forEach(c -> signature.add(c.getIRI().toString()));
        try (BufferedReader reader = Files.newBufferedReader(taxonomy)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (!line.startsWith("S\t")) continue;
                String[] pair = line.split("\t", -1);
                if (pair.length != 3) throw new IllegalArgumentException("malformed taxonomy pair");
                String sub = pair[1], sup = pair[2];
                if (sub.equals(sup) || builtin(sub) || builtin(sup) || unsat.contains(sub)) continue;
                if (!signature.contains(sub) || !signature.contains(sup))
                    throw new IllegalArgumentException("reference class outside source signature");
                OWLClass a = manager.getOWLDataFactory().getOWLClass(IRI.create(sub));
                OWLClass b = manager.getOWLDataFactory().getOWLClass(IRI.create(sup));
                if (source.containsAxiomIgnoreAnnotations(manager.getOWLDataFactory().getOWLSubClassOfAxiom(a, b))) continue;
                String key = rank(sourceHash, sub, sup);
                if (selected.stream().anyMatch(r -> r[0].equals(key) && r[1].equals(sub) && r[2].equals(sup))) continue;
                candidates++;
                selected.add(new String[]{key, sub, sup});
                selected.sort(Comparator.comparing((String[] r) -> r[0]).thenComparing(r -> r[1]).thenComparing(r -> r[2]));
                if (selected.size() > 3) selected.remove(3);
            }
        }
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, source, ModuleType.STAR);
        StringBuilder table = new StringBuilder("query\trank_sha256\tsub_iri\tsuper_iri\tmodule_sha256\tlogical_axioms\n");
        int index = 0;
        for (String[] row : selected) {
            String name = String.format("%03d", index++);
            Set<org.semanticweb.owlapi.model.OWLEntity> terms = new HashSet<>(Arrays.asList(
                manager.getOWLDataFactory().getOWLClass(IRI.create(row[1])),
                manager.getOWLDataFactory().getOWLClass(IRI.create(row[2]))));
            OWLOntology module = extractor.extractAsOntology(terms, IRI.create("urn:km:v145:query:" + row[0]));
            for (OWLAxiom axiom : module.getLogicalAxioms())
                if (!source.containsAxiom(axiom)) throw new IllegalStateException("module logical axiom outside source");
            Path target = output.resolve(name + ".ofn");
            manager.saveOntology(module, new FunctionalSyntaxDocumentFormat(), IRI.create(target.toUri()));
            OWLOntologyManager reloadManager = OWLManager.createOWLOntologyManager();
            reloadManager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
            OWLOntology reloaded = reloadManager.loadOntologyFromOntologyDocument(target.toFile());
            if (!reloaded.getLogicalAxioms().equals(module.getLogicalAxioms()))
                throw new IllegalStateException("module serialization changed logical axioms");
            reloadManager.removeOntology(reloaded);
            table.append(name).append('\t').append(row[0]).append('\t').append(row[1]).append('\t')
                 .append(row[2]).append('\t').append(hashFile(target)).append('\t')
                 .append(module.getLogicalAxiomCount()).append('\n');
            manager.removeOntology(module);
        }
        Files.write(output.resolve("queries.tsv"), table.toString().getBytes(StandardCharsets.UTF_8));
        String receipt = "source_sha256\t" + sourceHash + "\nreference_taxonomy_sha256\t" + taxonomyHash
            + "\nsource_logical_axioms\t" + source.getLogicalAxiomCount() + "\ncandidate_queries\t" + candidates
            + "\nselected_queries\t" + selected.size() + "\npreparation_ns\t" + (System.nanoTime() - start) + "\n";
        Files.write(output.resolve("receipt.tsv"), receipt.getBytes(StandardCharsets.UTF_8));
        Files.write(output.resolve("COMPLETE"), "complete\n".getBytes(StandardCharsets.UTF_8));
    }
}
