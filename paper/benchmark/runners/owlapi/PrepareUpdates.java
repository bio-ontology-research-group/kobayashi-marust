package org.kmbenchmark;

import java.nio.charset.StandardCharsets;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/** Freeze a common deletion/restoration stream without consulting any reasoner. */
public final class PrepareUpdates {
    private PrepareUpdates() {}
    private static String hash(byte[] value) {
        try {
            byte[] digest = MessageDigest.getInstance("SHA-256").digest(value);
            StringBuilder s = new StringBuilder();for (byte b : digest) s.append(String.format("%02x", b & 255));
            return s.toString();
        } catch (Exception e) { throw new IllegalStateException(e); }
    }
    private static String hashFile(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        try (InputStream input = Files.newInputStream(path)) {
            byte[] block = new byte[1048576];int n;
            while ((n = input.read(block)) != -1) digest.update(block, 0, n);
        }
        StringBuilder s = new StringBuilder();
        for (byte b : digest.digest()) s.append(String.format("%02x", b & 255));
        return s.toString();
    }
    private static String rank(OWLAxiom axiom) {
        return hash(("km-v145-updates-v1\n" + axiom.toString()).getBytes(StandardCharsets.UTF_8));
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 2) throw new IllegalArgumentException("source.ofn output-directory");
        Path input = Paths.get(args[0]);Path output = Paths.get(args[1]);
        Files.createDirectories(output);
        if (Files.exists(output.resolve("COMPLETE"))) throw new IllegalArgumentException("already prepared");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology source = manager.loadOntologyFromOntologyDocument(input.toFile());
        if (!source.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        List<OWLAxiom> logical = new ArrayList<>(source.getLogicalAxioms());
        Map<OWLAxiom, String> ranks = new HashMap<>();
        for (OWLAxiom axiom : logical) ranks.put(axiom, rank(axiom));
        logical.sort(Comparator.comparing((OWLAxiom a) -> ranks.get(a)).thenComparing(Object::toString));
        int batch = Math.min(32, Math.max(1, (logical.size() + 99) / 100));
        int[] removals = {0, Math.min(1, logical.size()), 0, Math.min(batch, logical.size()), 0};
        StringBuilder receipt = new StringBuilder("revision\tlogical_axioms\tremoved_from_original\tsha256\n");
        String sourceHash = hashFile(input);
        IRI revisionIri = IRI.create("urn:km:v145:updates:" + sourceHash);
        Set<OWLAxiom> original = new HashSet<>(source.getAxioms());
        for (int i = 0; i < removals.length; i++) {
            Set<OWLAxiom> axioms = new HashSet<>(original);
            for (int j = 0; j < removals[i]; j++) axioms.remove(logical.get(j));
            OWLOntology revision = manager.createOntology(axioms, revisionIri);
            for (org.semanticweb.owlapi.model.OWLAnnotation annotation : source.getAnnotations())
                manager.applyChange(new org.semanticweb.owlapi.model.AddOntologyAnnotation(revision, annotation));
            Path path = output.resolve(String.format("%03d.ofn", i));
            try (java.io.BufferedWriter writer = Files.newBufferedWriter(path, StandardCharsets.UTF_8)) {
                FunctionalSyntaxObjectRenderer renderer = new FunctionalSyntaxObjectRenderer(revision, writer);
                renderer.setAddMissingDeclarations(false);
                revision.accept(renderer);
            }
            receipt.append(i).append('\t').append(revision.getLogicalAxiomCount()).append('\t')
                .append(removals[i]).append('\t').append(hashFile(path)).append('\n');
            manager.removeOntology(revision);
        }
        Files.write(output.resolve("revisions.tsv"), receipt.toString().getBytes(StandardCharsets.UTF_8));
        StringBuilder selection = new StringBuilder("rank\tsha256\taxiom\n");
        for (int i=0; i<Math.min(batch, logical.size()); i++) {
            OWLAxiom axiom=logical.get(i);String text=axiom.toString();
            if (text.indexOf('\t')>=0 || text.indexOf('\n')>=0 || text.indexOf('\r')>=0)
                throw new IllegalArgumentException("unescaped axiom rendering separator");
            selection.append(i).append('\t').append(rank(axiom)).append('\t').append(text).append('\n');
        }
        Files.write(output.resolve("selected-axioms.tsv"),selection.toString().getBytes(StandardCharsets.UTF_8));
        Files.write(output.resolve("source.sha256"),(sourceHash+"\n").getBytes(StandardCharsets.UTF_8));
        VerifyUpdates.main(new String[]{args[0], args[1], output.resolve("verification.tsv").toString()});
        Files.write(output.resolve("COMPLETE"),"complete\n".getBytes(StandardCharsets.UTF_8));
    }
}
