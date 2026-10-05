package org.kmbenchmark;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;

/** Retain one OWLAPI reasoner across complete, import-free source revisions. */
public final class IncrementalClassifier {
    private IncrementalClassifier() {}
    private static void preserveAnonymousIds(OWLOntologyManager manager) throws Exception {
        try {
            Object configurator = OWLOntologyManager.class.getMethod("getOntologyConfigurator").invoke(manager);
            configurator.getClass().getMethod("withRemapAllAnonymousIndividualsIds", boolean.class)
                .invoke(configurator, false);
        } catch (NoSuchMethodException legacyApi) {
            Class.forName("org.semanticweb.owlapi.io.AnonymousIndividualProperties")
                .getMethod("setRemapAllAnonymousIndividualsIds", boolean.class).invoke(null, false);
        }
    }

    public static void main(String[] args) throws Exception {
        boolean interactive = args.length == 3 && args[2].equals("--stdin");
        if (!interactive && args.length < 4) {
            throw new IllegalArgumentException("factory output-directory initial.ofn updated.ofn [...]");
        }
        OWLReasonerFactory factory = (OWLReasonerFactory) Class.forName(args[0])
            .getDeclaredConstructor().newInstance();
        Path output = Paths.get(args[1]).toAbsolutePath();
        Files.createDirectories(output);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        preserveAnonymousIds(manager);
        OWLOntology ontology = null;
        OWLReasoner reasoner = null;
        java.io.BufferedReader requests = interactive ? new java.io.BufferedReader(
            new java.io.InputStreamReader(System.in, StandardCharsets.UTF_8)) : null;
        try {
            for (int revisionIndex = 0; ; revisionIndex++) {
                String sourcePath = interactive ? requests.readLine()
                    : revisionIndex + 2 < args.length ? args[revisionIndex + 2] : null;
                if (sourcePath == null) break;
                if (sourcePath.isEmpty()) throw new IllegalArgumentException("empty revision path");
                long started = System.nanoTime();
                OWLOntologyManager loader = OWLManager.createOWLOntologyManager();
                preserveAnonymousIds(loader);
                OWLOntology revision = loader.loadOntologyFromOntologyDocument(Paths.get(sourcePath).toFile());
                if (!revision.getImportsDeclarations().isEmpty()) {
                    throw new IllegalArgumentException("benchmark source must have a frozen import closure");
                }
                Set<OWLAxiom> next = new HashSet<>(revision.getAxioms());
                long parsed = System.nanoTime();
                int added, removed;
                if (ontology == null) {
                    ontology = manager.createOntology(next);
                    added = next.size(); removed = 0;
                    reasoner = factory.createReasoner(ontology);
                } else {
                    Set<OWLAxiom> deletes = new HashSet<>(ontology.getAxioms());
                    deletes.removeAll(next);
                    Set<OWLAxiom> adds = new HashSet<>(next);
                    adds.removeAll(ontology.getAxioms());
                    added = adds.size(); removed = deletes.size();
                    manager.removeAxioms(ontology, deletes);
                    manager.addAxioms(ontology, adds);
                    reasoner.flush();
                }
                long applied = System.nanoTime();
                String stem = String.format("%03d", revisionIndex);
                FullIriClassifier.writeSnapshot(reasoner, ontology, factory, output.resolve(stem + ".taxonomy.tsv"));
                long finished = System.nanoTime();
                String receipt = "revision\tparse_ns\tapply_flush_ns\tclassify_publish_ns\tadded\tremoved\tbuffering\n"
                    + revisionIndex + "\t" + (parsed - started) + "\t" + (applied - parsed) + "\t"
                    + (finished - applied) + "\t" + added + "\t" + removed + "\t" + reasoner.getBufferingMode() + "\n";
                Path receiptTemporary = output.resolve(stem + ".timing.tsv.part");
                Files.write(receiptTemporary, receipt.getBytes(StandardCharsets.UTF_8));
                Files.move(receiptTemporary, output.resolve(stem + ".timing.tsv"),
                    java.nio.file.StandardCopyOption.ATOMIC_MOVE);
                loader.removeOntology(revision);
            }
            Files.write(output.resolve("COMPLETE"), "complete\n".getBytes(StandardCharsets.UTF_8));
        } finally {
            if (reasoner != null) reasoner.dispose();
        }
    }
}
