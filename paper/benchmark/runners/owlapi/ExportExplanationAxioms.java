package org.kmbenchmark;

import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer;
import org.semanticweb.owlapi.io.StringDocumentSource;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

/** Export exact logical axiom units for an external classification deletion oracle. */
public final class ExportExplanationAxioms {
    private static String render(OWLOntology source, OWLAxiom axiom) {
        StringWriter writer = new StringWriter();
        FunctionalSyntaxObjectRenderer renderer = new FunctionalSyntaxObjectRenderer(source, writer);
        DefaultPrefixManager prefixes = new DefaultPrefixManager(); prefixes.clear();
        renderer.setPrefixManager(prefixes);
        renderer.setAddMissingDeclarations(false);
        axiom.accept(renderer);
        return writer.toString();
    }
    public static void main(String[] args) throws Exception {
        if (args.length != 2) throw new IllegalArgumentException("module.ofn output-directory");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        manager.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology source = manager.loadOntologyFromOntologyDocument(Paths.get(args[0]).toFile());
        if (!source.getImportsDeclarations().isEmpty()) throw new IllegalArgumentException("unfrozen imports");
        Path output = Paths.get(args[1]); Files.createDirectories(output);
        List<OWLAxiom> logical = new ArrayList<>(source.getLogicalAxioms());
        logical.sort(Comparator.comparing(Object::toString));
        List<OWLAxiom> declarations = new ArrayList<>();
        for (OWLAxiom a : source.getAxioms()) if (a.isOfType(AxiomType.DECLARATION)) declarations.add(a);
        declarations.sort(Comparator.comparing(Object::toString));
        StringBuilder background = new StringBuilder(), all = new StringBuilder("Ontology(\n");
        for (OWLAxiom a : declarations) background.append(render(source,a)).append('\n');
        all.append(background);
        StringBuilder manifest = new StringBuilder("M\tschema\t1\n");
        for (int i=0; i<logical.size(); i++) {
            String rendered = render(source,logical.get(i)); all.append(rendered).append('\n');
            manifest.append("A\t").append(i).append('\t').append(Base64.getEncoder().encodeToString(rendered.getBytes(StandardCharsets.UTF_8))).append('\n');
        }
        all.append(")\n");
        OWLOntologyManager reload = OWLManager.createOWLOntologyManager();
        reload.getOntologyConfigurator().withRemapAllAnonymousIndividualsIds(false);
        OWLOntology checked = reload.loadOntologyFromOntologyDocument(new StringDocumentSource(all.toString()));
        Set<OWLAxiom> expected = new HashSet<>(logical); expected.addAll(declarations);
        if (!checked.getAxioms().equals(expected)) throw new IllegalStateException("export changed source axioms");
        Files.write(output.resolve("background.ofn-fragment"),background.toString().getBytes(StandardCharsets.UTF_8));
        manifest.append("Z\tcomplete\n");
        Files.write(output.resolve("axioms.tsv"),manifest.toString().getBytes(StandardCharsets.UTF_8));
        Files.write(output.resolve("roundtrip.ofn"),all.toString().getBytes(StandardCharsets.UTF_8));
        Files.write(output.resolve("COMPLETE"),"source axiom roundtrip passed\n".getBytes(StandardCharsets.UTF_8));
    }
}
