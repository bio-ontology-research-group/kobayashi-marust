package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.functional.renderer.FunctionalSyntaxObjectRenderer;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.util.DefaultPrefixManager;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.charset.StandardCharsets;
import java.io.StringWriter;
import java.io.Writer;

/** Shared imports-closure and functional-syntax boundary for native KM calls. */
final class FlattenedOntology {

    private FlattenedOntology() {
    }

    static void save(OWLOntology ontology, Path destination) throws Exception {
        OWLOntology flattened = snapshot(ontology);
        try (Writer output = Files.newBufferedWriter(destination, StandardCharsets.UTF_8)) {
            render(flattened, output);
        }
    }

    static String functionalSyntax(OWLOntology ontology) throws Exception {
        OWLOntology flattened = snapshot(ontology);
        return functionalSyntaxOfSnapshot(flattened);
    }

    static String functionalSyntaxOfSnapshot(OWLOntology flattened) throws Exception {
        StringWriter output = new StringWriter();
        render(flattened, output);
        return output.toString();
    }

    private static void render(OWLOntology flattened, Writer output) {
        FunctionalSyntaxObjectRenderer renderer = new FunctionalSyntaxObjectRenderer(
                flattened, new FunctionalSyntaxDocumentFormat(), output);
        DefaultPrefixManager prefixes = new DefaultPrefixManager();
        prefixes.clear();
        // The native answer preserves source spellings. Full IRIs keep the
        // Java result contract independent of the ontology's namespace.
        renderer.setPrefixManager(prefixes);
        flattened.accept(renderer);
    }

    static OWLOntology snapshot(OWLOntology ontology) throws Exception {
        validateImports(ontology);
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        // A generated ID on every copy changes the serialized source header,
        // preventing exact and locality reuse across otherwise related edits.
        OWLOntology snapshot = manager.createOntology(ontology.getOntologyID());
        manager.addAxioms(snapshot, ontology.getAxioms(Imports.INCLUDED));
        return snapshot;
    }

    static void validateImports(OWLOntology ontology) {
        OWLOntologyManager sourceManager = ontology.getOWLOntologyManager();
        for (OWLOntology member : ontology.getImportsClosure()) {
            for (OWLImportsDeclaration declaration : member.getImportsDeclarations()) {
                if (sourceManager.getImportedOntology(declaration) == null) {
                    throw new IllegalStateException(
                            "Protégé has not loaded ontology import " + declaration.getIRI());
                }
            }
        }
    }
}
