package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.nio.file.Path;
import java.nio.charset.StandardCharsets;
import java.io.ByteArrayOutputStream;

/** Shared imports-closure and functional-syntax boundary for native KM calls. */
final class FlattenedOntology {

    private FlattenedOntology() {
    }

    static void save(OWLOntology ontology, Path destination) throws Exception {
        OWLOntology flattened = snapshot(ontology);
        OWLOntologyManager manager = flattened.getOWLOntologyManager();
        manager.saveOntology(
                flattened,
                new FunctionalSyntaxDocumentFormat(),
                IRI.create(destination.toUri()));
    }

    static String functionalSyntax(OWLOntology ontology) throws Exception {
        OWLOntology flattened = snapshot(ontology);
        return functionalSyntaxOfSnapshot(flattened);
    }

    static String functionalSyntaxOfSnapshot(OWLOntology flattened) throws Exception {
        OWLOntologyManager manager = flattened.getOWLOntologyManager();
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        manager.saveOntology(flattened, new FunctionalSyntaxDocumentFormat(), output);
        return new String(output.toByteArray(), StandardCharsets.UTF_8);
    }

    static OWLOntology snapshot(OWLOntology ontology) throws Exception {
        validateImports(ontology);
        return OWLManager.createOWLOntologyManager()
                .createOntology(ontology.getAxioms(Imports.INCLUDED));
    }

    private static void validateImports(OWLOntology ontology) {
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
