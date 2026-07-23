package org.bioontology.kobayashimarust.protege;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLImportsDeclaration;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;

import java.nio.file.Path;

/** Shared imports-closure and functional-syntax boundary for native KM calls. */
final class FlattenedOntology {

    private FlattenedOntology() {
    }

    static void save(OWLOntology ontology, Path destination) throws Exception {
        OWLOntologyManager sourceManager = ontology.getOWLOntologyManager();
        for (OWLOntology member : ontology.getImportsClosure()) {
            for (OWLImportsDeclaration declaration : member.getImportsDeclarations()) {
                if (sourceManager.getImportedOntology(declaration) == null) {
                    throw new IllegalStateException(
                            "Protégé has not loaded ontology import " + declaration.getIRI());
                }
            }
        }

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology flattened = manager.createOntology(ontology.getAxioms(Imports.INCLUDED));
        manager.saveOntology(
                flattened,
                new FunctionalSyntaxDocumentFormat(),
                IRI.create(destination.toUri()));
    }
}
