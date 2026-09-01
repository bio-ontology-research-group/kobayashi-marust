package org.kmbenchmark;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Set;
import java.util.TreeSet;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.semanticweb.more.reasoner.MOReReasoner;

/** OWLAPI 3 adapter implementing the common paper-benchmark wire contract. */
public final class FullIriClassifier3 {
    private FullIriClassifier3() {}

    public static void main(String[] args) throws Exception {
        if (args.length != 3) {
            System.err.println("Usage: FullIriClassifier3 <factory-class> <ontology> <output>");
            System.exit(2);
        }
        String factoryClass = args[0];
        File input = new File(args[1]).getAbsoluteFile();
        File output = new File(args[2]).getAbsoluteFile();
        if (!input.isFile() || input.length() == 0) throw new IllegalArgumentException("missing ontology");
        output.getParentFile().mkdirs();
        File temporary = new File(output.getPath() + ".part");
        temporary.delete();

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(input);
        OWLReasonerFactory factory = (OWLReasonerFactory) Class.forName(factoryClass).newInstance();
        OWLReasoner reasoner = factory.createReasoner(ontology);
        if (!(reasoner instanceof MOReReasoner)) throw new IllegalArgumentException("factory did not create MORe");
        MOReReasoner more = (MOReReasoner) reasoner;
        Set<String> unsatisfiable = new TreeSet<String>();
        Set<String> pairs = new TreeSet<String>();
        String consistency = "unknown";
        try {
            more.classifyClasses();
            for (OWLClass cls : more.getAllUnsatisfiableClasses()) {
                if (!cls.isOWLNothing()) unsatisfiable.add(cls.getIRI().toString());
            }
            for (OWLClass sub : ontology.getClassesInSignature(true)) {
                String subIri = sub.getIRI().toString();
                if (sub.isOWLThing() || sub.isOWLNothing() || unsatisfiable.contains(subIri)) continue;
                for (OWLClass sup : more.getAllSuperClasses(sub)) add(pairs, subIri, sup);
            }
        } finally {
            reasoner.dispose();
        }
        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(temporary), StandardCharsets.UTF_8), 1 << 16);
        try {
            writer.write("M\tschema\t1\nM\tfactory\t" + clean(factoryClass) + "\n");
            String name = factory.getReasonerName();
            writer.write("M\treasoner\t" + clean(name == null ? factoryClass : name) + "\n");
            writer.write("C\t" + consistency + "\n");
            for (String iri : unsatisfiable) writer.write("U\t" + clean(iri) + "\n");
            for (String pair : pairs) writer.write("S\t" + pair + "\n");
            writer.write("M\tclasses\t" + ontology.getClassesInSignature(true).size() + "\n");
            writer.write("M\tunsatisfiable\t" + unsatisfiable.size() + "\n");
            writer.write("M\tsubsumptions\t" + pairs.size() + "\nZ\tcomplete\n");
        } finally {
            writer.close();
        }
        Path source = temporary.toPath();
        Path destination = output.toPath();
        Files.move(source, destination, StandardCopyOption.REPLACE_EXISTING);
    }

    private static void add(Set<String> pairs, String sub, OWLClass sup) {
        if (!sup.isOWLThing() && !sup.isOWLNothing()) {
            String value = sup.getIRI().toString();
            if (!sub.equals(value)) pairs.add(clean(sub) + "\t" + clean(value));
        }
    }

    private static String clean(String value) {
        if (value.indexOf('\t') >= 0 || value.indexOf('\n') >= 0 || value.indexOf('\r') >= 0) {
            throw new IllegalArgumentException("record field contains a control separator");
        }
        return value;
    }
}
