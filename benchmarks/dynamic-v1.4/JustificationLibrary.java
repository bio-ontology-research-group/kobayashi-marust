package org.kmbenchmark;

import java.nio.file.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.reasoner.*;
import com.clarkparsia.owlapi.explanation.DefaultExplanationGenerator;
import com.clarkparsia.owlapi.explanation.util.ExplanationProgressMonitor;

/** Pinned OWLAPI black-box/HST library, separate from the common extractor. */
public final class JustificationLibrary {
    public static void main(String[] a) throws Exception {
        OWLReasonerFactory factory=(OWLReasonerFactory)Class.forName(a[0]).getDeclaredConstructor().newInstance();
        OWLOntology original=DynamicBenchmark.load(Paths.get(a[1]));
        OWLOntologyManager m=OWLManager.createOWLOntologyManager();
        Set<OWLAxiom> normalized=JustificationBenchmark.logical(original);
        OWLDataFactory d=m.getOWLDataFactory();
        original.getSignature().forEach(e->normalized.add(d.getOWLDeclarationAxiom(e)));
        OWLOntology o=JustificationBenchmark.create(m,normalized);
        OWLAxiom query=d.getOWLSubClassOfAxiom(d.getOWLClass(IRI.create(a[2])),d.getOWLClass(IRI.create(a[3])));
        Path out=Paths.get(a[4]);Files.createDirectories(out);int limit=Integer.parseInt(a[5]);
        long start=System.nanoTime();double[] first={-1};
        OWLReasoner r=factory.createReasoner(o);
        boolean positive=!r.isConsistent()||r.isEntailed(query);
        double entailment=(System.nanoTime()-start)/1e9;
        ExplanationProgressMonitor monitor=new ExplanationProgressMonitor() {
            public void foundExplanation(Set<OWLAxiom> support) {if(first[0]<0)first[0]=(System.nanoTime()-start)/1e9;}
        };
        Set<Set<OWLAxiom>> supports=new HashSet<>();
        try {
            if(positive) {
                DefaultExplanationGenerator generator=new DefaultExplanationGenerator(m,factory,o,r,monitor);
                supports=generator.getExplanations(query,limit);
            }
        } finally {r.dispose();}
        double total=(System.nanoTime()-start)/1e9;
        int i=0;
        for(Set<OWLAxiom> support:supports) {
            OWLOntologyManager output=OWLManager.createOWLOntologyManager();
            output.saveOntology(JustificationBenchmark.create(output,support),new FunctionalSyntaxDocumentFormat(),IRI.create(out.resolve(String.format("support-%03d.ofn",i++)).toAbsolutePath().toUri()));
        }
        // API does not expose a search frontier; never infer completion from a bound.
        Files.write(out.resolve("metrics.tsv"),Arrays.asList("entailed\t"+positive,"supports\t"+supports.size(),"enumeration_complete\tunknown","entailment_s\t"+entailment,"first_s\t"+first[0],"total_s\t"+total,"oracle_checks\tunknown"),StandardCharsets.UTF_8);
        Files.write(out.resolve("COMPLETE"),Arrays.asList("complete"),StandardCharsets.UTF_8);
    }
}
