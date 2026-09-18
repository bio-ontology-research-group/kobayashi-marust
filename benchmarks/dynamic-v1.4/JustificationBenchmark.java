package org.kmbenchmark;

import java.nio.file.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.io.*;
import com.fasterxml.jackson.databind.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.reasoner.*;

/** Common black-box deletion + hitting-set enumeration, independently verifiable. */
public final class JustificationBenchmark {
    static OWLReasonerFactory factory;
    static String kmBinary;
    static Path scratch;
    static OWLAxiom query;
    static Set<OWLAxiom> declarations;
    static int checks;
    static boolean entails(Set<OWLAxiom> axioms) throws Exception {
        checks++;
        OWLOntologyManager m=OWLManager.createOWLOntologyManager();
        Set<OWLAxiom> all=new HashSet<>(axioms); all.addAll(declarations);
        OWLOntology o=create(m,all);
        if(kmBinary!=null) {
            Path file=Files.createTempFile(scratch,"oracle-",".ofn");
            Path error=Files.createTempFile(scratch,"oracle-",".stderr");
            Process process=null;
            try {
                m.saveOntology(o,new FunctionalSyntaxDocumentFormat(),IRI.create(file.toUri()));
                ProcessBuilder builder=new ProcessBuilder(kmBinary,"incremental-source");
                builder.environment().keySet().removeIf(k->k.startsWith("KM_"));
                builder.environment().put("KM_THREADS","1");
                builder.environment().put("KM_CENTRAL_TIME_CAP","240");
                process=builder.redirectError(error.toFile()).start();
                ObjectMapper mapper=new ObjectMapper();
                Map<String,String> request=new HashMap<>();
                request.put("op","init");request.put("functional_syntax",Files.readString(file));
                try(Writer writer=new OutputStreamWriter(process.getOutputStream(),StandardCharsets.UTF_8)) {
                    writer.write(mapper.writeValueAsString(request)+"\n");
                }
                // Jackson closes an InputStream after parsing its first JSON value.
                // Drain to EOF first so the worker can finish writing before
                // we inspect its exit status (including the trailing newline).
                JsonNode response=mapper.readTree(process.getInputStream().readAllBytes());
                if(process.waitFor()!=0 || !response.path("status").asText().equals("ok"))
                    throw new IllegalStateException("KM oracle failed: "+response+" "+Files.readString(error));
                JsonNode result=response.path("result");
                if(result.path("dropped").size()!=0 || result.path("dropped").asInt(0)!=0)throw new IllegalStateException("KM dropped axioms");
                if(!result.path("consistent").asBoolean())return true;
                OWLSubClassOfAxiom q=(OWLSubClassOfAxiom)query;
                String sub=q.getSubClass().asOWLClass().getIRI().toString();
                String sup=q.getSuperClass().asOWLClass().getIRI().toString();
                if(sub.equals(sup)||q.getSubClass().isOWLNothing()||q.getSuperClass().isOWLThing())return true;
                for(JsonNode c:result.path("unsatisfiable"))if(c.asText().equals(sub))return true;
                JsonNode pairs=result.path("subsumptions");
                if(pairs.isObject()) {for(JsonNode c:pairs.path(sub))if(c.asText().equals(sup))return true;}
                else for(JsonNode pair:pairs)if(pair.get(0).asText().equals(sub)&&pair.get(1).asText().equals(sup))return true;
                return false;
            } finally {
                if(process!=null && process.isAlive())process.destroyForcibly().waitFor();
                Files.deleteIfExists(file);Files.deleteIfExists(error);
            }
        }
        OWLReasoner r=factory.createReasoner(o);
        try {
            if(!r.isConsistent())return true;
            try {return r.isEntailed(query);}
            catch(UnsupportedOperationException unsupported) {
                // Whelk exposes classification but not isEntailed. For a named
                // subclass query the full taxonomy is an exact entailment oracle.
                OWLSubClassOfAxiom q=(OWLSubClassOfAxiom)query;
                OWLClass sub=q.getSubClass().asOWLClass(),sup=q.getSuperClass().asOWLClass();
                if(sub.equals(sup)||sub.isOWLNothing()||sup.isOWLThing())return true;
                if(r.getUnsatisfiableClasses().contains(sub))return true;
                return r.getEquivalentClasses(sub).contains(sup)||r.getSuperClasses(sub,false).containsEntity(sup);
            }
        }
        finally { r.dispose(); }
    }
    // applyChange has the same ABI in the pinned OWLAPI 4 and 5 runtimes.
    static OWLOntology create(OWLOntologyManager m, Set<OWLAxiom> axioms) throws Exception {
        OWLOntology o=m.createOntology();
        for (OWLAxiom ax : axioms) m.applyChange(new AddAxiom(o,ax));
        return o;
    }
    static Set<OWLAxiom> logical(OWLOntology o) {
        Set<OWLAxiom> result=new HashSet<>();
        o.getLogicalAxioms().forEach(ax->result.add(ax.getAxiomWithoutAnnotations()));
        return result;
    }
    static boolean verify(Set<OWLAxiom> support) throws Exception {
        if (!entails(support)) return false;
        for (OWLAxiom ax : support) {
            Set<OWLAxiom> smaller=new HashSet<>(support); smaller.remove(ax);
            if (entails(smaller)) return false;
        }
        return true;
    }
    public static void main(String[] a) throws Exception {
        // extract|verify factory input sub super output limit|support-directory
        if(a[1].startsWith("km:"))kmBinary=a[1].substring(3);
        else factory=(OWLReasonerFactory)Class.forName(a[1]).getDeclaredConstructor().newInstance();
        OWLOntology o=DynamicBenchmark.load(Paths.get(a[2]));
        OWLDataFactory d=OWLManager.getOWLDataFactory();
        query=d.getOWLSubClassOfAxiom(d.getOWLClass(IRI.create(a[3])),d.getOWLClass(IRI.create(a[4])));
        declarations=new HashSet<>();
        o.getSignature().forEach(e->declarations.add(d.getOWLDeclarationAxiom(e)));
        query.getSignature().forEach(e->declarations.add(d.getOWLDeclarationAxiom(e)));
        Set<OWLAxiom> source=logical(o);
        Path out=Paths.get(a[5]); Files.createDirectories(out);
        scratch=out.resolve("oracle-tmp");Files.createDirectories(scratch);
        if (a[0].equals("verify")) {
            List<String> rows=new ArrayList<>(); rows.add("support\tsource_subset\tminimal_entailed");
            try (java.util.stream.Stream<Path> paths=Files.list(Paths.get(a[6]))) {
                for (Path path : (Iterable<Path>)paths.filter(p->p.getFileName().toString().startsWith("support-") && p.toString().endsWith(".ofn")).sorted()::iterator) {
                    Set<OWLAxiom> support=logical(DynamicBenchmark.load(path));
                    boolean subset=source.containsAll(support), valid=verify(support);
                    rows.add(path.getFileName()+"\t"+subset+"\t"+valid);
                }
            }
            Files.write(out.resolve("verification.tsv"),rows,StandardCharsets.UTF_8);
            Files.write(out.resolve("source-entailed.txt"),Arrays.asList(Boolean.toString(entails(source))),StandardCharsets.UTF_8);
            return;
        }
        if (!a[0].equals("extract")) throw new IllegalArgumentException("invalid operation");
        int limit=Integer.parseInt(a[6]);
        if (limit<1) throw new IllegalArgumentException("positive limit required");
        long start=System.nanoTime(); double first=-1;
        boolean positive=entails(source);
        double entailment=(System.nanoTime()-start)/1e9;
        List<Set<OWLAxiom>> supports=new ArrayList<>();
        ArrayDeque<Set<OWLAxiom>> queue=new ArrayDeque<>();
        Set<Set<OWLAxiom>> seen=new HashSet<>();
        if (positive) { queue.add(new HashSet<>()); seen.add(new HashSet<>()); }
        while (!queue.isEmpty() && supports.size()<limit) {
            Set<OWLAxiom> blocked=queue.remove();
            Set<OWLAxiom> candidate=new HashSet<>(source); candidate.removeAll(blocked);
            if (!entails(candidate)) continue;
            List<OWLAxiom> order=new ArrayList<>(candidate);
            order.sort(Comparator.comparing(Object::toString));
            for (OWLAxiom ax : order) {
                candidate.remove(ax);
                if (!entails(candidate)) candidate.add(ax);
            }
            if (!supports.contains(candidate)) {
                supports.add(new HashSet<>(candidate));
                if (first<0) first=(System.nanoTime()-start)/1e9;
            }
            // Every alternative support must omit an axiom of this support.
            List<OWLAxiom> branch=new ArrayList<>(candidate);
            branch.sort(Comparator.comparing(Object::toString));
            for (OWLAxiom ax : branch) {
                Set<OWLAxiom> child=new HashSet<>(blocked); child.add(ax);
                if (seen.add(child)) queue.add(child);
            }
        }
        double total=(System.nanoTime()-start)/1e9;
        for (int i=0;i<supports.size();i++) {
            OWLOntologyManager m=OWLManager.createOWLOntologyManager();
            Set<OWLAxiom> all=new HashSet<>(supports.get(i)); all.addAll(declarations);
            m.saveOntology(create(m,all),new FunctionalSyntaxDocumentFormat(),
                IRI.create(out.resolve(String.format("support-%03d.ofn",i)).toAbsolutePath().toUri()));
        }
        Files.write(out.resolve("metrics.tsv"),Arrays.asList(
            "entailed\t"+positive,"supports\t"+supports.size(),"enumeration_complete\t"+queue.isEmpty(),
            "entailment_s\t"+entailment,"first_s\t"+first,"total_s\t"+total,"oracle_checks\t"+checks),StandardCharsets.UTF_8);
        Files.write(out.resolve("COMPLETE"),Arrays.asList("complete"),StandardCharsets.UTF_8);
    }
}
