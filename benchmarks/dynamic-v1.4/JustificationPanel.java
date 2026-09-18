package org.kmbenchmark;

import java.nio.file.*;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.reasoner.*;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

/** Freeze candidate queries independently of KM, then shared STAR modules. */
public final class JustificationPanel {
    static String hash(String s) throws Exception {
        byte[] bytes=MessageDigest.getInstance("SHA-256").digest(s.getBytes(StandardCharsets.UTF_8));
        StringBuilder b=new StringBuilder(); for(byte x:bytes)b.append(String.format("%02x",x));
        return b.toString();
    }
    public static void main(String[] a) throws Exception {
        OWLOntology o=DynamicBenchmark.load(Paths.get(a[2]));
        Path out=Paths.get(a[3]); Files.createDirectories(out);
        OWLDataFactory d=OWLManager.getOWLDataFactory();
        if (a[0].equals("sample") || a[0].equals("validate")) {
            OWLReasonerFactory f=(OWLReasonerFactory)Class.forName(a[1]).getDeclaredConstructor().newInstance();
            OWLReasoner r=f.createReasoner(o);
            try {
                DynamicBenchmark.classify(r);
                if(!r.isConsistent())throw new IllegalArgumentException("inconsistent source; use separate inconsistency control");
                if(a[0].equals("sample")) {
                    TreeMap<String,OWLClass> classes=new TreeMap<>();
                    for(OWLClass c:o.getClassesInSignature())if(!c.isOWLThing()&&!c.isOWLNothing())classes.put(hash(c.getIRI().toString()),c);
                    Set<OWLClass> unsat=r.getUnsatisfiableClasses().getEntitiesMinusBottom();
                    List<String> candidates=new ArrayList<>();int sampled=0;
                    for(OWLClass c:classes.values()) {
                        if(sampled++>=128)break;
                        if(unsat.contains(c))continue;
                        Set<OWLClass> supers=new HashSet<>(r.getSuperClasses(c,false).getFlattened());
                        supers.addAll(r.getEquivalentClasses(c).getEntities());
                        for(OWLClass sup:supers) {
                            if(sup.equals(c)||sup.isOWLThing()||sup.isOWLNothing())continue;
                            OWLAxiom ax=d.getOWLSubClassOfAxiom(c,sup);
                            if(o.containsAxiomIgnoreAnnotations(ax))continue;
                            String pair=c.getIRI()+"\t"+sup.getIRI();
                            candidates.add(hash("S\t"+pair)+"\t"+pair);
                        }
                    }
                    Collections.sort(candidates);
                    Files.write(out.resolve("candidates.tsv"),candidates,StandardCharsets.UTF_8);
                    Files.write(out.resolve("queries.tsv"),candidates.subList(0,Math.min(5,candidates.size())),StandardCharsets.UTF_8);
                } else {
                    List<String> checks=new ArrayList<>();
                    for(String line:Files.readAllLines(Paths.get(a[4]),StandardCharsets.UTF_8)) {
                        String[] v=line.split("\t");
                        OWLAxiom ax=d.getOWLSubClassOfAxiom(d.getOWLClass(IRI.create(v[1])),d.getOWLClass(IRI.create(v[2])));
                        if(!r.isEntailed(ax))throw new IllegalStateException("independent query disagreement: "+line);
                        checks.add(line+"\ttrue");
                    }
                    Files.write(out.resolve("confirmed.tsv"),checks,StandardCharsets.UTF_8);
                }
                Files.write(out.resolve("consistent.txt"),Arrays.asList("true"),StandardCharsets.UTF_8);
            } finally {r.dispose();}
        } else if (a[0].equals("candidates")) {
            OWLReasonerFactory f=(OWLReasonerFactory)Class.forName(a[1]).getDeclaredConstructor().newInstance();
            OWLReasoner r=f.createReasoner(o);
            try {
                DynamicBenchmark.classify(r);
                TreeSet<String> taxonomy=DynamicBenchmark.taxonomy(r,o);
                Files.write(out.resolve("taxonomy.tsv"),taxonomy,StandardCharsets.UTF_8);
                List<String> candidates=new ArrayList<>();
                for(String line:taxonomy) {
                    if(!line.startsWith("S\t"))continue;
                    String[] v=line.split("\t");
                    OWLAxiom ax=d.getOWLSubClassOfAxiom(d.getOWLClass(IRI.create(v[1])),d.getOWLClass(IRI.create(v[2])));
                    if(o.containsAxiomIgnoreAnnotations(ax))continue;
                    candidates.add(hash(line)+"\t"+v[1]+"\t"+v[2]);
                }
                Collections.sort(candidates);
                Files.write(out.resolve("candidates.tsv"),candidates,StandardCharsets.UTF_8);
            } finally {r.dispose();}
        } else if(a[0].equals("modules")) {
            int index=0;
            for(String line:Files.readAllLines(Paths.get(a[1]),StandardCharsets.UTF_8)) {
                String[] v=line.split("\t");
                Set<OWLEntity> sig=new HashSet<>();
                sig.add(d.getOWLClass(IRI.create(v[1])));sig.add(d.getOWLClass(IRI.create(v[2])));
                long start=System.nanoTime();
                SyntacticLocalityModuleExtractor extractor=new SyntacticLocalityModuleExtractor(o.getOWLOntologyManager(),o,ModuleType.STAR);
                Set<OWLAxiom> module=extractor.extract(sig);
                Set<OWLAxiom> normalized=new HashSet<>();
                for(OWLAxiom ax:module) if(ax.isLogicalAxiom())normalized.add(ax.getAxiomWithoutAnnotations());
                for(OWLEntity e:sig)normalized.add(d.getOWLDeclarationAxiom(e));
                OWLOntologyManager m=OWLManager.createOWLOntologyManager();
                OWLOntology result=JustificationBenchmark.create(m,normalized);
                String id=String.format("q%03d",index++);
                m.saveOntology(result,new FunctionalSyntaxDocumentFormat(),IRI.create(out.resolve(id+".ofn").toAbsolutePath().toUri()));
                double seconds=(System.nanoTime()-start)/1e9;
                Files.write(out.resolve(id+".tsv"),Arrays.asList("query_hash\t"+v[0],"sub\t"+v[1],"super\t"+v[2],"module_logical_axioms\t"+result.getLogicalAxiomCount(),"extraction_and_save_s\t"+seconds),StandardCharsets.UTF_8);
            }
        } else throw new IllegalArgumentException("unknown mode");
        Files.write(out.resolve("COMPLETE"),Arrays.asList("complete"),StandardCharsets.UTF_8);
    }
}
