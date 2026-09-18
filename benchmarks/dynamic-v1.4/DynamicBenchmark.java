package org.kmbenchmark;

import java.nio.file.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import org.semanticweb.owlapi.reasoner.*;

/** Source-level dynamic benchmark. Each invocation runs exactly one arm. */
public final class DynamicBenchmark {
    static long now() { return System.nanoTime(); }
    static double seconds(long start) { return (now() - start) / 1e9; }
    static OWLOntology load(Path path) throws Exception {
        OWLOntology o;
        if (path.toString().endsWith(".gz")) {
            try (java.io.InputStream in = new java.util.zip.GZIPInputStream(Files.newInputStream(path))) {
                o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(in);
            }
        } else o = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(path.toFile());
        if (!o.getImportsDeclarations().isEmpty())
            throw new IllegalArgumentException("Input must have a frozen, flattened imports closure");
        return o;
    }
    static TreeSet<String> taxonomy(OWLReasoner r, OWLOntology o) {
        TreeSet<String> rows = new TreeSet<>();
        boolean consistent = r.isConsistent();
        rows.add("C\t" + consistent);
        if (!consistent) return rows;
        Set<OWLClass> unsat = r.getUnsatisfiableClasses().getEntitiesMinusBottom();
        for (OWLClass c : unsat) rows.add("U\t" + c.getIRI());
        for (OWLClass c : o.getClassesInSignature(Imports.INCLUDED)) {
            if (c.isOWLThing() || c.isOWLNothing() || unsat.contains(c)) continue;
            Set<OWLClass> supers = new HashSet<>(r.getSuperClasses(c, false).getFlattened());
            supers.addAll(r.getEquivalentClasses(c).getEntities());
            for (OWLClass s : supers)
                if (!s.equals(c) && !s.isOWLThing() && !s.isOWLNothing())
                    rows.add("S\t" + c.getIRI() + "\t" + s.getIRI());
        }
        return rows;
    }
    static void classify(OWLReasoner r) {
        if (r.isConsistent()) r.precomputeInferences(InferenceType.CLASS_HIERARCHY);
    }
    static void prepare(String[] a) throws Exception {
        OWLOntology original = load(Paths.get(a[1]));
        Path out = Paths.get(a[2]); Files.createDirectories(out);
        int steps = Integer.parseInt(a[3]), n = Integer.parseInt(a[4]);
        Random rng = new Random(Long.parseLong(a[5]));
        List<OWLAxiom> eligible = new ArrayList<>();
        Set<OWLAxiom> fixed = new HashSet<>();
        // Annotations do not participate; every state shares a fixed vocabulary.
        for (OWLAxiom ax : original.getAxioms()) {
            if (ax instanceof OWLSubClassOfAxiom || ax instanceof OWLEquivalentClassesAxiom
                    || ax instanceof OWLDisjointClassesAxiom) eligible.add(ax.getAxiomWithoutAnnotations());
            else if (ax.isLogicalAxiom() || ax instanceof OWLDeclarationAxiom)
                fixed.add(ax.getAxiomWithoutAnnotations());
        }
        for (OWLEntity e : original.getSignature())
            fixed.add(original.getOWLOntologyManager().getOWLDataFactory().getOWLDeclarationAxiom(e));
        eligible = new ArrayList<>(new HashSet<>(eligible));
        eligible.sort(Comparator.comparing(Object::toString));
        if (eligible.size() < 2*n) throw new IllegalArgumentException("insufficient concept axioms");
        Collections.shuffle(eligible, rng);
        int holdout = Math.max(n, eligible.size()/10);
        List<OWLAxiom> absent = new ArrayList<>(eligible.subList(0, holdout));
        List<OWLAxiom> active = new ArrayList<>(eligible.subList(holdout, eligible.size()));
        List<String> manifest = new ArrayList<>();
        for (int i=0; i<=steps; i++) {
            if (i>0) {
                Collections.shuffle(active, rng); Collections.shuffle(absent, rng);
                List<OWLAxiom> removed = new ArrayList<>(active.subList(0,n));
                List<OWLAxiom> added = new ArrayList<>(absent.subList(0,n));
                active.removeAll(removed); absent.removeAll(added);
                active.addAll(added); absent.addAll(removed);
            }
            OWLOntologyManager m = OWLManager.createOWLOntologyManager();
            Set<OWLAxiom> all = new HashSet<>(fixed); all.addAll(active);
            OWLOntology state = m.createOntology(all);
            boolean compressed = a.length > 6 && a[6].equals("gzip");
            Path p = out.resolve(String.format("state-%03d.ofn",i)+(compressed ? ".gz" : "")).toAbsolutePath();
            if (compressed) {
                try (java.io.OutputStream stream = new java.util.zip.GZIPOutputStream(Files.newOutputStream(p))) {
                    m.saveOntology(state,new FunctionalSyntaxDocumentFormat(),stream);
                }
            } else m.saveOntology(state, new FunctionalSyntaxDocumentFormat(), IRI.create(p.toUri()));
            manifest.add(p.toString());
        }
        Files.write(out.resolve("states.txt"),manifest,StandardCharsets.UTF_8);
    }
    public static void main(String[] a) throws Exception {
        if (a[0].equals("prepare")) { prepare(a); return; }
        // session|fresh factory states.txt output-directory
        boolean session = a[0].equals("session");
        if (!session && !a[0].equals("fresh")) throw new IllegalArgumentException("invalid arm");
        OWLReasonerFactory f = (OWLReasonerFactory)Class.forName(a[1]).getDeclaredConstructor().newInstance();
        Path out = Paths.get(a[3]); Files.createDirectories(out);
        OWLOntology current = null; OWLReasoner reasoner = null;
        List<String> timing = new ArrayList<>();
        timing.add("revision\tparse_s\tupdate_inference_s\textract_s\tadded\tremoved");
        int i=0;
        Files.write(out.resolve("timings.tsv"),timing,StandardCharsets.UTF_8);
        try {
            for (String line : Files.readAllLines(Paths.get(a[2]),StandardCharsets.UTF_8)) {
                final int revision = i;
                Timer deadline = new Timer(true);
                deadline.schedule(new TimerTask() { public void run() {
                    System.err.println("STATE_TIMEOUT revision="+revision); System.exit(124);
                }},240000);
                long t=now(); OWLOntology next = load(Paths.get(line)); double parse=seconds(t);
                Set<OWLAxiom> add = new HashSet<>(next.getAxioms()), remove = new HashSet<>();
                if (current != null) {
                    add.removeAll(current.getAxioms()); remove.addAll(current.getAxioms());
                    remove.removeAll(next.getAxioms());
                }
                t=now();
                if (session && reasoner != null) {
                    for (OWLAxiom ax : remove) current.getOWLOntologyManager().applyChange(new RemoveAxiom(current,ax));
                    for (OWLAxiom ax : add) current.getOWLOntologyManager().applyChange(new AddAxiom(current,ax));
                    reasoner.flush();
                } else {
                    if (reasoner != null) reasoner.dispose();
                    current=next; reasoner=f.createReasoner(current);
                }
                classify(reasoner); double inference=seconds(t);
                t=now(); TreeSet<String> signature = taxonomy(reasoner,current); double extract=seconds(t);
                if ("1".equals(System.getenv("DYNAMIC_DIGEST_ONLY"))) {
                    java.security.MessageDigest hash = java.security.MessageDigest.getInstance("SHA-256");
                    for (String row : signature) hash.update((row+"\n").getBytes(StandardCharsets.UTF_8));
                    StringBuilder hex = new StringBuilder();
                    for (byte b : hash.digest()) hex.append(String.format("%02x",b & 255));
                    Files.write(out.resolve(String.format("%03d.sig.sha256",i)),
                        Arrays.asList(hex.toString()),StandardCharsets.UTF_8);
                } else if ("1".equals(System.getenv("DYNAMIC_COMPACT"))) {
                    try (java.io.Writer writer = new java.io.OutputStreamWriter(new java.util.zip.GZIPOutputStream(
                            Files.newOutputStream(out.resolve(String.format("%03d.sig.gz",i)))),StandardCharsets.UTF_8)) {
                        for (String row : signature) { writer.write(row); writer.write("\n"); }
                    }
                } else Files.write(out.resolve(String.format("%03d.sig",i)),signature,StandardCharsets.UTF_8);
                timing.add(i+"\t"+parse+"\t"+inference+"\t"+extract+"\t"+add.size()+"\t"+remove.size());
                Files.write(out.resolve("timings.tsv"),timing,StandardCharsets.UTF_8);
                deadline.cancel();
                if (current != next) next.getOWLOntologyManager().removeOntology(next);
                i++;
            }
        } finally { if (reasoner != null) reasoner.dispose(); }
        Files.write(out.resolve("timings.tsv"),timing,StandardCharsets.UTF_8);
        Files.write(out.resolve("COMPLETE"),Arrays.asList("states="+i),StandardCharsets.UTF_8);
    }
}
