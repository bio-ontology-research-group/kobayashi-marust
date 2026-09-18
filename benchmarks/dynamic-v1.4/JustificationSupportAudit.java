package org.kmbenchmark;

import java.nio.file.*;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.*;
import org.semanticweb.owlapi.model.*;

/** Post-run normalization: OWL axiom set semantics, ignoring source occurrences. */
public final class JustificationSupportAudit {
    public static void main(String[] args) throws Exception {
        Path root=Paths.get(args[0]);List<String> rows=new ArrayList<>();
        rows.add("support\tnormalized_logical_axioms\tsha256");
        try(java.util.stream.Stream<Path> paths=Files.walk(root)) {
            for(Path file:(Iterable<Path>)paths.filter(p->p.getFileName().toString().matches("support-[0-9]+\\.ofn")).sorted()::iterator) {
                OWLOntology o=DynamicBenchmark.load(file);
                TreeSet<String> axioms=new TreeSet<>();
                for(OWLAxiom ax:JustificationBenchmark.logical(o))axioms.add(ax.toString());
                byte[] digest=MessageDigest.getInstance("SHA-256").digest((String.join("\n",axioms)+"\n").getBytes(StandardCharsets.UTF_8));
                StringBuilder hash=new StringBuilder();for(byte b:digest)hash.append(String.format("%02x",b));
                rows.add(root.relativize(file)+"\t"+axioms.size()+"\t"+hash);
                o.getOWLOntologyManager().removeOntology(o);
            }
        }
        Files.write(Paths.get(args[1]),rows,StandardCharsets.UTF_8);
    }
}
