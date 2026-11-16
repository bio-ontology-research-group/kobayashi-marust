// HermiT cross-check for producer/km disagreements (stage H3).
// java -cp <protege-parity classpath> HermitCheck.java ONTOLOGY sat C | sub A B | type a C ...
import java.io.File;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

public class HermitCheck {
    public static void main(String[] a) throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        OWLOntology o = m.loadOntologyFromOntologyDocument(new File(a[0]));
        OWLDataFactory f = m.getOWLDataFactory();
        Configuration c = new Configuration();
        c.ignoreUnsupportedDatatypes = true;
        Reasoner r = new Reasoner(c, o);
        System.out.println("consistent " + r.isConsistent());
        for (int i = 1; i < a.length; ) {
            String k = a[i];
            if (k.equals("sat")) {
                OWLClass x = f.getOWLClass(IRI.create(a[i + 1]));
                System.out.println("sat " + a[i + 1] + " " + r.isSatisfiable(x));
                i += 2;
            } else if (k.equals("sub")) {
                OWLClass x = f.getOWLClass(IRI.create(a[i + 1]));
                OWLClass y = f.getOWLClass(IRI.create(a[i + 2]));
                System.out.println("sub " + a[i + 1] + " " + a[i + 2] + " " + r.isEntailed(f.getOWLSubClassOfAxiom(x, y)));
                i += 3;
            } else if (k.equals("type")) {
                OWLNamedIndividual x = f.getOWLNamedIndividual(IRI.create(a[i + 1]));
                OWLClass y = f.getOWLClass(IRI.create(a[i + 2]));
                System.out.println("type " + a[i + 1] + " " + a[i + 2] + " " + r.isEntailed(f.getOWLClassAssertionAxiom(y, x)));
                i += 3;
            } else {
                throw new IllegalArgumentException(k);
            }
        }
        r.dispose();
    }
}
