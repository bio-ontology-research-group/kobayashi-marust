import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;
import org.semanticweb.owlapi.formats.FunctionalSyntaxDocumentFormat;
import java.io.File;
public class Entail {
  public static void main(String[] a) throws Exception {
    OWLOntologyManager m = OWLManager.createOWLOntologyManager();
    OWLOntology o = m.loadOntologyFromOntologyDocument(new File(a[0]));
    OWLDataFactory f = m.getOWLDataFactory();
    System.out.println("axioms " + o.getLogicalAxiomCount());
    if (a.length > 2 && a[2].equals("--ofn")) { m.saveOntology(o, new FunctionalSyntaxDocumentFormat(), IRI.create(new File(a[3]))); System.out.println("saved " + a[3]); return; }
    OWLReasoner r = new org.semanticweb.HermiT.ReasonerFactory().createReasoner(o);
    System.out.println("consistent " + r.isConsistent());
    String p = a[1];
    for (int i = 2; i + 1 < a.length; i += 2) {
      OWLClass x = f.getOWLClass(IRI.create(p + a[i])), y = f.getOWLClass(IRI.create(p + a[i+1]));
      long t = System.nanoTime();
      boolean e = r.isEntailed(f.getOWLSubClassOfAxiom(x, y));
      System.out.println(a[i] + " <= " + a[i+1] + " : " + e + " (" + (System.nanoTime()-t)/1e9 + " s)");
      System.out.flush();
    }
  }
}
