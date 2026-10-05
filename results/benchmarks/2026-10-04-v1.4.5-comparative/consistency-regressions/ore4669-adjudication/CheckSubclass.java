import java.io.File;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.*;
public class CheckSubclass {
 public static void main(String[] args) throws Exception {
  OWLOntologyManager m=OWLManager.createOWLOntologyManager();
  OWLOntology source=m.loadOntologyFromOntologyDocument(new File(args[0]));
  OWLOntology module=m.loadOntologyFromOntologyDocument(new File(args[1]));
  if(!source.getImportsDeclarations().isEmpty() || !module.getImportsDeclarations().isEmpty()) throw new IllegalStateException("imports");
  if(!source.getLogicalAxioms().containsAll(module.getLogicalAxioms())) throw new IllegalStateException("not source subset");
  OWLReasonerFactory f=(OWLReasonerFactory)Class.forName("org.semanticweb.HermiT.ReasonerFactory").getDeclaredConstructor().newInstance();
  OWLReasoner r=f.createReasoner(module);
  try {
   boolean consistent=r.isConsistent();
   OWLDataFactory d=m.getOWLDataFactory();
   boolean entailed=r.isEntailed(d.getOWLSubClassOfAxiom(d.getOWLClass(IRI.create(args[2])),d.getOWLClass(IRI.create(args[3]))));
   System.out.println("source_subset=true consistent="+consistent+" entailed="+entailed);
  } finally { r.dispose(); }
 }
}
