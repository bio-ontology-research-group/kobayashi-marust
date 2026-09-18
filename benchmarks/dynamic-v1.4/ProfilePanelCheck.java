package org.kmbenchmark;
import java.nio.file.*;
import java.util.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.profiles.OWL2DLProfile;
/** Independent syntactic eligibility audit, without invoking any reasoner. */
public final class ProfilePanelCheck {
 public static void main(String[] args) throws Exception {
  Set<String> seen=new HashSet<>();
  System.out.println("id\trule_axioms\towl2dl\tviolations\timports\tdata_properties");
  for(String line:Files.readAllLines(Paths.get(args[0])).subList(1,Files.readAllLines(Paths.get(args[0])).size())) {
   String[] row=line.split("\t");String id=row[2];if(!seen.add(id))continue;
   OWLOntologyManager manager=OWLManager.createOWLOntologyManager();
   OWLOntology ontology=manager.loadOntologyFromOntologyDocument(Paths.get(row[6]).toFile());
   org.semanticweb.owlapi.profiles.OWLProfileReport report=new OWL2DLProfile().checkOntology(ontology);
   System.out.println(id+"\t"+ontology.getAxiomCount(AxiomType.SWRL_RULE)+"\t"+report.isInProfile()+"\t"+report.getViolations().size()+"\t"+ontology.getImportsDeclarations().size()+"\t"+ontology.getDataPropertiesInSignature().size());
   System.out.flush();manager.removeOntology(ontology);
  }
 }
}
