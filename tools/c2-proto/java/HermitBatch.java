import java.io.File;
import java.util.concurrent.*;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

/** Consistency of many small ontologies in one JVM: prints "path<TAB>true|false|error|timeout". */
public class HermitBatch {
    public static void main(String[] args) throws Exception {
        ExecutorService ex = Executors.newSingleThreadExecutor(r -> { Thread t = new Thread(r); t.setDaemon(true); return t; });
        for (String p : args) {
            Future<String> f = ex.submit(() -> {
                OWLOntologyManager m = OWLManager.createOWLOntologyManager();
                OWLOntology o = m.loadOntologyFromOntologyDocument(new File(p));
                Reasoner r = new Reasoner(new org.semanticweb.HermiT.Configuration(), o);
                boolean c = r.isConsistent();
                r.dispose();
                return Boolean.toString(c);
            });
            String res;
            try { res = f.get(60, TimeUnit.SECONDS); }
            catch (TimeoutException e) { f.cancel(true); res = "timeout";
                ex.shutdownNow(); ex = Executors.newSingleThreadExecutor(r -> { Thread t = new Thread(r); t.setDaemon(true); return t; }); }
            catch (ExecutionException e) { res = "error:" + e.getCause(); }
            System.out.println(p + "\t" + res);
            System.out.flush();
        }
        System.exit(0);
    }
}
