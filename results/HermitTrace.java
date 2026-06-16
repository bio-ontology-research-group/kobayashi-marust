import java.io.File;
import java.lang.reflect.Method;
import java.util.*;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.HermiT.monitor.CountingMonitor;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

/**
 * Trace HermiT classification effort per ontology using CountingMonitor.
 * Prints, reflectively (robust to API drift), every numeric getter on the
 * monitor after classifyClasses(), plus the most expensive individual tests.
 * Goal: distinguish "few real SAT tests" (pseudo-model pruning) from
 * "many tests, cheap each" (blocking/backjumping efficiency).
 */
public class HermitTrace {
    public static void main(String[] args) throws Exception {
        for (String path : args) {
            try {
                traceOne(path);
            } catch (Throwable t) {
                System.out.println("ONT " + path + " ERROR " + t);
                t.printStackTrace();
            }
            System.out.println();
        }
    }

    static void traceOne(String path) throws Exception {
        OWLOntologyManager m = OWLManager.createOWLOntologyManager();
        long l0 = System.currentTimeMillis();
        OWLOntology o = m.loadOntologyFromOntologyDocument(new File(path));
        long l1 = System.currentTimeMillis();
        Configuration c = new Configuration();
        CountingMonitor mon = new CountingMonitor();
        c.monitor = mon;
        Reasoner r = new Reasoner(c, o);
        long c0 = System.currentTimeMillis();
        r.classifyClasses();
        long c1 = System.currentTimeMillis();

        int nClasses = o.getClassesInSignature(org.semanticweb.owlapi.model.parameters.Imports.INCLUDED).size();
        System.out.println("ONT " + path);
        System.out.println("  classes=" + nClasses + "  load_ms=" + (l1 - l0) + "  classify_ms=" + (c1 - c0));

        // Dump all no-arg numeric getters on the monitor.
        TreeMap<String, Object> stats = new TreeMap<String, Object>();
        Object recordsList = null;
        for (Method me : mon.getClass().getMethods()) {
            if (me.getParameterTypes().length != 0) continue;
            String n = me.getName();
            if (!n.startsWith("get") && !n.startsWith("num") && !n.startsWith("count")) continue;
            Class<?> rt = me.getReturnType();
            try {
                Object v = me.invoke(mon);
                if (rt == int.class || rt == long.class || rt == double.class
                        || Number.class.isAssignableFrom(rt)) {
                    stats.put(n, v);
                } else if (v instanceof List) {
                    recordsList = v;
                }
            } catch (Throwable ignore) {}
        }
        for (Map.Entry<String, Object> e : stats.entrySet())
            System.out.println("  " + e.getKey() + " = " + e.getValue());

        // Dump the most expensive individual tests (by any numeric getter we can find).
        if (recordsList instanceof List) {
            List<?> recs = (List<?>) recordsList;
            System.out.println("  num_test_records = " + recs.size());
            // For each record, find a "backtracking"-like numeric getter to rank by.
            List<Object[]> ranked = new ArrayList<Object[]>();
            for (Object rec : recs) {
                long bt = numGetter(rec, "acktrack");
                long cl = numGetter(rec, "lash");
                long nd = numGetter(rec, "ode");
                long ms = numGetter(rec, "ime");
                String desc = strGetter(rec);
                ranked.add(new Object[]{bt, cl, nd, ms, desc});
            }
            ranked.sort(new Comparator<Object[]>() {
                public int compare(Object[] a, Object[] b) {
                    return Long.compare((Long) b[0], (Long) a[0]);
                }
            });
            long totBt = 0;
            for (Object[] x : ranked) totBt += (Long) x[0];
            System.out.println("  total_backtrack_over_records = " + totBt);
            int top = Math.min(8, ranked.size());
            System.out.println("  top " + top + " tests by backtracking (bt,clash,nodes,ms,desc):");
            for (int i = 0; i < top; i++) {
                Object[] x = ranked.get(i);
                System.out.println("    bt=" + x[0] + " clash=" + x[1] + " nodes=" + x[2]
                        + " ms=" + x[3] + " " + x[4]);
            }
        }
    }

    static long numGetter(Object rec, String contains) {
        for (Method me : rec.getClass().getMethods()) {
            if (me.getParameterTypes().length != 0) continue;
            String n = me.getName();
            if (!n.startsWith("get")) continue;
            if (!n.toLowerCase().contains(contains.toLowerCase())) continue;
            Class<?> rt = me.getReturnType();
            if (rt == int.class || rt == long.class || rt == double.class
                    || Number.class.isAssignableFrom(rt)) {
                try {
                    Object v = me.invoke(rec);
                    if (v instanceof Number) return ((Number) v).longValue();
                } catch (Throwable ignore) {}
            }
        }
        return 0;
    }

    static String strGetter(Object rec) {
        for (Method me : rec.getClass().getMethods()) {
            if (me.getParameterTypes().length != 0) continue;
            if (me.getReturnType() != String.class) continue;
            if (!me.getName().startsWith("get")) continue;
            try {
                Object v = me.invoke(rec);
                if (v != null) return me.getName() + "=" + v;
            } catch (Throwable ignore) {}
        }
        return "";
    }
}
