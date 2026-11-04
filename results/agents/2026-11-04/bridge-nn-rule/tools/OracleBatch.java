import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.nio.file.Files;

/**
 * Batch driver for the HermiT validation oracle (Oracle.java of
 * .work/agent-scratch/r3-unannounced/oracle): one JVM, many seeds.
 * usage: java -cp ORACLE_DIR:BUILD_DIR:CP OracleBatch GOLD_DIR FILE...
 * Writes GOLD_DIR/<stem>.json for every FILE whose answer is not cached.
 */
public class OracleBatch {
    public static void main(String[] args) throws Exception {
        File gold = new File(args[0]);
        PrintStream out = System.out;
        for (int i = 1; i < args.length; i++) {
            File f = new File(args[i]);
            String stem = f.getName().replaceAll("\\.ofn$", "");
            File dst = new File(gold, stem + ".json");
            if (dst.exists() && dst.length() > 0) continue;
            ByteArrayOutputStream buf = new ByteArrayOutputStream();
            System.setOut(new PrintStream(buf, true, "UTF-8"));
            try {
                Oracle.main(new String[]{f.getAbsolutePath()});
                System.out.flush();
                File tmp = new File(gold, stem + ".tmp");
                Files.write(tmp.toPath(), buf.toByteArray());
                tmp.renameTo(dst);
            } catch (Throwable e) {
                System.err.println("oracle failed on " + f + ": " + e);
            } finally {
                System.setOut(out);
            }
        }
    }
}
