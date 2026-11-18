#!/usr/bin/env bash
# Run the randomized HermiT/KM differential test on N random ontologies (default 2000)
# outside mvn test, using 2 worker threads (at most 2 concurrent reasoner runs)
# and reporting total checks, adjudicated HermiT differences, KM mismatches, and
# hit counts for all 25 plugin reductions.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${KM_BIN:=/mnt/data1/leechuck/km-work/v170/scratch/bin/km-f2eb0196}"
: "${PARITY_TMP:=/mnt/data1/leechuck/km-work/v170/scratch/w13/tmp}"
: "${MVN:=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/tools/apache-maven-3.9.9/bin/mvn}"
COUNT="${1:-2000}"
OUT_JSON="${2:-/mnt/data1/leechuck/km-work/v170/scratch/w13/random2000.json}"

case "$PARITY_TMP" in /tmp|/tmp/*) echo "PARITY_TMP must not be under /tmp" >&2; exit 2;; esac
mkdir -p "$PARITY_TMP"
export TMPDIR="$PARITY_TMP" KM_THREADS=1

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  (cd "$here/../protege" && "$MVN" -o -q -Djava.io.tmpdir="$PARITY_TMP" test-compile)
  (cd "$here" && "$MVN" -o -q -Djava.io.tmpdir="$PARITY_TMP" compile dependency:build-classpath -Dmdep.outputFile=target/classpath.txt)
fi

CP="$here/../protege/target/protege5/test-classes:$here/../protege/target/protege5/classes:$here/target/classes:$(cat "$here/target/classpath.txt")"

cat > "$PARITY_TMP/RunRandomBatch.java" << 'EOF'
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import org.bioontology.kobayashimarust.protege.KMReasoner;
import org.bioontology.kobayashimarust.protege.RandomDifferentialTest;
import org.bioontology.kobayashimarust.protege.RandomOntologyGenerator;

import java.io.FileWriter;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

public class RunRandomBatch {
    public static void main(String[] args) throws Exception {
        int count = Integer.parseInt(args[0]);
        String outPath = args[1];
        long seed = RandomDifferentialTest.SEED;
        KMReasoner.resetReductionHits();
        long t0 = System.currentTimeMillis();

        int threads = 2;
        ExecutorService pool = Executors.newFixedThreadPool(threads);
        AtomicInteger nextIdx = new AtomicInteger(0);
        List<Future<RandomDifferentialTest.ComparisonSummary>> futures = new ArrayList<>();
        for (int t = 0; t < threads; t++) {
            futures.add(pool.submit(() -> {
                RandomDifferentialTest.ComparisonSummary local = new RandomDifferentialTest.ComparisonSummary();
                while (true) {
                    int idx = nextIdx.getAndIncrement();
                    if (idx >= count) break;
                    RandomOntologyGenerator.GeneratedOntology gen = RandomOntologyGenerator.generate(seed, idx);
                    RandomDifferentialTest.compareOne(gen, local);
                    local.ontologiesRun++;
                }
                return local;
            }));
        }
        RandomDifferentialTest.ComparisonSummary merged = new RandomDifferentialTest.ComparisonSummary();
        for (Future<RandomDifferentialTest.ComparisonSummary> f : futures) {
            RandomDifferentialTest.ComparisonSummary s = f.get();
            merged.ontologiesRun += s.ontologiesRun;
            merged.totalChecks += s.totalChecks;
            merged.hermitDirectTypesAdjudicated += s.hermitDirectTypesAdjudicated;
            merged.hermitDirectInstancesAdjudicated += s.hermitDirectInstancesAdjudicated;
            merged.hermitDataValuesAdjudicated += s.hermitDataValuesAdjudicated;
            merged.hermitBottomPropertyAdjudicated += s.hermitBottomPropertyAdjudicated;
            merged.kmMismatches.addAll(s.kmMismatches);
        }
        pool.shutdown();
        merged.reductionHits = KMReasoner.getReductionHits();
        long elapsedMs = System.currentTimeMillis() - t0;

        Map<String, Object> report = new LinkedHashMap<>();
        report.put("seed", seed);
        report.put("ontologiesRun", merged.ontologiesRun);
        report.put("elapsedSeconds", elapsedMs / 1000.0);
        report.put("totalChecks", merged.totalChecks);
        report.put("hermitDirectTypesAdjudicated", merged.hermitDirectTypesAdjudicated);
        report.put("hermitDirectInstancesAdjudicated", merged.hermitDirectInstancesAdjudicated);
        report.put("hermitDataValuesAdjudicated", merged.hermitDataValuesAdjudicated);
        report.put("kmMismatchesCount", merged.kmMismatches.size());
        report.put("kmMismatches", merged.kmMismatches);
        report.put("reductionHits", merged.reductionHits);

        Gson gson = new GsonBuilder().setPrettyPrinting().disableHtmlEscaping().create();
        try (FileWriter fw = new FileWriter(outPath)) {
            gson.toJson(report, fw);
        }
        System.out.println(gson.toJson(report));
        if (!merged.kmMismatches.isEmpty()) {
            System.exit(1);
        }
        for (Map.Entry<String, Long> e : merged.reductionHits.entrySet()) {
            if (e.getValue() <= 0L) {
                System.err.println("Unreached reduction: " + e.getKey());
                System.exit(2);
            }
        }
    }
}
EOF

javac -cp "$CP" -d "$PARITY_TMP" "$PARITY_TMP/RunRandomBatch.java"
java -Xmx4g -Djava.io.tmpdir="$PARITY_TMP" -Dkm.bin="$KM_BIN" -cp "$PARITY_TMP:$CP" RunRandomBatch "$COUNT" "$OUT_JSON"
