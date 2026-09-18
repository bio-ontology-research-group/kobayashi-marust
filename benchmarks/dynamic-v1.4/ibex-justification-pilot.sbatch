#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:40:00
#SBATCH --job-name=km-justification-pilot
set -euo pipefail
export LD_LIBRARY_PATH=/home/hohndor/bench/compat:${LD_LIBRARY_PATH:-}
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
binary=/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex
test "$(sha256sum "$binary" | cut -d' ' -f1)" = ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a
mkdir -p justification-classes justification-inputs justification-results
javac -cp "$runtime/classifier-hermit.jar" -d justification-classes DynamicBenchmark.java JustificationBenchmark.java
python3 - <<'PY'
from pathlib import Path
base=['SubClassOf(:A :B)','SubClassOf(:B :D)','SubClassOf(:A :C)','SubClassOf(:C :D)']
for case,axioms in [('two-paths',base),('noise',base+[f'SubClassOf(:Noise{i} :Noise{i+1})' for i in range(30)]),('negative',['SubClassOf(:A :B)','Declaration(Class(:D))'])]:
    Path(f'justification-inputs/{case}.ofn').write_text('Prefix(:=<urn:km:just:>)\nOntology(\n'+'\n'.join(axioms)+'\n)\n')
PY
names=(hermit jfact openllet elk whelk km konclude)
factories=(org.semanticweb.HermiT.ReasonerFactory uk.ac.manchester.cs.jfact.JFactFactory openllet.owlapi.OpenlletReasonerFactory org.semanticweb.elk.owlapi.ElkReasonerFactory org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory "km:$binary" "km:/ibex/scratch/hohndor/km/dynamic-benchmark-20260917/konclude_oracle.py")
opts=(-XX:ActiveProcessorCount=1 -Xmx16g -Delk.reasoner.number_of_workers=1)
for case in two-paths noise negative; do
  input="justification-inputs/$case.ofn"
  for limit in 1 10; do
    out="justification-results/$case/$limit/km-native"
    mkdir -p "$out"
    set +e
    /usr/bin/time -v -o "$out/process.time" timeout -k 5 600 env KM_THREADS=1 "$binary" explain --max-axioms 100 --max-checks 10000 --max-justifications "$limit" "$input" subclass urn:km:just:A urn:km:just:D > "$out/report.json" 2> "$out/stderr.log"
    rc=$?
    set -e
    echo "$rc" > "$out/exit-code"
    if [ "$rc" -eq 0 ]; then
      python3 - "$out" <<'PY'
import json,sys
from pathlib import Path
p=Path(sys.argv[1]); r=json.loads((p/'report.json').read_text())
for i,j in enumerate(r.get('justifications',[])):
    (p/f'support-{i:03}.ofn').write_text('\n'.join(r['prefixDeclarations'])+'\nOntology(\n'+'\n'.join(a['functionalSyntax'] for a in j['axioms'])+'\n)\n')
(p/'COMPLETE').write_text('complete\n')
PY
    fi
    for i in "${!names[@]}"; do
      out="justification-results/$case/$limit/${names[$i]}-common"
      mkdir -p "$out"
      jar=${names[$i]}; if [[ "$jar" = km || "$jar" = konclude ]]; then jar=hermit; fi
      set +e
      /usr/bin/time -v -o "$out/process.time" timeout -k 5 600 java "${opts[@]}" -cp "justification-classes:$runtime/classifier-$jar.jar" org.kmbenchmark.JustificationBenchmark extract "${factories[$i]}" "$input" urn:km:just:A urn:km:just:D "$out" "$limit" > "$out/stdout.log" 2> "$out/stderr.log"
      rc=$?
      set -e
      echo "$rc" > "$out/exit-code"
    done
    for out in justification-results/"$case"/"$limit"/*; do
      if [ -f "$out/COMPLETE" ]; then
        # HermiT validates other engines, JFact validates HermiT.
        validator=hermit; factory=org.semanticweb.HermiT.ReasonerFactory
        if [[ $out == *hermit-common ]]; then validator=jfact; factory=uk.ac.manchester.cs.jfact.JFactFactory; fi
        timeout -k 5 600 java "${opts[@]}" -cp "justification-classes:$runtime/classifier-$validator.jar" org.kmbenchmark.JustificationBenchmark verify "$factory" "$input" urn:km:just:A urn:km:just:D "$out/independent-$validator" "$out"
      fi
    done
  done
done
sha256sum "$binary" *.java justification-inputs/*.ofn "$runtime"/classifier-{hermit,jfact,openllet,elk,whelk}.jar > justification-hashes.txt
printf 'job=%s\n' "$SLURM_JOB_ID" > justification-host.txt
lscpu >> justification-host.txt
echo JUSTIFICATION_PILOT_COMPLETE
