#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --cpus-per-task=1
#SBATCH --mem=20G
#SBATCH --time=00:40:00
#SBATCH --job-name=km-dynamic-pilot
set -euo pipefail
: "${DYNAMIC_ROOT:?}"
cd "$DYNAMIC_ROOT"
mkdir -p classes results inputs
runtime=/ibex/scratch/hohndor/km/paper-benchmark-20260830/runtimes
binary=/ibex/scratch/hohndor/km/v140-release-final-20260916/km.ibex
expected=ddc30d2f9013b371b5c4ec19c0623c91ecc1b2dbdc172ded9002fd238903d09a
test "$(sha256sum "$binary" | cut -d' ' -f1)" = "$expected"
sha256sum "$binary" "$runtime"/classifier-{hermit,jfact,openllet,elk,whelk}.jar *.java *.py > runtime-hashes.txt
javac -cp "$runtime/classifier-hermit.jar" -d classes DynamicBenchmark.java
python3 - <<'PY'
from pathlib import Path
axioms=[]
for i in range(100):
    axioms.extend([f'SubClassOf(:A{i} :B{i})',f'SubClassOf(:B{i} :C{i})',f'SubClassOf(:C{i} :D{i})'])
Path('inputs/chains.ofn').write_text('Prefix(:=<urn:km:dynamic:>)\nOntology(\n'+'\n'.join(axioms)+'\n)\n')
PY
java_opts=(-XX:ActiveProcessorCount=1 -Xmx16g -Delk.reasoner.number_of_workers=1)
java "${java_opts[@]}" -cp "classes:$runtime/classifier-hermit.jar" org.kmbenchmark.DynamicBenchmark prepare inputs/chains.ofn inputs/chains 5 10 20260917
java "${java_opts[@]}" -cp "classes:$runtime/classifier-hermit.jar" org.kmbenchmark.DynamicBenchmark prepare /ibex/scratch/hohndor/km/paper-benchmark-20260830/obo-snapshot/merged/ado.ofn inputs/ado 5 1 20260917
find inputs -name '*.ofn' -print0 | sort -z | xargs -0 sha256sum > input-hashes.txt
names=(hermit jfact openllet elk whelk)
factories=(org.semanticweb.HermiT.ReasonerFactory uk.ac.manchester.cs.jfact.JFactFactory openllet.owlapi.OpenlletReasonerFactory org.semanticweb.elk.owlapi.ElkReasonerFactory org.geneontology.whelk.owlapi.WhelkOWLReasonerFactory)
for case in chains ado; do
  for arm in session fresh; do
    out="results/$case/km/$arm"
    mkdir -p "$out"
    set +e
    /usr/bin/time -v -o "$out/process.time" timeout -k 5 240 python3 km_incremental.py "$binary" "inputs/$case/states.txt" "$out" "$arm" >"$out/stdout.log" 2>"$out/driver.stderr"
    rc=$?
    set -e
    echo "$rc" > "$out/exit-code"
    for i in "${!names[@]}"; do
      out="results/$case/${names[$i]}/$arm"
      mkdir -p "$out"
      set +e
      /usr/bin/time -v -o "$out/process.time" timeout -k 5 240 java "${java_opts[@]}" -cp "classes:$runtime/classifier-${names[$i]}.jar" org.kmbenchmark.DynamicBenchmark "$arm" "${factories[$i]}" "inputs/$case/states.txt" "$out" >"$out/stdout.log" 2>"$out/stderr.log"
      rc=$?
      set -e
      echo "$rc" > "$out/exit-code"
    done
  done
done
python3 audit_pilot.py results > audit.json
{
  echo "job=$SLURM_JOB_ID"
  hostname
  lscpu
} > host.txt
echo PILOT_COMPLETE
