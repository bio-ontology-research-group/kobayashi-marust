#!/bin/bash
# Read-only semantic diagnostic: rerun the pinned Konclude reference and emit
# only the full-IRI superclass closure of FMA Flagellum.
#SBATCH --job-name=km-10621-flag-ref
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "reference diagnostic failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
ontology=$km_root/corpus/ore_ont_10621.owl
ontology_sha256=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
konclude=$km_root/Konclude-official
konclude_sha256=5484f16dcff71486a5deed9cf9cea8a0f7febf115aaa6915ad2e8c1cf16965e3
pcre=$km_root/libpcre.so.3
pcre_sha256=18a3afc32488c647144f659d1629604df7ff58482a5734626dac65bd35eba8bd
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
[[ $(/usr/bin/sha256sum "$ontology" | /usr/bin/awk '{print $1}') == "$ontology_sha256" ]]
[[ $(/usr/bin/sha256sum "$konclude" | /usr/bin/awk '{print $1}') == "$konclude_sha256" ]]
[[ $(/usr/bin/sha256sum "$pcre" | /usr/bin/awk '{print $1}') == "$pcre_sha256" ]]

output=$routing_root/diagnostics/10621-flagellum-reference-$SLURM_JOB_ID
[[ ! -e $output ]]
/usr/bin/mkdir -p "$output"

set +e
/usr/bin/timeout --signal=TERM --kill-after=15s 240s \
    /usr/bin/env -i \
        PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
        LD_LIBRARY_PATH="$km_root:" \
        "$konclude" classification -w 16 -v \
            -i "$ontology" -o "$output/taxonomy.owl" \
    > "$output/konclude.stdout" 2> "$output/konclude.stderr"
konclude_rc=$?
set -e
/usr/bin/printf '%s\n' "$konclude_rc" > "$output/konclude.exit-code"
[[ $konclude_rc -eq 0 ]]
[[ -s $output/taxonomy.owl ]]

/usr/bin/python3 -I - "$output/taxonomy.owl" "$output/report.json" <<'PY'
import json
from pathlib import Path
import re
import sys

taxonomy = Path(sys.argv[1])
report_path = Path(sys.argv[2])
text = taxonomy.read_text(encoding="utf-8", errors="replace")
subclass = re.compile(
    r'<SubClassOf>\s*<Class\s+IRI="([^"]+)"\s*/>\s*'
    r'<Class\s+IRI="([^"]+)"\s*/>\s*</SubClassOf>',
    re.S,
)
equivalent = re.compile(r"<EquivalentClasses>(.*?)</EquivalentClasses>", re.S)
class_iri = re.compile(r'<Class\s+IRI="([^"]+)"\s*/>')
successors: dict[str, set[str]] = {}
for left, right in subclass.findall(text):
    successors.setdefault(left, set()).add(right)
for body in equivalent.findall(text):
    values = class_iri.findall(body)
    if len(values) < 2:
        continue
    first = values[0]
    for value in values[1:]:
        successors.setdefault(first, set()).add(value)
        successors.setdefault(value, set()).add(first)

target = "http://nlm.nih.gov/ontology/FMAInOWL#Flagellum"
top = "http://www.w3.org/2002/07/owl#Thing"
bottom = "http://www.w3.org/2002/07/owl#Nothing"
closure: set[str] = set()
pending = list(successors.get(target, ()))
while pending:
    current = pending.pop()
    if current in closure:
        continue
    closure.add(current)
    pending.extend(set(successors.get(current, ())) - closure)
closure.discard(target)
closure.discard(top)
closure.discard(bottom)
record = {
    "schema_version": 1,
    "target": target,
    "superclass_count": len(closure),
    "superclasses": sorted(closure),
}
report_path.write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(record, sort_keys=True))
PY

/usr/bin/sha256sum "$driver" "$ontology" "$konclude" "$pcre" \
    "$output/taxonomy.owl" "$output/report.json" \
    > "$output/artifacts.sha256"
/usr/bin/chmod a-w "$output"/*
/usr/bin/chmod a-w "$output"
/usr/bin/cat "$output/report.json"
