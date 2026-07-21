#!/bin/bash
# Hash every ontology named by the frozen 592-row route registry on an IBEX
# compute node. This is input provenance only and does not invoke a reasoner.
#SBATCH --job-name=ore-corpus-hash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "corpus manifest failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__ore_corpus_manifest_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        OUTPUT_ROOT="${OUTPUT_ROOT:?export a new persistent OUTPUT_ROOT}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        "${optional_slurm[@]}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
[[ $SLURM_CPUS_PER_TASK == 1 ]]

routing_root=/ibex/scratch/hohndor/km/routing_20260715
corpus_root=/ibex/scratch/hohndor/km/corpus
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
registry=$submit_dir/ontology-solve-routes.tsv
registry_sha256=bd149a8d2a24cf46d0fd39feb12b821f2ea8cb0f00c2012f4ae4fe36e8121522
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1

expected_entries=(
    ibex_capture_ore_corpus_manifest.sbatch
    ontology-solve-routes.tsv
)
mapfile -t actual_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_entries[@]} -eq ${#expected_entries[@]} ]]
for index in "${!expected_entries[@]}"; do
    [[ ${actual_entries[$index]} == "${expected_entries[$index]}" ]]
done
[[ -f $registry && ! -L $registry ]]
[[ $(/usr/bin/sha256sum "$registry" | /usr/bin/awk '{print $1}') == "$registry_sha256" ]]
[[ $(/usr/bin/sha256sum /usr/bin/python3 | /usr/bin/awk '{print $1}') == "$python_sha256" ]]
[[ $OUTPUT_ROOT == $routing_root/ore-corpus-manifests/* ]]
[[ ! -e $OUTPUT_ROOT ]]
/usr/bin/mkdir -p "$OUTPUT_ROOT"
/usr/bin/install -m 0444 "$registry" "$OUTPUT_ROOT/ontology-solve-routes.tsv"
/usr/bin/install -m 0555 "$driver" "$OUTPUT_ROOT/ibex_capture_ore_corpus_manifest.sbatch"

/usr/bin/python3 -I - \
    "$registry" "$corpus_root" "$OUTPUT_ROOT" "$registry_sha256" \
    "$driver_sha256" "$python_sha256" <<'PY'
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import sys

registry, corpus, output = map(Path, sys.argv[1:4])
registry_sha, driver_sha, python_sha = sys.argv[4:]
with registry.open(newline="", encoding="utf-8") as stream:
    rows = list(csv.DictReader(stream, delimiter="\t"))
names = [row["ontology"] for row in rows]
if len(names) != 592 or len(set(names)) != 592:
    raise SystemExit("the frozen registry does not name 592 unique ontologies")
if any(re.fullmatch(r"ore_ont_[0-9]+\.owl", name) is None for name in names):
    raise SystemExit("the registry contains an invalid ontology name")

def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()

manifest = bytearray()
table = ["ontology\tsha256\tbytes\n"]
total_bytes = 0
for name in names:
    path = corpus / name
    if not path.is_file() or path.is_symlink():
        raise SystemExit(f"invalid corpus input: {path}")
    size = path.stat().st_size
    sha = digest(path)
    total_bytes += size
    manifest.extend(f"{sha}  {path}\n".encode())
    table.append(f"{name}\t{sha}\t{size}\n")
(output / "ore-corpus-files.sha256").write_bytes(manifest)
(output / "ore-corpus.tsv").write_text("".join(table), encoding="utf-8")
receipt = {
    "schema_version": 1,
    "status": "verified",
    "reasoner_executed": False,
    "registry_sha256": registry_sha,
    "registry_row_count": len(rows),
    "corpus_root": str(corpus),
    "ontology_count": len(names),
    "total_bytes": total_bytes,
    "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
    "table_sha256": digest(output / "ore-corpus.tsv"),
    "driver_sha256": driver_sha,
    "python_sha256": python_sha,
    "slurm_job_id": int(os.environ["SLURM_JOB_ID"]),
    "host": os.uname().nodename,
}
(output / "RECEIPT.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(receipt, sort_keys=True))
PY

/usr/bin/sha256sum "$OUTPUT_ROOT/RECEIPT.json" > "$OUTPUT_ROOT/RECEIPT.sha256"
/usr/bin/find "$OUTPUT_ROOT" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$OUTPUT_ROOT" -type d -exec /usr/bin/chmod 0555 {} +
