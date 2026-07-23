#!/bin/bash
# Build the source revision frozen by the rerun contract and every comparison variant.
#SBATCH --job-name=km-panel30-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=08:00:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260723-rerun/slurm-%x-%j.out

set -euo pipefail
[[ $# -eq 0 ]]

script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?missing Slurm submit directory}")
deployment_root=/ibex/scratch/hohndor/km/full-panel-20260723-rerun
if [[ -e $deployment_root/build ]]; then
    echo "refusing pre-existing build root: $deployment_root/build" >&2
    exit 2
fi
contract=$script_dir/full_panel_contract.py
historical_ledger=$script_dir/ontology-route-performance.pre-panel.tsv
base_builder=$script_dir/ibex_build_full_panel.sbatch
for required in \
    "$contract" "$historical_ledger" "$base_builder" \
    "$script_dir/audit_full_panel_route_coverage.py" \
    "$script_dir/full_panel_correctness.py" \
    "$script_dir/test_audit_full_panel_route_coverage.py" \
    "$script_dir/test_full_panel_chunks.py" \
    "$script_dir/test_full_panel_correctness.py" \
    "$script_dir/FullIriHermitOracle.java"
do
    [[ -s $required ]] || { echo "missing build input: $required" >&2; exit 2; }
done

/usr/bin/python3 "$script_dir/test_audit_full_panel_route_coverage.py"
/usr/bin/python3 "$script_dir/test_full_panel_chunks.py"
/usr/bin/python3 "$script_dir/test_full_panel_correctness.py"

km_commit=$(/usr/bin/python3 - "$contract" <<'PY'
import importlib.util
import re
import sys

path = sys.argv[1]
spec = importlib.util.spec_from_file_location("_frozen_panel_contract", path)
if spec is None or spec.loader is None:
    raise SystemExit(f"cannot import panel contract: {path}")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
revision = module.KM_REVISION
if not re.fullmatch(r"[0-9a-f]{40}", revision):
    raise SystemExit(f"invalid frozen KM revision: {revision!r}")
print(revision)
PY
)

/bin/bash "$base_builder" \
    "$deployment_root" \
    "$km_commit" \
    "$script_dir/ibex_build_full_panel_rerun.sbatch"

# A build is not eligible for the sweep unless its public routes exactly equal
# the frozen contract and every accepted historical environment is covered.
/usr/bin/python3 "$script_dir/audit_full_panel_route_coverage.py" \
    --ledger "$historical_ledger" \
    --contract "$contract" \
    --km-binary "$deployment_root/build/bin/km-main" \
    --output "$deployment_root/build/route-coverage-audit.json"

echo "RERUN_BUILD_COMPLETE root=$deployment_root revision=$km_commit job=$SLURM_JOB_ID"
