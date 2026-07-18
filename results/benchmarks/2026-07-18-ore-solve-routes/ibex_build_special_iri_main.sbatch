#!/bin/bash
# Release gate for the source-IRI fix rebased onto the latest payg-strategy.
# The repository contents are staged under RUN_ROOT before submission.
#SBATCH --job-name=km-iri-main
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=01:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/special-iri-main-20260718/slurm/build-%j.out

set -euo pipefail

run_root=/ibex/scratch/hohndor/km/routing_20260715/special-iri-main-20260718
source_root=$run_root/source
target_root=$run_root/target
seed_target=/ibex/scratch/hohndor/km/routing_20260715/special-iri-fix-20260718/target

/usr/bin/mkdir -p "$run_root/slurm"
test -f "$source_root/tests/completeness-gaps/mini7914_unsat.ofn"
test -f "$source_root/tests/completeness-gaps/mini7914_chain_recognition.ofn"

if [[ ! -e "$target_root/CACHEDIR.TAG" ]]; then
    /usr/bin/cp -a "$seed_target" "$target_root"
fi

cd "$source_root/engine"
export CARGO_TARGET_DIR=$target_root

/usr/bin/printf 'BUILD_START host=%s rustc=%s source=%s\n' \
    "$(hostname)" "$(rustc --version)" "$source_root"

cargo test --release
module load python/3.11.0
MOOSE_HOME=/ibex/scratch/hohndor/km/moose \
    PYTHONPATH=py python3 py/test_frontend_special_iris.py -v
cargo build --release --bin km --bin ofn

/usr/bin/sha256sum "$target_root/release/km" "$target_root/release/ofn" \
    > "$run_root/binaries.sha256"
/usr/bin/find "$source_root" -type f -not -path '*/target/*' -print0 \
    | /usr/bin/sort -z \
    | /usr/bin/xargs -0 /usr/bin/sha256sum \
    > "$run_root/source-files.sha256"

/usr/bin/printf 'BUILD_DONE host=%s binary=%s\n' \
    "$(hostname)" "$target_root/release/km"
