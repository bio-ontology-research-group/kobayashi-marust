#!/bin/bash
# Supplemental build used by the initial panel after the main build had begun.
# Fresh reproductions get the identical class from ibex_build_full_panel.sbatch.
#SBATCH --job-name=km-hermit-oracle-build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/full-panel-20260722/slurm-%x-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/full-panel-20260722
build_root=$root/build
benchmark_root=/ibex/scratch/hohndor/km/bench
jdk=$benchmark_root/jdk8u492-b09
script_dir=$(/usr/bin/readlink -f "${SLURM_SUBMIT_DIR:?missing Slurm submit directory}")

"$jdk/bin/javac" -cp "$benchmark_root/hermit_cp/*" -d "$build_root/bin" \
    "$script_dir/FullIriHermitOracle.java"
/usr/bin/sha256sum "$script_dir/FullIriHermitOracle.java" \
    "$build_root/bin/FullIriHermitOracle.class" \
    > "$build_root/hermit-fulliri.sha256"
/usr/bin/python3 - "$build_root" "$SLURM_JOB_ID" "$script_dir/FullIriHermitOracle.java" <<'PY'
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1])
job = sys.argv[2]
source = Path(sys.argv[3]).resolve(strict=True)
receipt_path = root / "build-receipt.json"
receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
class_path = root / "bin" / "FullIriHermitOracle.class"
digest = hashlib.sha256(class_path.read_bytes()).hexdigest()
receipt["binaries"][class_path.name] = {
    "path": str(class_path),
    "resolved_path": str(class_path.resolve(strict=True)),
    "sha256": digest,
}
receipt.setdefault("supplemental_builds", []).append(
    {
        "kind": "full-IRI HermiT oracle",
        "slurm_job_id": job,
        "source": str(source),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "binary_sha256": digest,
    }
)
primary_script = root / "executed-primary-build.sbatch"
if primary_script.is_file():
    receipt["build_script"] = str(primary_script)
    receipt["build_script_sha256"] = hashlib.sha256(primary_script.read_bytes()).hexdigest()
receipt["toolchain"] = {
    "cargo": subprocess.check_output(
        ["/home/hohndor/.cargo/bin/cargo", "--version"], text=True
    ).strip(),
    "rustc": subprocess.check_output(
        ["/home/hohndor/.cargo/bin/rustc", "--version", "--verbose"], text=True
    ).strip(),
    "rustdl_cargo": subprocess.check_output(
        [
            "/home/hohndor/.cargo/bin/rustup",
            "run",
            "1.95.0",
            "cargo",
            "--version",
        ],
        text=True,
    ).strip(),
    "rustdl_rustc": subprocess.check_output(
        [
            "/home/hohndor/.cargo/bin/rustup",
            "run",
            "1.95.0",
            "rustc",
            "--version",
            "--verbose",
        ],
        text=True,
    ).strip(),
    "java": subprocess.check_output(
        ["/ibex/scratch/hohndor/km/bench/jdk8u492-b09/bin/java", "-version"],
        stderr=subprocess.STDOUT,
        text=True,
    ).strip(),
}
temporary = receipt_path.with_suffix(".json.tmp")
temporary.write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
temporary.replace(receipt_path)
with (root / "binaries.sha256").open("w", encoding="utf-8") as handle:
    for name, row in sorted(receipt["binaries"].items()):
        handle.write(f"{row['sha256']}  {name}\n")
PY
/usr/bin/printf 'HERMIT_ORACLE_BUILD_COMPLETE job=%s\n' "$SLURM_JOB_ID"
