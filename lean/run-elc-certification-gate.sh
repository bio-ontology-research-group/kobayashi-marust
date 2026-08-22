#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
target_root="$repo_root/.work/target"
artifact_root="$repo_root/.work/artifacts"
surface_log="$artifact_root/elc-certification-surface.log"

mkdir -p "$artifact_root"
preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
else
    /home/leechuck/Public/software/kobayashi-marust/tools/workspace-preflight.sh
fi

(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build
    LEAN_NUM_THREADS=4 lake build elc-cert-check
    LEAN_NUM_THREADS=4 lake build ContextCalculus.ELCompletionPublication \
        2>&1 | tee "$surface_log"
)

if grep -q 'sorryAx' "$surface_log"; then
    echo "ELC certification surface depends on an admitted theorem" >&2
    exit 1
fi

grep -q "ELCompletionPublication.*checkV5_publication_semantics\|'ContextCalculus.ELCompletion.DecodedCertificate.checkV5_publication_semantics'" \
    "$surface_log" || {
    echo "missing ELC publication-surface axiom audit" >&2
    exit 1
}

checker="$bin_root/elc-cert-check"
[[ -x "$checker" ]] || {
    echo "missing Lean checker: $checker" >&2
    exit 1
}

(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_ELC_TEST_LEAN_CHECKER="$checker"
    cargo test --release --lib \
        elcomplete::tests::lean_certificate_reconstructs_and_audits_the_production_fixpoint \
        -- --nocapture
    cargo test --release --lib \
        elcomplete::tests::lean_v5_certificate_checks_source_partition_and_rejects_tampering \
        -- --nocapture
    cargo test --release --lib \
        elcomplete::tests::lean_residual_compilation_payload_accepts_and_tampering_fails \
        -- --nocapture
    cargo test --release --test elc_certificate -- --nocapture
)

echo "ELC certification gate passed"
