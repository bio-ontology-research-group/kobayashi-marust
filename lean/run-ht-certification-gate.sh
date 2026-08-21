#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
target_root="$repo_root/.work/target"

preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
else
    free_kib=$(df -Pk "$repo_root" | awk 'NR == 2 { print $4 }')
    available_kib=$(awk '/^MemAvailable:/ { print $2 }' /proc/meminfo)
    (( free_kib >= 20 * 1024 * 1024 )) || {
        echo "HT certification gate requires at least 20 GiB free disk" >&2
        exit 1
    }
    (( available_kib >= 16 * 1024 * 1024 )) || {
        echo "HT certification gate requires at least 16 GiB available memory" >&2
        exit 1
    }
fi

checkers=(
    ht-projection-cert-check
    ht-native-abox-taxonomy-matrix-cert-check
    ht-native-abox-cardinality-taxonomy-cert-check
    ht-native-abox-taxonomy-source-cert-check
    ht-native-abox-cardinality-taxonomy-source-cert-check
)

(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build
)

for checker in "${checkers[@]}"; do
    [[ -x "$bin_root/$checker" ]] || {
        echo "missing Lean checker: $bin_root/$checker" >&2
        exit 1
    }
done

(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_HT_TEST_LEAN_PROJECTION_CHECKER="$bin_root/ht-projection-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-taxonomy-matrix-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_MATRIX_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-taxonomy-source-cert-check"
    export KM_HT_TEST_LEAN_NATIVE_ABOX_CARDINALITY_TAXONOMY_SOURCE_CHECKER="$bin_root/ht-native-abox-cardinality-taxonomy-source-cert-check"

    cargo test --release source_matrix_passes_real_lean_checker -- --nocapture
    cargo test --release --test ht_taxonomy_certificate -- --nocapture
)
