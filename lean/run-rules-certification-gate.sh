#!/usr/bin/env bash
# Rules certification gate, two parts.
#
# 1. The answers of the rule worker (KM_RULES_CONSISTENCY, KM_RULES_CLASSIFY):
#    ContextCalculus/RulesRoute*.lean, checker rules-cert-check,
#    docs/DL-SAFE-RULES.md "Lean coverage". It audits the theorem surface,
#    runs the checker on the hand-written fixtures (valid ones accepted,
#    forged ones rejected) and runs engine/tests/rules_lean_certificate.rs,
#    whose km runs write certificates and fail closed on a rejection.
# 2. The inert-sort release of the rule-consistency
# worker input (engine/src/orchestrate/inert_sorts.rs, docs/NOMINALS-CB.md
# section 6). It audits the Lean theorem surface of
# ContextCalculus/RulesInertSortRelease.lean, runs the checker on a valid and
# a forged fixture, and runs the Rust tests that emit certificates and require
# the Lean checker to accept them: the randomized release check, a small
# finite-rule fixture and ore_ont_7278.
#
# KM_RULES_GATE_ORE_7278 names ore_ont_7278.owl (default: the first of the
# candidate paths below that exists). The gate fails when it is missing.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_root="$repo_root/lean"
engine_root="$repo_root/engine"
bin_root="$lean_root/.lake/build/bin"
work_root="${KM_WORK_ROOT:-$repo_root/.work}"
target_root="$work_root/target"
artifact_root="$work_root/artifacts"
surface_log="$artifact_root/rules-certification-surface.log"
route_surface_log="$artifact_root/rules-route-certification-surface.log"

mkdir -p "$artifact_root"
preflight="$repo_root/tools/workspace-preflight.sh"
if [[ -x "$preflight" ]]; then
    "$preflight"
fi

ore_7278="${KM_RULES_GATE_ORE_7278:-}"
if [[ -z "$ore_7278" ]]; then
    for candidate in \
        "$repo_root/.work/inputs/ore_ont_7278.owl" \
        "$HOME/ore2015/pool_sample/files/ore_ont_7278.owl" \
        "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/subset-blocking-cost/inputs/ore_ont_7278.owl"
    do
        if [[ -f "$candidate" ]]; then
            ore_7278="$candidate"
            break
        fi
    done
fi
[[ -f "$ore_7278" ]] || {
    echo "rules certification gate needs ore_ont_7278.owl (set KM_RULES_GATE_ORE_7278)" >&2
    exit 1
}

checker="$bin_root/rules-inert-sort-release-check"
route_checker="$bin_root/rules-cert-check"
cleanup_native_checker() {
    [[ "${KM_CERT_KEEP_NATIVE_CHECKERS:-0}" == "1" ]] && return
    [[ ! -e "$checker" ]] || unlink "$checker"
    [[ ! -e "$route_checker" ]] || unlink "$route_checker"
}
trap cleanup_native_checker EXIT

(
    cd "$lean_root"
    LEAN_NUM_THREADS=4 lake build
    LEAN_NUM_THREADS=4 lake build rules-inert-sort-release-check
    LEAN_NUM_THREADS=4 lake build rules-cert-check
    LEAN_NUM_THREADS=4 lake build ContextCalculus.RulesInertSortRelease 2>&1 | tee "$surface_log"
    LEAN_NUM_THREADS=4 lake build ContextCalculus.RulesRouteCertificate 2>&1 | tee "$route_surface_log"
)

# Part 1: rule-route answers.
if grep -q 'sorryAx' "$route_surface_log"; then
    echo "rule-route certification surface depends on an admitted theorem" >&2
    exit 1
fi
for theorem in clauseModel_of_dlSafeModel dlSafeModel_of_clauseModel FModel.check_sound \
    checkProof_sound refutation_inconsistent refutation_unsat refutation_sub \
    Certificate.check_sound WireRulesCertificate.check_sound
do
    grep -q "'ContextCalculus.RulesRoute.$theorem' depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$route_surface_log" ||
    grep -q "'ContextCalculus.RulesRoute.$theorem' depends on axioms: \[propext, Quot.sound\]" "$route_surface_log" || {
        echo "missing rule-route certification-surface axiom audit: $theorem" >&2
        exit 1
    }
done
[[ -x "$route_checker" ]] || { echo "missing Lean checker: $route_checker" >&2; exit 1; }
for fixture in "$lean_root"/testdata/rules-route-*-valid.json; do
    "$route_checker" "$fixture"
done
for fixture in "$lean_root"/testdata/rules-route-*-forged.json; do
    if "$route_checker" "$fixture"; then
        echo "forged rule-route certificate was accepted: $fixture" >&2
        exit 1
    fi
done
(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_REQUIRE_LEAN_CHECKERS=1
    export KM_RULES_TEST_LEAN_CHECKER="$route_checker"
    export KM_RULES_TEST_ORE_7278="$ore_7278"
    cargo test --release --test rules_lean_certificate -- --nocapture --test-threads=1
)

# Part 2: the inert-sort release.

if grep -q 'sorryAx' "$surface_log"; then
    echo "rules certification surface depends on an admitted theorem" >&2
    exit 1
fi
for theorem in release_equisatisfiable release_equisatisfiable_clauses \
    WireInertSortRelease.check_sound extend_models restrict_models
do
    grep -q "'ContextCalculus.RulesInertSort.$theorem' depends on axioms: \[propext" "$surface_log" ||
    grep -q "'ContextCalculus.RulesInertSort.$theorem' does not depend on any axioms" "$surface_log" || {
        echo "missing rules certification-surface axiom audit: $theorem" >&2
        exit 1
    }
done
[[ -x "$checker" ]] || { echo "missing Lean checker: $checker" >&2; exit 1; }
"$checker" "$lean_root/testdata/rules-inert-valid.json"
if "$checker" "$lean_root/testdata/rules-inert-forged.json"; then
    echo "forged inert-sort release certificate was accepted" >&2
    exit 1
fi

(
    cd "$engine_root"
    export CARGO_TARGET_DIR="$target_root"
    export KM_REQUIRE_LEAN_CHECKERS=1
    export KM_RULES_TEST_INERT_LEAN_CHECKER="$checker"
    export KM_RULES_TEST_ORE_7278="$ore_7278"
    cargo test --release --lib orchestrate::inert_sorts -- --nocapture --test-threads=1
    cargo test --release --test rules_inert_sort_certificate -- --nocapture --test-threads=1
)
echo "rules certification gate passed"
