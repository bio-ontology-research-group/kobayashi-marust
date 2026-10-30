#!/usr/bin/env python3
"""Assemble BENCHMARKS.md, build-completion.json, SHA256SUMS and manifest.json
for the v1.5.4 release assets from the local copies of the Ibex run records
(`../data/`) and the certification receipts (`gate-work/`, `full-rust-execution/`,
`../../pgo-v154/`). Pure assembly: every number is computed from the records.
"""
import datetime
import hashlib
import json
import os
import statistics
import subprocess
import sys

W = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work"
CTL = W + "/v154-release-cert/ctl"
LOGS = W + "/v154-release-cert/logs"
DATA = W + "/v154-release-cert/data"
PGO = W + "/pgo-v154"
ASSETS = W + "/v154-release-assets-80c8f82a"
TAG = "v1.5.4"
VERSION = "1.5.4"
COMMIT = "80c8f82aea9c99db89b7fa3885cc2c63010aa7f6"
RUNS = {
    "paired_design": ("paired-design-54786965", "54786965", "design run 9, run_paired.py, both policies, 300 s"),
    "paired_held_out": ("paired-held_out-54796887", "54796887", "held-out paired run, run_paired.py, both policies, 300 s"),
    "g8_v154": ("g8-v154-54796888", "54796888", "held-out protocol run of the v1.5.4 PGO binary, run_combined.py (240 s, 20 GiB, scoped watchdog)"),
    "g8_v153_sameday": ("g8-v153-sameday-54801090", "54801090", "held-out protocol run of the v1.5.3 PGO binary, same evening, same protocol"),
    "v153_baseline": ("combined-v150-54539952", "54539952", "v1.5.3 PGO protocol run of 2026-10-25 (all 1,708 inputs)"),
}
IBEX_ROOT = "/ibex/scratch/projects/c2014/hohndor/km/v154-routing-20261026"
IBEX_PERF = "/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005"
IBEX_DIRS = {
    "paired_design": IBEX_ROOT + "/paired-design-54786965/chunks",
    "paired_held_out": IBEX_ROOT + "/paired-held_out-54796887/chunks",
    "g8_v154": IBEX_PERF + "/g8-v154-80c8f82a/g8-v154-54796888/chunks",
    "g8_v153_sameday": IBEX_PERF + "/g8-v153-sameday-baseline/g8-v153-sameday-54801090/chunks",
    "v153_baseline": IBEX_PERF + "/recovery-v153-scoped-20261025/combined-v150-54539952/chunks",
}
KONCLUDE_RUN = "/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004/classification-konclude-53201252/konclude"


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def load_run(name):
    d = os.path.join(DATA, RUNS[name][0])
    outcomes, chunk_hashes, meta = [], {}, {}
    for f in sorted(os.listdir(d)):
        p = os.path.join(d, f)
        chunk_hashes[f] = sha(p)
        x = json.load(open(p))
        meta.setdefault("status", set()).add(x.get("status"))
        for k in ("runner_sha256", "inventory_sha256", "manifest_sha256", "half", "policies"):
            if k in x:
                meta.setdefault(k, set()).add(json.dumps(x[k]) if isinstance(x[k], list) else x[k])
        outcomes.extend(x["outcomes"])
    meta = {k: sorted(v) for k, v in meta.items()}
    return outcomes, chunk_hashes, meta


def by_ont(outcomes, policy=None):
    return {r["ontology"]: r for r in outcomes if policy is None or r.get("policy") == policy}


def ver(d):
    return {o for o, r in d.items() if r.get("verified_solved")}


def ratios(a, b, common):
    ta = [a[o]["wall_s"] for o in common]
    tb = [b[o]["wall_s"] for o in common]
    return {
        "common": len(common),
        "sum_candidate_s": round(sum(ta), 3),
        "sum_baseline_s": round(sum(tb), 3),
        "mean_candidate_s": statistics.mean(ta),
        "mean_baseline_s": statistics.mean(tb),
        "mean_ratio": statistics.mean(ta) / statistics.mean(tb),
        "median_candidate_s": statistics.median(ta),
        "median_baseline_s": statistics.median(tb),
        "median_ratio": statistics.median(ta) / statistics.median(tb),
    }


split = json.load(open(DATA + "/split.json"))
design, held = set(split["design"]), set(split["held_out"])
konc = json.load(open(DATA + "/konclude-20261004-records.json"))

runs = {k: load_run(k) for k in RUNS}
pd_v153 = by_ont(runs["paired_design"][0], "v153")
pd_gen = by_ont(runs["paired_design"][0], "general")
ph_v153 = by_ont(runs["paired_held_out"][0], "v153")
ph_gen = by_ont(runs["paired_held_out"][0], "general")
g8n = {o: r for o, r in by_ont(runs["g8_v154"][0]).items() if o in held}
g8s = {o: r for o, r in by_ont(runs["g8_v153_sameday"][0]).items() if o in held}
base_all = by_ont(runs["v153_baseline"][0])
base_d = {o: r for o, r in base_all.items() if o in design}
base_h = {o: r for o, r in base_all.items() if o in held}


def konclude_solved(base):
    """Konclude counts as solved when its 2026-10-04 run executed with exit 0 and,
    wherever v1.5.3's answer is verified, agrees with it (the v1.5.3 baseline
    records the comparison)."""
    solved = set()
    for o, rec in konc.items():
        executed = rec.get("status") == "executed_unvalidated" and rec.get("exit_code") == 0
        agree = base.get(o, {}).get("comparisons", {}).get("konclude", {}).get("status")
        if executed and (agree == "agreement" or not base.get(o, {}).get("verified_solved")):
            solved.add(o)
    return solved


def summarise(cand, base, half_set, label):
    a, b = ver(cand) & half_set, ver(base) & half_set
    common = sorted(a & b)
    wrong = sorted(o for o, r in cand.items() if r.get("wrong") and o in half_set)
    s = {
        "label": label,
        "inputs": len(half_set),
        "outcomes": len([o for o in cand if o in half_set]),
        "verified": len(a),
        "baseline_verified": len(b),
        "lost": sorted(b - a),
        "gained": sorted(a - b),
        "flagged_wrong": wrong,
    }
    s.update(ratios(cand, base, common))
    return s


summary = {
    "design_v153_policy_vs_v153_baseline": summarise(pd_v153, base_d, design, "design half, v1.5.4 binary under the v1.5.3 policy, against the v1.5.3 PGO run of 2026-10-25"),
    "design_general_policy_vs_v153_baseline": summarise(pd_gen, base_d, design, "design half, v1.5.4 binary under the general policy, against the v1.5.3 PGO run of 2026-10-25"),
    "held_out_v153_policy_vs_v153_baseline": summarise(ph_v153, base_h, held, "held-out half, v1.5.4 binary under the v1.5.3 policy, against the v1.5.3 PGO run of 2026-10-25"),
    "held_out_general_policy_vs_v153_baseline": summarise(ph_gen, base_h, held, "held-out half, v1.5.4 binary under the general policy, against the v1.5.3 PGO run of 2026-10-25"),
    "g8_protocol_vs_v153_baseline_20261025": summarise(g8n, base_h, held, "G8 protocol run against the v1.5.3 PGO run of 2026-10-25"),
    "g8_protocol_vs_v153_sameday": summarise(g8n, g8s, held, "G8 protocol run against the same-day v1.5.3 protocol run"),
}
policy_pairs = {
    "design_run9_general_vs_v153_policy": summarise(pd_gen, pd_v153, design, "design run 9: general policy against the v1.5.3 policy on the same binary"),
    "held_out_paired_general_vs_v153_policy": summarise(ph_gen, ph_v153, held, "held-out paired run: general policy against the v1.5.3 policy on the same binary"),
}
# four-run common set (RUNS.md decomposition)
four = sorted(ver(g8n) & ver(g8s) & ver(ph_v153) & ver(ph_gen))
decomp = {
    "common": len(four),
    "total_g8_vs_sameday": ratios(g8n, g8s, four),
    "engine_only_v154_binary_v153_policy_vs_v153_binary": ratios(ph_v153, g8s, four),
    "policy_only_general_vs_v153_policy_same_binary": ratios(ph_gen, ph_v153, four),
    "noise_floor_same_binary_and_policy_paired_vs_protocol": ratios(ph_gen, g8n, four),
}
bound = 1.10 * decomp["total_g8_vs_sameday"]["sum_baseline_s"]
excess = decomp["total_g8_vs_sameday"]["sum_candidate_s"] - bound
deltas = sorted(((g8n[o]["wall_s"] - g8s[o]["wall_s"], o) for o in four), reverse=True)
top = [{"ontology": o, "v153_sameday_s": round(g8s[o]["wall_s"], 2), "v154_s": round(g8n[o]["wall_s"], 2), "delta_s": round(d, 2)} for d, o in deltas[:15]]

ks = konclude_solved(base_all)
kh = ks & held
ck = sorted(ver(g8n) & kh)
konclude_clause = {
    "konclude_run": KONCLUDE_RUN,
    "konclude_solved_held_out": len(kh),
    "v154_verified_held_out": len(ver(g8n)),
    "common": len(ck),
    "mean_v154_s": statistics.mean(g8n[o]["wall_s"] for o in ck),
    "mean_konclude_s": statistics.mean(konc[o]["wall_s"] for o in ck),
    "median_v154_s": statistics.median(g8n[o]["wall_s"] for o in ck),
    "median_konclude_s": statistics.median(konc[o]["wall_s"] for o in ck),
    "caveat": "Konclude ran on 2026-10-04 on other nodes; the clause needs a same-day Konclude run to be judged, which was not made.",
}

# ---- receipts
gates = {g: json.load(open(f"{CTL}/gate-work/{g}-gate-receipt.json")) for g in ("elc", "routing", "ht", "cb")}
rust = json.load(open(CTL + "/full-rust-execution/receipt.json"))
pins = json.load(open(CTL + "/pins.json"))
native = json.load(open(PGO + "/native-build-receipt.json"))
bfd = json.load(open(PGO + "/pgo-use-bfd-build.json"))
merge = json.load(open(PGO + "/merge-receipt.json"))
mvn_log = LOGS + "/mvn-package-from-tag.log"
java_log = LOGS + "/java-from-tag.log"
jar = ASSETS + "/kobayashi-marust-protege-1.5.4.jar"
binary = ASSETS + "/km-v1.5.4-linux-x86_64"
source = ASSETS + "/km-v1.5.4-certified-source.tar.gz"
assert sha(binary) == bfd["binary_sha256"], "asset binary is not the receipted PGO binary"
java_receipt = {
    "schema": "km-v154-java-receipt-v1",
    "source_commit": subprocess.check_output(["git", "-C", W + "/gates-4dd7995b/src", "rev-parse", "HEAD"], text=True).strip(),
    "execution_source": W + "/gates-4dd7995b/src/protege",
    "command": [W + "/tools/apache-maven-3.9.9/bin/mvn", "-o", "-B", "-Dkm.bin=" + PGO + "/km-pgo-use", "package"],
    "km_binary_for_tests": {"path": PGO + "/km-pgo-use", "sha256": native["binary_sha256"], "note": "the ws-linked profile-use build (needs GLIBC_2.39); same source, profile and flags as the released binary, which is linked through the glibc wrapper"},
    "jdk": subprocess.run(["java", "-version"], capture_output=True, text=True).stderr.splitlines()[0],
    "maven": "Apache Maven 3.9.9",
    "tests": {"run": 76, "failures": 0, "errors": 0, "skipped": 0},
    "test_run_log": {"path": java_log, "sha256": sha(java_log)},
    "package_log": {"path": mvn_log, "sha256": sha(mvn_log)},
    "jar_sha256": sha(jar),
}
assert java_receipt["source_commit"] == COMMIT
with open(mvn_log) as f:
    assert "Tests run: 76, Failures: 0, Errors: 0, Skipped: 0" in f.read()

accept = {
    "contract": "docs/V1.5.4-ACCEPTANCE.md with the approved amendments of 2026-10-27, 2026-10-28 and 2026-10-28 (second)",
    "G1_G5": {"status": "evidence_in_repository", "references": ["docs/V1.5.4-ROUTING-INVENTORY.md", "docs/V1.5.4-STATUS.md", "engine/tests (metamorphic routing tests run by the Rust recipe)"]},
    "G6_held_out_evaluation": {"status": "done", "split": DATA + "/split.json", "split_sha256": sha(DATA + "/split.json"), "design_inputs": len(design), "held_out_inputs": len(held), "held_out_runs": ["54796887 (paired)", "54796888 (protocol)", "54801090 (same-day v1.5.3 protocol)"]},
    "G7_correctness": {"status": "met", "wrong_answers_attributable_to_km": [], "flagged_wrong_held_out": summary["held_out_general_policy_vs_v153_baseline"]["flagged_wrong"], "note": "ore_ont_3794 is a Konclude incompleteness: HermiT entails all ten KM-only subsumptions (results/benchmarks/2026-10-26-v154-routing/held-out-3794-adjudication/)"},
    "G8_performance": {
        "no_loss": {"status": "met_under_amendments_2_and_3", "verified_v154": summary["g8_protocol_vs_v153_baseline_20261025"]["verified"], "verified_v153_20261025": summary["g8_protocol_vs_v153_baseline_20261025"]["baseline_verified"], "lost": summary["g8_protocol_vs_v153_baseline_20261025"]["lost"], "lost_classification": {"ore_ont_10874": "amendment 3 (nominal-mode answer only from the complete regime); also publishes 879 data-property assertions as dropped", "ore_ont_7610": "amendment 2 (v1.5.3 answered after silently discarding 613 data-property assertions)"}},
        "median": {"status": "met", "ratio_vs_sameday": decomp["total_g8_vs_sameday"]["median_ratio"], "bound": 1.10},
        "mean": {"status": "NOT_MET", "ratio_vs_sameday": decomp["total_g8_vs_sameday"]["mean_ratio"], "bound": 1.10, "sum_v154_s": decomp["total_g8_vs_sameday"]["sum_candidate_s"], "sum_v153_sameday_s": decomp["total_g8_vs_sameday"]["sum_baseline_s"], "allowed_sum_s": round(bound, 3), "excess_s": round(excess, 3), "attribution": "ore_ont_205 (checked subset blocking, card arm, soundness fix), ore_ont_7278 and ore_ont_3726 (data-property assertions carried into the rules-consistency worker, soundness fix), six inputs the general policy sends to certified_nominals instead of the Konclude bridge; see results/benchmarks/2026-10-26-v154-routing/RUNS.md and docs/V1.5.4-STATUS.md", "decision": "pending the maintainer (amendment, re-tag with the blocking fix, or hold)"},
        "konclude": {"status": "more_verified_than_konclude; speed clause not judged (no same-day Konclude run)", **{k: v for k, v in konclude_clause.items()}},
        "vs_20261025_baseline_for_reference": {"mean_ratio": summary["g8_protocol_vs_v153_baseline_20261025"]["mean_ratio"], "median_ratio": summary["g8_protocol_vs_v153_baseline_20261025"]["median_ratio"], "note": "different day and nodes; the same-day run is the comparison of record"},
    },
    "G9_release_gates": {"status": "met", "lean_gates": {g: gates[g]["status"] for g in gates}, "rust": rust["status"], "rust_counts": rust["counts"], "java_tests": java_receipt["tests"]},
    "G10_documentation": {"status": "evidence_in_repository", "references": ["docs/RELEASE-1.5.4.md", "CHANGELOG.md", "docs/V1.5.4-ROUTING-INVENTORY.md"]},
}

completion = {
    "schema": "km-v154-release-completion-v1",
    "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
    "tag": TAG,
    "version": VERSION,
    "release_commit": COMMIT,
    "engine_tree_note": "engine/ tree identical to freeze candidate 0a0d73c8 plus the version bump (engine/Cargo.toml, Cargo.lock, protege/pom.xml, README jar name)",
    "status": "complete_except_G8_mean; release decision pending the maintainer (docs/V1.5.4-STATUS.md, Release decision)",
    "authorized_performance_exception": None,
    "source_manifests": {
        "certification_complete_source_manifest": {"path": CTL + "/complete-source-manifest.json", "sha256": pins["manifest_sha256"]},
        "pgo_pipeline_source_manifest": {"path": PGO + "/source-manifest.json", "sha256": native["source_manifest_sha256"]},
    },
    "pins": pins,
    "certification": gates,
    "rust_ci_receipt": rust,
    "java_receipt": java_receipt,
    "pgo": {
        "pipeline": PGO + "/run_pgo_pipeline.py",
        "native_build_receipt": native,
        "released_binary_build": bfd,
        "merge_receipt": merge,
        "training_receipt_sha256": native["training_receipt_sha256"],
        "merged_profile_sha256": native["merged_profile_sha256"],
        "linker_wrapper": {"path": PGO + "/cc-wrapper.sh", "sha256": bfd["linker_wrapper_sha256"], "purpose": bfd["linker_wrapper_purpose"]},
        "note": "km-pgo-use (sha ac15b822…) is the same source, profile and flags linked for ws; it needs GLIBC_2.39 and is not released. The released binary is the wrapper-linked km-pgo-use-bfd.",
    },
    "benchmark": {
        "protocol": "docs/V1.5.4-ACCEPTANCE.md G6 and G8; v1.5.3 protocol: run_combined.py, one core, 240 s, 20 GiB, scoped watchdog, gold-6248 nodes; paired design: run_paired.py, 300 s, both policies on the same binary",
        "released_binary_sha256": bfd["binary_sha256"],
        "v153_baseline_binary": "v1.5.3 release PGO binary (sha 2470b041…), rerun same day as 54801090",
        "runs": {k: {"ibex_dir": IBEX_DIRS[k], "slurm_array": RUNS[k][1], "description": RUNS[k][2], "chunks": len(runs[k][1]), "chunk_sha256": runs[k][1], "meta": runs[k][2]} for k in RUNS},
        "ibex_file_hashes": {"g8_v154_combined_files_sha256": sha(DATA + "/combined-files.sha256"), "g8_v153_sameday_combined_files_sha256": sha(DATA + "/combined-files-sameday.sha256")},
        "inventory_sha256": sha(DATA + "/inventory.json"),
        "split_sha256": sha(DATA + "/split.json"),
        "konclude_records_sha256": sha(DATA + "/konclude-20261004-records.json"),
        "summary_vs_v153_run_20261025": summary,
        "policy_comparisons_same_binary": policy_pairs,
        "g8_decomposition_556": decomp,
        "g8_largest_deltas": top,
    },
    "acceptance": accept,
    "documents": ["docs/RELEASE-1.5.4.md", "CHANGELOG.md", "docs/V1.5.4-ACCEPTANCE.md", "docs/V1.5.4-STATUS.md", "results/benchmarks/2026-10-26-v154-routing/RUNS.md"],
}


def f2(x):
    return f"{x:.3f}"


# ---- BENCHMARKS.md
L = []
L.append("# KM v1.5.4 benchmark results\n")
L.append(f"Tag `{TAG}`, commit `{COMMIT}`. Measured binary: the profile-guided build of the tag linked through the glibc wrapper (sha256 `{bfd['binary_sha256']}`, the released `km-v1.5.4-linux-x86_64`). All runs on Ibex gold-6248 nodes, one core per input. The machine-readable record is `build-completion.json`; the narrative is `results/benchmarks/2026-10-26-v154-routing/RUNS.md` in the source archive.\n")
L.append("## Method\n")
L.append("The 1,708-input pool of the v1.5.3 campaign is split into a design half (1,123 inputs) and a held-out half (585), `split.json`. The general routing policy was developed on the design half only. Each input is classified once per policy; the answer is verified against the Konclude, HermiT and Openllet taxonomies of the reference audit; an input counts as verified when KM answers inside the budget and the taxonomy agrees with the references. Paired runs (`run_paired.py`, 300 s) run both policies on the same binary in one task; protocol runs (`run_combined.py`, 240 s, 20 GiB, scoped watchdog) are the v1.5.3 measurement protocol and are the basis of G8.\n")
L.append("| Run | Slurm array | Binary | Policy | Inputs |\n|---|---|---|---|---|")
L.append("| design run 9 (paired) | 54786965 | v1.5.4 release-candidate build a42e3816 of 0a0d73c8 (engine tree of the tag) | v153 and general | 1,123 |")
L.append("| held-out paired | 54796887 | v1.5.4 PGO 5f5901d8 | v153 and general | 585 |")
L.append("| held-out protocol (G8) | 54796888 | v1.5.4 PGO 5f5901d8 | general (default) | 585 |")
L.append("| held-out protocol, same day | 54801090 | v1.5.3 PGO 2470b041 | v1.5.3 | 585 |")
L.append("| v1.5.3 baseline, 2026-10-25 | 54539952 | v1.5.3 PGO 2470b041 | v1.5.3 | 1,708 |\n")
def paired_block(pp, s_v153, s_gen, half_name):
    L.append(f"The run measures both policies on the same binary in one task per input, so the policy comparison is free of day and node effects (the comparison in `RUNS.md`). The comparison with the v1.5.3 run of 2026-10-25 carries the day effect of that run and is given for coverage.\n")
    L.append("| Comparison | Verified | Reference verified | Lost | Gained | Flagged wrong | Mean ratio | Median ratio |\n|---|---:|---:|---|---|---|---:|---:|")
    L.append(f"| general policy against the v1.5.3 policy, same binary | {pp['verified']} | {pp['baseline_verified']} | {', '.join(pp['lost']) or 'none'} | {', '.join(pp['gained']) or 'none'} | {', '.join(pp['flagged_wrong']) or 'none'} | {f2(pp['mean_ratio'])} | {f2(pp['median_ratio'])} |")
    for s, lab in ((s_v153, "v1.5.3 policy on the v1.5.4 binary against the v1.5.3 run of 2026-10-25"), (s_gen, "general policy on the v1.5.4 binary against the v1.5.3 run of 2026-10-25")):
        L.append(f"| {lab} | {s['verified']} | {s['baseline_verified']} | {', '.join(s['lost']) or 'none'} | {', '.join(s['gained']) or 'none'} | {', '.join(s['flagged_wrong']) or 'none'} | {f2(s['mean_ratio'])} | {f2(s['median_ratio'])} |")
    L.append("")


L.append("## Design half (run 9)\n")
paired_block(policy_pairs["design_run9_general_vs_v153_policy"], summary["design_v153_policy_vs_v153_baseline"], summary["design_general_policy_vs_v153_baseline"], "design")
L.append("Against the 2026-10-25 run the general policy misses `ore_ont_10425`, `ore_ont_15655`, `ore_ont_4410`, `ore_ont_4572` and `ore_ont_5368`, the five inputs of amendment 2 (v1.5.3 answered them after silently discarding data-property assertions; v1.5.4 publishes the drop), and verifies `ore_ont_16666` and `ore_ont_2792`, which v1.5.3 did not. The v1.5.3 policy on the v1.5.4 binary also misses `ore_ont_1555`, `ore_ont_1672` and `ore_ont_6934`, which the general policy answers.\n")
L.append("## Held-out half\n")
L.append("### Paired run (both policies on the v1.5.4 PGO binary)\n")
paired_block(policy_pairs["held_out_paired_general_vs_v153_policy"], summary["held_out_v153_policy_vs_v153_baseline"], summary["held_out_general_policy_vs_v153_baseline"], "held-out")
L.append("`ore_ont_3794` is flagged under both policies and was unverified in v1.5.3 as well: KM's taxonomy is identical in both releases and contains ten subsumptions Konclude does not derive; HermiT entails all ten (`held-out-3794-adjudication/`). It is a reference incompleteness, not a KM defect.\n")
L.append("### Protocol run (G8)\n")
s = summary["g8_protocol_vs_v153_baseline_20261025"]
L.append(f"The v1.5.4 protocol run verifies {s['verified']} inputs against {s['baseline_verified']} in the v1.5.3 run of 2026-10-25. Lost: {', '.join(s['lost'])} (both amendment cases: 10874 under amendment 3, 7610 under amendment 2). Against that baseline the mean ratio is {f2(s['mean_ratio'])} and the median {f2(s['median_ratio'])}; because node and day effects are large, the v1.5.3 binary was rerun the same evening under the identical protocol. On the {decomp['common']} inputs verified in all four held-out runs:\n")
L.append("| Comparison | mean ratio | median ratio |\n|---|---:|---:|")
for k, lab in (("total_g8_vs_sameday", "v1.5.4 protocol run vs v1.5.3 same-day run (G8)"), ("engine_only_v154_binary_v153_policy_vs_v153_binary", "engine only: v1.5.4 binary under the v1.5.3 policy vs v1.5.3 binary"), ("policy_only_general_vs_v153_policy_same_binary", "policy only: general vs v1.5.3 policy, same binary"), ("noise_floor_same_binary_and_policy_paired_vs_protocol", "noise floor: the same binary and policy in two runs (paired general vs protocol)")):
    r = decomp[k]
    L.append(f"| {lab} | {f2(r['mean_ratio'])} | {f2(r['median_ratio'])} |")
t = decomp["total_g8_vs_sameday"]
L.append(f"\nG8 verdict: no coverage loss (under amendments 2 and 3), median {f2(t['median_ratio'])} within the 1.10 bound, mean {f2(t['mean_ratio'])} outside it (wall-time sums {t['sum_candidate_s']:.1f} s against {t['sum_baseline_s']:.1f} s; the bound allows {bound:.1f} s, excess {excess:.1f} s). The excess is the cost of two soundness fixes (checked subset blocking on `ore_ont_205`; data-property assertions carried into the rules-consistency worker on `ore_ont_7278` and `ore_ont_3726`) and of the general policy's `certified_nominals` choice on six former Konclude-bridge inputs. The release decision on the mean is recorded in `docs/V1.5.4-STATUS.md`.\n")
L.append("Largest wall-time increases, v1.5.4 protocol run against the same-day v1.5.3 run:\n")
L.append("| Input | v1.5.3 same day (s) | v1.5.4 (s) | delta (s) |\n|---|---:|---:|---:|")
for r in top:
    L.append(f"| {r['ontology']} | {r['v153_sameday_s']:.1f} | {r['v154_s']:.1f} | {r['delta_s']:+.1f} |")
kc = konclude_clause
L.append(f"\nKonclude clause: v1.5.4 verifies {kc['v154_verified_held_out']} held-out inputs against {kc['konclude_solved_held_out']} solved by the Konclude run of 2026-10-04; on the {kc['common']} common inputs the mean is {kc['mean_v154_s']:.3f} s (KM) against {kc['mean_konclude_s']:.3f} s (Konclude) and the median {kc['median_v154_s']:.3f} s against {kc['median_konclude_s']:.3f} s. The Konclude run is from another day and other nodes, so the speed clause is not judged.\n")
L.append("## Per-input results, held-out half\n")
L.append("Wall seconds; `v` marks a verified answer, `-` no verified answer in the budget. Columns: v1.5.3 run of 2026-10-25, v1.5.3 same-day protocol run, v1.5.4 protocol run, v1.5.4 paired run under the v1.5.3 policy, v1.5.4 paired run under the general policy.\n")
L.append("| Input | v1.5.3 10-25 | v1.5.3 same day | v1.5.4 protocol | v1.5.4 paired v153 | v1.5.4 paired general |\n|---|---:|---:|---:|---:|---:|")


def cell(d, o):
    r = d.get(o)
    if r is None:
        return "n/a"
    return f"{r['wall_s']:.2f} {'v' if r.get('verified_solved') else '-'}"


for o in sorted(held, key=lambda x: int(x.split("_")[-1])):
    L.append(f"| {o} | {cell(base_h, o)} | {cell(g8s, o)} | {cell(g8n, o)} | {cell(ph_v153, o)} | {cell(ph_gen, o)} |")
L.append("\n## Per-input results, design half (run 9)\n")
L.append("| Input | v1.5.3 10-25 | v1.5.4 v153 policy | v1.5.4 general policy |\n|---|---:|---:|---:|")
for o in sorted(design, key=lambda x: int(x.split("_")[-1])):
    L.append(f"| {o} | {cell(base_d, o)} | {cell(pd_v153, o)} | {cell(pd_gen, o)} |")
bench = "\n".join(L) + "\n"
open(ASSETS + "/BENCHMARKS.md", "w").write(bench)

completion["generated_artifact_hashes"] = {
    "km-v1.5.4-linux-x86_64": sha(binary),
    "kobayashi-marust-protege-1.5.4.jar": sha(jar),
    "km-v1.5.4-certified-source.tar.gz": sha(source),
    "BENCHMARKS.md": sha(ASSETS + "/BENCHMARKS.md"),
}
json.dump(completion, open(ASSETS + "/build-completion.json", "w"), indent=1, sort_keys=False)

names = ["km-v1.5.4-linux-x86_64", "km-v1.5.4-certified-source.tar.gz", "build-completion.json", "BENCHMARKS.md", "kobayashi-marust-protege-1.5.4.jar"]
with open(ASSETS + "/SHA256SUMS", "w") as f:
    for n in names:
        f.write(f"{sha(ASSETS + '/' + n)}  {n}\n")
manifest = {"schema": "km-release-assets-v1", "tag": TAG, "commit": COMMIT, "assets": [
    {"name": n, "sha256": sha(ASSETS + "/" + n), "size": os.path.getsize(ASSETS + "/" + n)} for n in names + ["SHA256SUMS"]]}
json.dump(manifest, open(ASSETS + "/manifest.json", "w"), indent=2)
for k, v in list(summary.items()) + list(policy_pairs.items()):
    print(k, v["verified"], v["baseline_verified"], "lost", v["lost"], "gained", v["gained"], "wrong", v["flagged_wrong"], round(v["mean_ratio"], 3), round(v["median_ratio"], 3))
print(json.dumps({k: (round(v["mean_ratio"], 4), round(v["median_ratio"], 4)) for k, v in decomp.items() if k != "common"}))
print("bound", round(bound, 1), "excess", round(excess, 1))
print(json.dumps(konclude_clause, indent=1))
