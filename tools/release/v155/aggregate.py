#!/usr/bin/env python3
"""Aggregate the v1.5.5 release measurement into BENCHMARKS.md and build-completion.json.

The G8 arithmetic is copied from `.work/v154-release-cert/ctl/build-assets.py`
(the v1.5.4 asset builder): `ratios()` (ratio of the means and ratio of the
medians of wall seconds over a common set of verified inputs), `summarise()`
(coverage, lost, gained, flagged wrong), the four-run decomposition when a
paired run is given, and `konclude_solved()` for the Konclude clause. Added
for v1.5.5: the S1 verdict without any performance exception, the same-day
Konclude records (from `run_konclude.py`), and the zero-wrong-answer check on
the full regression pool against the pinned references
(`adjudications.json` excuses an answer only by its exact fingerprint).

Every number is computed from the chunk records; nothing is typed in.

Release mode (v1.5.5, after `fetch.sh` copied the chunk files):
  aggregate.py --data D --rc heldout-rc-<job> --v153 heldout-v153-<job> \
      --konclude heldout-konclude-<job> --pool pool-rc-<job> --out ASSETS \
      --tag v1.5.5 --commit <sha> --pgo-root <pgo dir> [--cert-root <gates ctl dir>]

Check mode (recompute the v1.5.4 numbers from the v1.5.4 records):
  aggregate.py --reproduce-v154 --out <scratch dir>
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import statistics
import sys

HERE = Path(__file__).resolve().parent
W = Path("/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work")
V154_DATA = W / "v154-release-cert/data"
BOUND = 1.10


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def load_run(d):
    """Chunk directory -> (outcomes, {chunk: sha256}, meta, incomplete chunks)."""
    d = Path(d)
    if (d / "chunks").is_dir():
        d = d / "chunks"
    outcomes, chunk_hashes, meta, incomplete = [], {}, {}, []
    for f in sorted(os.listdir(d), key=lambda x: (len(x), x)):
        if not f.endswith(".json"):
            continue
        p = d / f
        chunk_hashes[f] = sha(p)
        x = json.load(open(p))
        if x.get("status") != "complete":
            incomplete.append(f)
        for k in ("status", "runner_sha256", "inventory_sha256", "manifest_sha256", "half", "policies", "binary_sha256", "label"):
            if k in x:
                meta.setdefault(k, set()).add(json.dumps(x[k]) if isinstance(x[k], (list, dict)) else x[k])
        outcomes.extend(x["outcomes"])
    meta = {k: sorted(v) for k, v in meta.items()}
    return outcomes, chunk_hashes, meta, incomplete


def by_ont(outcomes, policy=None):
    d = {r["ontology"]: r for r in outcomes if policy is None or r.get("policy") == policy}
    assert len(d) == len([r for r in outcomes if policy is None or r.get("policy") == policy]), "duplicate outcome rows"
    return d


def ver(d):
    return {o for o, r in d.items() if r.get("verified_solved")}


def is_wrong(r):
    """run_paired.py's definition, recomputed from the comparisons so records of
    runners without a `wrong` field are judged identically."""
    c = r.get("comparisons", {}).values()
    return any(x.get("agreement") is False for x in c) and not any(x.get("agreement") is True for x in c)


# ---- build-assets.py arithmetic (unchanged)
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


def summarise(cand, base, half_set, label):
    a, b = ver(cand) & half_set, ver(base) & half_set
    common = sorted(a & b)
    wrong = sorted(o for o, r in cand.items() if is_wrong(r) and o in half_set)
    s = {"label": label, "inputs": len(half_set), "outcomes": len([o for o in cand if o in half_set]),
         "verified": len(a), "baseline_verified": len(b), "lost": sorted(b - a), "gained": sorted(a - b),
         "flagged_wrong": wrong}
    s.update(ratios(cand, base, common))
    return s


def konclude_solved(konc, base):
    """build-assets.py: Konclude counts as solved when its run executed with exit 0
    and, wherever v1.5.3's answer is verified, agrees with it (the v1.5.3 baseline
    records the comparison against the 2026-10-04 Konclude answer). For a same-day
    run the base comparison carries over only when the same-day answer equals the
    2026-10-04 answer; a same-day answer that agrees with HermiT, Openllet or JFact
    counts in any case."""
    solved = set()
    for o, rec in konc.items():
        executed = rec.get("status") == "executed_unvalidated" and rec.get("exit_code") == 0
        if not executed:
            continue
        if rec.get("verified_solved"):
            solved.add(o)
            continue
        if rec.get("same_answer_as_20261004") is False or rec.get("audit_status") == "audit_error":
            continue
        agree = base.get(o, {}).get("comparisons", {}).get("konclude", {}).get("status")
        if agree == "agreement" or not base.get(o, {}).get("verified_solved"):
            solved.add(o)
    return solved


def konclude_records_from_chunks(outcomes):
    return {r["ontology"]: dict(r, status=r.get("measurement_status")) for r in outcomes}


def apply_adjudications(wrong, cand, adj, legacy):
    excused, remaining = [], []
    table = {a["ontology"]: a for a in adj["adjudications"]}
    for o in wrong:
        a = table.get(o)
        fp = cand[o].get("relation_sha256")
        if a and (fp == a["km_relation_sha256"] or (legacy and fp is None)):
            excused.append({"ontology": o, "verdict": a["verdict"], "evidence": a["evidence"],
                            "fingerprint_checked": fp is not None})
        else:
            remaining.append(o)
    return excused, remaining


def f2(x):
    return f"{x:.3f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--reproduce-v154", action="store_true")
    ap.add_argument("--data", type=Path)
    ap.add_argument("--rc")
    ap.add_argument("--v153")
    ap.add_argument("--konclude")
    ap.add_argument("--pool")
    ap.add_argument("--paired", help="optional paired run (run_paired.py records with policy v153/general)")
    ap.add_argument("--baseline", type=Path, default=V154_DATA / "combined-v150-54539952", help="v1.5.3 PGO run of 2026-10-25 (1,920 rows)")
    ap.add_argument("--split", type=Path, default=V154_DATA / "split.json")
    ap.add_argument("--konclude-1004", type=Path, default=V154_DATA / "konclude-20261004-records.json")
    ap.add_argument("--adjudications", type=Path, default=HERE / "adjudications.json")
    ap.add_argument("--ibex-root", default="/ibex/scratch/projects/c2014/hohndor/km/v155-release-YYYYMMDD")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--tag", default="v1.5.5")
    ap.add_argument("--version", default="1.5.5")
    ap.add_argument("--commit", default="")
    ap.add_argument("--pgo-root", type=Path)
    ap.add_argument("--cert-root", type=Path, help="gate control dir with gate-work/*-gate-receipt.json, full-rust-execution/receipt.json, pins.json, java receipt")
    a = ap.parse_args()

    legacy = False
    if a.reproduce_v154:
        legacy = True
        a.data = V154_DATA
        a.rc, a.v153, a.paired, a.konclude, a.pool = "g8-v154-54796888", "g8-v153-sameday-54801090", "paired-held_out-54796887", None, None
        a.tag, a.version, a.commit = "v1.5.4", "1.5.4", "80c8f82aea9c99db89b7fa3885cc2c63010aa7f6"
    a.out.mkdir(parents=True, exist_ok=True)

    split = json.load(open(a.split))
    design, held = set(split["design"]), set(split["held_out"])
    base_out, base_hash, base_meta, base_inc = load_run(a.baseline)
    base_all = by_ont(base_out)
    base_h = {o: r for o, r in base_all.items() if o in held}
    admitted = {o for o, r in base_all.items() if r.get("input_admission") == "checks_passed"}

    runs = {}
    for key in ("rc", "v153", "konclude", "pool", "paired"):
        name = getattr(a, key)
        if name:
            runs[key] = (name,) + load_run(a.data / name)
    rc = {o: r for o, r in by_ont(runs["rc"][1]).items() if o in held}
    sd = {o: r for o, r in by_ont(runs["v153"][1]).items() if o in held}

    summary = {
        "g8_protocol_vs_v153_sameday": summarise(rc, sd, held, f"held-out protocol run of the {a.tag} candidate against the same-day v1.5.3 protocol run"),
        "g8_protocol_vs_v153_baseline_20261025": summarise(rc, base_h, held, f"held-out protocol run of the {a.tag} candidate against the v1.5.3 PGO run of 2026-10-25"),
        "v153_sameday_vs_v153_baseline_20261025": summarise(sd, base_h, held, "same-day v1.5.3 run against the v1.5.3 PGO run of 2026-10-25 (day and node effect)"),
    }
    two = sorted(ver(rc) & ver(sd))
    decomp = {"common": len(two), "total_g8_vs_sameday": ratios(rc, sd, two)}
    if "paired" in runs:
        ph_v153 = by_ont(runs["paired"][1], "v153")
        ph_gen = by_ont(runs["paired"][1], "general")
        four = sorted(ver(rc) & ver(sd) & ver(ph_v153) & ver(ph_gen))
        decomp_four = {
            "common": len(four),
            "total_g8_vs_sameday": ratios(rc, sd, four),
            "engine_only_candidate_binary_v153_policy_vs_v153_binary": ratios(ph_v153, sd, four),
            "policy_only_general_vs_v153_policy_same_binary": ratios(ph_gen, ph_v153, four),
            "noise_floor_same_binary_and_policy_paired_vs_protocol": ratios(ph_gen, rc, four),
        }
    else:
        decomp_four = None
    of_record = decomp_four if (decomp_four and legacy) else decomp
    t = of_record["total_g8_vs_sameday"]
    allowed = BOUND * t["sum_baseline_s"]
    common_rec = four if (decomp_four and legacy) else two
    deltas = sorted(((rc[o]["wall_s"] - sd[o]["wall_s"], o) for o in common_rec), reverse=True)
    top = [{"ontology": o, "v153_sameday_s": round(sd[o]["wall_s"], 2), "candidate_s": round(rc[o]["wall_s"], 2), "delta_s": round(d, 2)} for d, o in deltas[:15]]
    bottom = [{"ontology": o, "v153_sameday_s": round(sd[o]["wall_s"], 2), "candidate_s": round(rc[o]["wall_s"], 2), "delta_s": round(d, 2)} for d, o in deltas[-10:]]

    # ---- Konclude clause
    if "konclude" in runs:
        konc = konclude_records_from_chunks(runs["konclude"][1])
        konc_label = f"same-day Konclude run {runs['konclude'][0]}"
        same_day = True
    else:
        konc = json.load(open(a.konclude_1004))
        konc_label = "Konclude run of 2026-10-04 (classification-konclude-53201252)"
        same_day = False
    ks = konclude_solved(konc, base_all)
    kh = ks & held
    ck = sorted(ver(rc) & kh)
    kc = {
        "konclude_run": konc_label,
        "same_day": same_day,
        "konclude_solved_held_out": len(kh),
        "candidate_verified_held_out": len(ver(rc)),
        "common": len(ck),
        "mean_candidate_s": statistics.mean(rc[o]["wall_s"] for o in ck),
        "mean_konclude_s": statistics.mean(konc[o]["wall_s"] for o in ck),
        "median_candidate_s": statistics.median(rc[o]["wall_s"] for o in ck),
        "median_konclude_s": statistics.median(konc[o]["wall_s"] for o in ck),
    }
    if same_day:
        kh_rows = [konc[o] for o in held if o in konc]
        kc["konclude_answers_identical_to_20261004"] = sum(1 for r in kh_rows if r.get("same_answer_as_20261004"))
        kc["konclude_answers_differing_from_20261004"] = sorted(r["ontology"] for r in kh_rows if r.get("same_answer_as_20261004") is False)
        kc["konclude_flagged_wrong_held_out"] = sorted(r["ontology"] for r in kh_rows if r.get("wrong"))
        kc["konclude_incomplete_chunks"] = runs["konclude"][4]
    kc_more = kc["candidate_verified_held_out"] > kc["konclude_solved_held_out"]
    kc_faster = kc["mean_candidate_s"] < kc["mean_konclude_s"] and kc["median_candidate_s"] < kc["median_konclude_s"]

    # ---- correctness: held-out and pool
    adj = json.load(open(a.adjudications))
    held_wrong = summary["g8_protocol_vs_v153_sameday"]["flagged_wrong"]
    held_excused, held_remaining = apply_adjudications(held_wrong, rc, adj, legacy)
    pool = None
    if "pool" in runs:
        pc = by_ont(runs["pool"][1])
        pw = sorted(o for o, r in pc.items() if o in admitted and is_wrong(r))
        p_excused, p_remaining = apply_adjudications(pw, pc, adj, legacy)
        base_ver = ver(base_all) & admitted
        pv = ver(pc) & admitted
        pool = {
            "run": runs["pool"][0],
            "rows": len(pc),
            "admitted_inputs": len(admitted),
            "admitted_outcomes": len([o for o in pc if o in admitted]),
            "incomplete_chunks": runs["pool"][4],
            "verified": len(pv),
            "v153_20261025_verified": len(base_ver),
            "lost_vs_v153_20261025": sorted(base_ver - pv),
            "gained_vs_v153_20261025": sorted(pv - base_ver),
            "flagged_wrong": pw,
            "excused_by_adjudication": p_excused,
            "wrong_answers": p_remaining,
            "audit_errors": sorted(o for o, r in pc.items() if r.get("audit_status") == "audit_error"),
            "invalid_input_was_not_refused": sorted(o for o, r in pc.items() if r.get("audit_status") == "invalid_input_was_not_refused"),
            "status_counts": {s: sum(1 for r in pc.values() if r.get("measurement_status") == s) for s in sorted({r.get("measurement_status") for r in pc.values()})},
            "zero_wrong": not p_remaining and not runs["pool"][4],
        }

    sameday = summary["g8_protocol_vs_v153_sameday"]
    b1025 = summary["g8_protocol_vs_v153_baseline_20261025"]
    s1 = {
        "contract": "docs/V1.5.5-ACCEPTANCE.md S1 (the original G8 bound of docs/V1.5.4-ACCEPTANCE.md; no amendment allowed)",
        "no_loss": {"status": "met" if sameday["verified"] >= sameday["baseline_verified"] and b1025["verified"] >= b1025["baseline_verified"] else "NOT_MET",
                    "verified_candidate": sameday["verified"], "verified_v153_sameday": sameday["baseline_verified"],
                    "verified_v153_20261025": b1025["baseline_verified"], "lost_vs_sameday": sameday["lost"], "lost_vs_20261025": b1025["lost"],
                    "rule": "verified inputs at least those of the same-day v1.5.3 run and of the 2026-10-25 v1.5.3 run"},
        "mean": {"status": "met" if t["mean_ratio"] <= BOUND else "NOT_MET", "ratio_vs_sameday": t["mean_ratio"], "bound": BOUND,
                 "sum_candidate_s": t["sum_candidate_s"], "sum_v153_sameday_s": t["sum_baseline_s"], "allowed_sum_s": round(allowed, 3),
                 "excess_s": round(t["sum_candidate_s"] - allowed, 3), "common": of_record["common"]},
        "median": {"status": "met" if t["median_ratio"] <= BOUND else "NOT_MET", "ratio_vs_sameday": t["median_ratio"], "bound": BOUND},
        # The Konclude part of S1 as the maintainer's goal states it: more verified inputs than Konclude on a
        # same-day run. The mean and median against Konclude are reported, not gated: on the held-out half the
        # v1.5.3 baseline itself is slower than Konclude in mean (same-day v1.5.3 4.03 s against the 2026-10-04
        # Konclude run's 2.59 s on 535 common inputs, median 0.235 s against 0.241 s), so that clause of the
        # original G8 wording cannot separate a regression from the baseline (docs/V1.5.5-ACCEPTANCE.md S1).
        "konclude": {"status": ("met" if kc_more else "NOT_MET") if same_day else "not_judged_no_same_day_konclude_run",
                     "rule": "more verified inputs than the same-day Konclude run; mean and median reported",
                     "more_verified": kc_more, "faster_mean_and_median": kc_faster, **kc},
    }
    s1["status"] = "met" if all(s1[k]["status"] == "met" for k in ("no_loss", "mean", "median", "konclude")) else "NOT_MET"
    c1_bench = {"held_out_flagged_wrong": held_wrong, "held_out_excused_by_adjudication": held_excused, "held_out_wrong_answers": held_remaining,
                "pool": pool if pool else {"status": "not_run"}}
    c1_bench["status"] = "met" if (not held_remaining and pool and pool["zero_wrong"]) else ("NOT_MET" if held_remaining or (pool and not pool["zero_wrong"]) else "pending_pool_run")

    # ---- receipts (optional until the gates and the PGO build of the tag exist)
    def opt_json(p):
        return json.load(open(p)) if p and Path(p).is_file() else {"status": "pending", "expected_path": str(p) if p else None}
    pgo = {}
    if a.pgo_root:
        pgo = {"pipeline": str(HERE / "pgo_build.py"), "native_build_receipt": opt_json(a.pgo_root / "native-build-receipt.json"),
               "released_binary_build": opt_json(a.pgo_root / "pgo-use-bfd-build.json"), "merge_receipt": opt_json(a.pgo_root / "merge-receipt.json"),
               "training_receipt": opt_json(a.pgo_root / "training-receipt.json"), "build_warning_audit": opt_json(a.pgo_root / "build-warning-audit.json"),
               "linker_wrapper": {"path": str(HERE / "cc-wrapper.sh"), "sha256": sha(HERE / "cc-wrapper.sh")}}
    gates, rust, java, pins, checker_step, manifests = {}, None, None, None, None, {}
    if a.cert_root:
        gates = {g: opt_json(a.cert_root / f"gate-work/{g}-gate-receipt.json") for g in ("elc", "routing", "ht", "cb", "rules")}
        rust = opt_json(a.cert_root / "full-rust-execution/receipt.json")
        java = opt_json(a.cert_root / "java-receipt.json")
        pins = opt_json(a.cert_root / "pins.json")
        checker_step = opt_json(a.cert_root / "checker-step/receipt.json")
        if (a.cert_root / "complete-source-manifest.json").is_file():
            manifests["certification_complete_source_manifest"] = {"path": str(a.cert_root / "complete-source-manifest.json"), "sha256": sha(a.cert_root / "complete-source-manifest.json")}
    if a.pgo_root and (a.pgo_root / "source-manifest.json").is_file():
        manifests["pgo_pipeline_source_manifest"] = {"path": str(a.pgo_root / "source-manifest.json"), "sha256": sha(a.pgo_root / "source-manifest.json")}
    l1_gates = {"status": "met" if gates and all(isinstance(g, dict) and g.get("status") == "passed" for g in gates.values()) and checker_step and checker_step.get("status") == "passed" else "pending",
                "lean_gates": {g: (r.get("status") if isinstance(r, dict) else None) for g, r in gates.items()},
                "checkers_on_suite_and_checker_tests": checker_step.get("status") if checker_step else None}
    r1 = {"status": "met" if l1_gates["status"] == "met" and rust and rust.get("status", "").startswith("passed") and java and java.get("tests", {}).get("failures") == 0 else "pending",
          "rust": rust.get("status") if rust else None, "rust_counts": rust.get("counts") if rust else None,
          "java_tests": java.get("tests") if java else None}

    run_desc = {k: {"local_dir": str(a.data / v[0]), "ibex_dir": f"{a.ibex_root}/{v[0]}/chunks", "slurm_array": v[0].rsplit("-", 1)[-1],
                    "chunks": len(v[2]), "chunk_sha256": v[2], "meta": v[3], "incomplete_chunks": v[4]} for k, v in runs.items()}
    run_desc["v153_baseline_20261025"] = {"local_dir": str(a.baseline), "slurm_array": "54539952", "chunks": len(base_hash), "chunk_sha256": base_hash, "meta": base_meta}

    completion = {
        "schema": f"km-v{a.version.replace('.', '')}-release-completion-v1",
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "tag": a.tag,
        "version": a.version,
        "release_commit": a.commit,
        "status": "draft: generated by tools/release/v155/aggregate.py; complete only when S1, C1, L1 and the gates from the tag are met",
        "source_manifests": manifests,
        "pins": pins,
        "certification": gates,
        "checker_step": checker_step,
        "rust_ci_receipt": rust,
        "java_receipt": java,
        "pgo": pgo,
        "benchmark": {
            "protocol": "v1.5.3 protocol: one core, 240 s, 20 GiB, scoped watchdog, gold-6248 nodes; runners tools/release/v155/ibex/run_release.py and run_konclude.py with the v1.5.4 G8 run's protocol modules",
            "runs": run_desc,
            "split_sha256": sha(a.split),
            "konclude_20261004_records_sha256": sha(a.konclude_1004),
            "adjudications_sha256": sha(a.adjudications),
            "summary": summary,
            "g8_decomposition": decomp,
            "g8_decomposition_four_run": decomp_four,
            "g8_of_record": "four_run" if (decomp_four and legacy) else "two_run",
            "g8_largest_deltas": top,
            "g8_largest_savings": bottom,
        },
        "acceptance": {"S1_speed": s1, "C1_benchmark_correctness": c1_bench, "L1_gates_and_checkers": l1_gates, "R1_release_gates": r1},
        "documents": ["docs/RELEASE-1.5.5-PROCEDURE.md", "docs/V1.5.5-ACCEPTANCE.md", "docs/V1.5.5-STATUS.md"],
    }
    # ---- BENCHMARKS.md draft
    L = [f"# KM {a.tag} benchmark results (draft)\n"]
    L.append(f"Commit `{a.commit or 'not set'}`. Generated by `tools/release/v155/aggregate.py` from the chunk records; every number below is computed from them. All runs on Ibex gold-6248 nodes, one core per input, 240 s, 20 GiB, scoped watchdog.\n")
    L.append("| Run | Slurm array | Inputs (outcomes) | Incomplete chunks |\n|---|---|---:|---|")
    for k, v in runs.items():
        L.append(f"| {k} (`{v[0]}`) | {v[0].rsplit('-', 1)[-1]} | {len(v[1])} | {', '.join(v[4]) or 'none'} |")
    L.append(f"| v1.5.3 2026-10-25 baseline | 54539952 | {len(base_out)} | {', '.join(base_inc) or 'none'} |\n")
    L.append("## S1: held-out half against v1.5.3\n")
    L.append("| Comparison | Verified | Reference verified | Lost | Gained | Flagged wrong | Mean ratio | Median ratio |\n|---|---:|---:|---|---|---|---:|---:|")
    for k, s in summary.items():
        L.append(f"| {s['label']} | {s['verified']} | {s['baseline_verified']} | {', '.join(s['lost']) or 'none'} | {', '.join(s['gained']) or 'none'} | {', '.join(s['flagged_wrong']) or 'none'} | {f2(s['mean_ratio'])} | {f2(s['median_ratio'])} |")
    L.append("")
    L.append(f"G8 of record: {of_record['common']} inputs verified in {'all four runs' if (decomp_four and legacy) else 'both protocol runs'}; mean ratio {f2(t['mean_ratio'])}, median ratio {f2(t['median_ratio'])} (bound {BOUND}); wall-time sums {t['sum_candidate_s']:.1f} s against {t['sum_baseline_s']:.1f} s, allowed {allowed:.1f} s, excess {t['sum_candidate_s'] - allowed:+.1f} s.\n")
    if decomp_four:
        L.append("| Four-run decomposition | mean ratio | median ratio |\n|---|---:|---:|")
        for k, r in decomp_four.items():
            if k != "common":
                L.append(f"| {k} | {f2(r['mean_ratio'])} | {f2(r['median_ratio'])} |")
        L.append(f"\nTwo-run common set ({decomp['common']} inputs): mean {f2(decomp['total_g8_vs_sameday']['mean_ratio'])}, median {f2(decomp['total_g8_vs_sameday']['median_ratio'])}.\n")
    L.append("| S1 clause | Status | Value |\n|---|---|---|")
    L.append(f"| no loss | {s1['no_loss']['status']} | {s1['no_loss']['verified_candidate']} verified against {s1['no_loss']['verified_v153_sameday']} (same day) and {s1['no_loss']['verified_v153_20261025']} (2026-10-25) |")
    L.append(f"| mean ≤ {BOUND} | {s1['mean']['status']} | {f2(t['mean_ratio'])} |")
    L.append(f"| median ≤ {BOUND} | {s1['median']['status']} | {f2(t['median_ratio'])} |")
    L.append(f"| Konclude | {s1['konclude']['status']} | {kc['candidate_verified_held_out']} verified against {kc['konclude_solved_held_out']} ({konc_label}); on {kc['common']} common inputs mean {kc['mean_candidate_s']:.3f} s against {kc['mean_konclude_s']:.3f} s, median {kc['median_candidate_s']:.3f} s against {kc['median_konclude_s']:.3f} s |")
    L.append(f"\nS1 overall: **{s1['status']}**.\n")
    L.append("Largest wall-time increases against the same-day v1.5.3 run:\n")
    L.append("| Input | v1.5.3 same day (s) | candidate (s) | delta (s) |\n|---|---:|---:|---:|")
    for r in top:
        L.append(f"| {r['ontology']} | {r['v153_sameday_s']:.1f} | {r['candidate_s']:.1f} | {r['delta_s']:+.1f} |")
    L.append("\n## C1: wrong answers\n")
    L.append(f"Held-out protocol run: flagged {', '.join(held_wrong) or 'none'}; excused by adjudication {', '.join(x['ontology'] for x in held_excused) or 'none'}; wrong {', '.join(held_remaining) or 'none'}.\n")
    if pool:
        L.append(f"Full regression pool (`{pool['run']}`): {pool['admitted_outcomes']} of {pool['admitted_inputs']} admitted inputs measured, {pool['verified']} verified (v1.5.3 2026-10-25: {pool['v153_20261025_verified']}); lost {', '.join(pool['lost_vs_v153_20261025']) or 'none'}; gained {', '.join(pool['gained_vs_v153_20261025']) or 'none'}. Flagged wrong: {', '.join(pool['flagged_wrong']) or 'none'}; excused: {', '.join(x['ontology'] for x in pool['excused_by_adjudication']) or 'none'}; **wrong answers: {', '.join(pool['wrong_answers']) or 'none'}**. Audit errors: {', '.join(pool['audit_errors']) or 'none'}. Invalid inputs answered instead of refused: {len(pool['invalid_input_was_not_refused'])}. Status counts: {pool['status_counts']}.\n")
    else:
        L.append("Full regression pool: not run.\n")
    L.append("## Per-input results, held-out half\n")
    L.append("Wall seconds; `v` verified, `-` no verified answer in the budget.\n")
    L.append("| Input | v1.5.3 10-25 | v1.5.3 same day | candidate | Konclude |\n|---|---:|---:|---:|---:|")

    def cell(d, o, solved=None):
        r = d.get(o)
        if r is None or r.get("wall_s") is None:
            return "n/a"
        ok = (o in solved) if solved is not None else r.get("verified_solved")
        return f"{r['wall_s']:.2f} {'v' if ok else '-'}"
    for o in sorted(held, key=lambda x: int(x.split("_")[-1])):
        L.append(f"| {o} | {cell(base_h, o)} | {cell(sd, o)} | {cell(rc, o)} | {cell(konc, o, ks)} |")
    (a.out / "BENCHMARKS.md").write_text("\n".join(L) + "\n")

    # ---- release assets present in --out: hash them (v1.5.4 layout)
    names = [f"km-v{a.version}-linux-x86_64", f"km-v{a.version}-certified-source.tar.gz", "BENCHMARKS.md", f"kobayashi-marust-protege-{a.version}.jar"]
    present = [n for n in names if (a.out / n).is_file()]
    completion["generated_artifact_hashes"] = {n: sha(a.out / n) for n in present}
    if pgo and (a.out / names[0]).is_file():
        nb = pgo["native_build_receipt"]
        assert isinstance(nb, dict) and sha(a.out / names[0]) == nb.get("binary_sha256"), "asset binary is not the receipted PGO binary"
    json.dump(completion, open(a.out / "build-completion.json", "w"), indent=1)
    if len(present) == len(names):
        order = [names[0], names[1], "build-completion.json", "BENCHMARKS.md", names[3]]
        with open(a.out / "SHA256SUMS", "w") as f:
            for n in order:
                f.write(f"{sha(a.out / n)}  {n}\n")
        manifest = {"schema": "km-release-assets-v1", "tag": a.tag, "commit": a.commit,
                    "assets": [{"name": n, "sha256": sha(a.out / n), "size": os.path.getsize(a.out / n)} for n in order + ["SHA256SUMS"]]}
        json.dump(manifest, open(a.out / "manifest.json", "w"), indent=2)

    print(json.dumps({"S1": s1["status"], "no_loss": s1["no_loss"]["status"], "common": of_record["common"],
                      "mean_ratio": round(t["mean_ratio"], 4), "median_ratio": round(t["median_ratio"], 4),
                      "two_run": (decomp["common"], round(decomp["total_g8_vs_sameday"]["mean_ratio"], 4), round(decomp["total_g8_vs_sameday"]["median_ratio"], 4)),
                      "four_run": {k: (round(v["mean_ratio"], 4), round(v["median_ratio"], 4)) for k, v in (decomp_four or {}).items() if k != "common"},
                      "konclude": {k: kc[k] for k in ("konclude_solved_held_out", "candidate_verified_held_out", "common", "mean_candidate_s", "mean_konclude_s", "median_candidate_s", "median_konclude_s")},
                      "held_wrong": held_wrong, "held_excused": [x["ontology"] for x in held_excused],
                      "pool": {k: pool[k] for k in ("verified", "flagged_wrong", "wrong_answers", "audit_errors", "zero_wrong")} if pool else None}, indent=1))


if __name__ == "__main__":
    main()
