#!/usr/bin/env python3
"""Aggregate the feature-ablation sweep.

Reads all *.jsonl under a results dir (one record per (arm,ont)), then prints:
  1. per-arm panel: ok / gold-clean / unsound / incomplete / both, and
     avg AND median wall + peak-mem over the set every arm solved cleanly
     (apples-to-apples) plus over the arm's own clean set.
  2. deltas vs `base`: recoveries (base-not-clean -> arm-clean) and
     regressions (base-clean -> arm-not-clean), with ont ids.
  3. per-ont oracle / portfolio: for each ont the best clean arm (min wall,
     then min mem); portfolio coverage; onts no arm solves cleanly.

A record is "clean" iff status=="ok" and cmp_gold_match is True.
Usage: ablate_agg.py <results_dir> [--base base] [--portfolio out.json]
"""
import glob
import json
import os
import statistics as st
import sys


def clean(r):
    return r.get("status") == "ok" and r.get("cmp_gold_match") is True


def disagree(r):
    if r.get("status") != "ok":
        return (False, False)
    uns = (r.get("cmp_unsound", 0) or 0) + (r.get("cmp_unsat_unsound", 0) or 0)
    inc = (r.get("cmp_incomplete", 0) or 0) + (r.get("cmp_unsat_incomplete", 0) or 0)
    return (uns > 0, inc > 0)


def med(xs):
    return st.median(xs) if xs else 0.0


def avg(xs):
    return sum(xs) / len(xs) if xs else 0.0


def main():
    d = sys.argv[1]
    base = "base"
    portfolio_out = None
    for i, a in enumerate(sys.argv):
        if a == "--base":
            base = sys.argv[i + 1]
        if a == "--portfolio":
            portfolio_out = sys.argv[i + 1]

    # data[arm][ont] = record
    data = {}
    for fp in glob.glob(os.path.join(d, "*.jsonl")):
        for ln in open(fp):
            ln = ln.strip()
            if not ln:
                continue
            try:
                r = json.loads(ln)
            except Exception:
                continue
            arm = r.get("arm", "?")
            ont = r.get("ont", "?")
            data.setdefault(arm, {})[ont] = r

    arms = sorted(data)
    all_onts = sorted({o for a in data for o in data[a]})
    nont = len(all_onts)

    # common-clean set: onts clean in EVERY arm (apples-to-apples timing)
    common_clean = [o for o in all_onts
                    if all(clean(data[a].get(o, {})) for a in arms)]

    print(f"# ablation: {len(arms)} arms, {nont} onts, "
          f"{len(common_clean)} clean-in-all (common timing set)\n")

    # ---- per-arm panel ----
    hdr = (f"{'arm':<14} {'ok':>4} {'clean':>5} {'unsnd':>5} {'incmp':>5} "
           f"{'both':>4} | {'cwall_avg':>9} {'cwall_med':>9} {'cmem_avg':>8} "
           f"{'cmem_med':>8} | {'owall_med':>9} {'omem_med':>8}")
    print(hdr)
    print("-" * len(hdr))
    panel = {}
    for a in arms:
        recs = data[a]
        ok = sum(1 for o in recs.values() if o.get("status") == "ok")
        cl = sum(1 for o in recs.values() if clean(o))
        uns = sum(1 for o in recs.values() if disagree(o)[0])
        inc = sum(1 for o in recs.values() if disagree(o)[1])
        both = sum(1 for o in recs.values() if all(disagree(o)))
        # common-set timing
        cw = [data[a][o]["wall_s"] for o in common_clean]
        cm = [data[a][o]["peak_mb"] for o in common_clean]
        # own clean set timing
        ow = [r["wall_s"] for r in recs.values() if clean(r)]
        om = [r["peak_mb"] for r in recs.values() if clean(r)]
        panel[a] = dict(ok=ok, clean=cl, unsound=uns, incomplete=inc, both=both)
        print(f"{a:<14} {ok:>4} {cl:>5} {uns:>5} {inc:>5} {both:>4} | "
              f"{avg(cw):>9.2f} {med(cw):>9.2f} {avg(cm):>8.0f} {med(cm):>8.0f} | "
              f"{med(ow):>9.2f} {med(om):>8.0f}")

    # ---- deltas vs base ----
    if base in data:
        print(f"\n# deltas vs '{base}' (clean-set changes)")
        bclean = {o for o in all_onts if clean(data[base].get(o, {}))}
        for a in arms:
            if a == base:
                continue
            aclean = {o for o in all_onts if clean(data[a].get(o, {}))}
            rec = sorted(aclean - bclean, key=lambda x: int(x.split("_")[-1].split(".")[0]) if x.split("_")[-1].split(".")[0].isdigit() else 0)
            reg = sorted(bclean - aclean)
            if rec or reg:
                tag = []
                if rec:
                    tag.append(f"+{len(rec)} RECOVER {[oid(o) for o in rec]}")
                if reg:
                    tag.append(f"-{len(reg)} REGRESS {[oid(o) for o in reg]}")
                print(f"  {a:<14} {' | '.join(tag)}")

    # ---- per-ont oracle / portfolio ----
    print("\n# per-ont oracle (best clean arm: min wall, then min mem)")
    oracle = {}
    for o in all_onts:
        cands = []
        for a in arms:
            r = data[a].get(o, {})
            if clean(r):
                cands.append((r["wall_s"], r["peak_mb"], a))
        if cands:
            cands.sort()
            oracle[o] = {"arm": cands[0][2], "wall_s": cands[0][0],
                         "peak_mb": cands[0][1], "n_clean_arms": len(cands)}
    no_arm = [o for o in all_onts if o not in oracle]
    base_clean = {o for o in all_onts if clean(data.get(base, {}).get(o, {}))}
    portfolio_only = sorted(set(oracle) - base_clean)
    print(f"  portfolio coverage (clean by SOME arm): {len(oracle)}/{nont}")
    print(f"  base clean: {len(base_clean)}/{nont}")
    print(f"  recovered by portfolio over base ({len(portfolio_only)}): "
          f"{[oid(o) for o in portfolio_only]}")
    print(f"  clean by NO arm ({len(no_arm)}): {[oid(o) for o in no_arm]}")

    # which non-base arm each portfolio-only ont needs
    if portfolio_only:
        print("\n# routing table for portfolio-only onts")
        for o in portfolio_only:
            arms_clean = sorted(a for a in arms if clean(data[a].get(o, {})))
            print(f"  {oid(o):<10} best={oracle[o]['arm']:<12} "
                  f"({oracle[o]['wall_s']:.1f}s) by: {arms_clean}")

    if portfolio_out:
        json.dump({"oracle": oracle, "no_arm": no_arm, "panel": panel},
                  open(portfolio_out, "w"), indent=1)
        print(f"\nwrote {portfolio_out}")


def oid(ont):
    # ore_ont_1234.owl -> 1234
    b = ont.replace("ore_ont_", "").replace(".owl", "")
    return b


if __name__ == "__main__":
    main()
