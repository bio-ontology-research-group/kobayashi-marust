#!/usr/bin/env python3
"""Run Item 3 validation across all 25 pools of sat578-opus/tools/pools.sh plus
the two remaining families of .work/v155-seedround/families.txt
(bridge-nn-term-fam and cb-nn1811-fam).

Uses the guard-trace method:
1. On the 25 pools of pools.sh (47,344 seed-routes), reruns all 7,032 fired
   seed-routes of sat578-opus/data/pools/final-rows.tsv.gz on km-fix at 60 s.
2. Runs km-fix with KM_HT_SAT578_GUARD_TRACE on bridge-nn-term-fam and
   cb-nn1811-fam (both routes, 60 s cap); runs km-base (km-4bf690c8) on every
   marked or non-ok row of those two families.
3. For every seed-route where km-base (km-4bf690c8) and km-fix differ, runs 3
   confirming runs on both km-base and km-fix.
"""
import concurrent.futures as cf
import glob
import gzip
import json
import os
import signal
import subprocess
import sys
import time

ROOT = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust"
SCRATCH = f"{ROOT}/.work/agent-scratch"
MY_SCRATCH = f"{SCRATCH}/sat578-lost-argon"
WORKTREE = f"{ROOT}/.work/worktrees/fix-sat578-lost-argon"
DATA_DIR = f"{WORKTREE}/results/agents/2026-11-09/sat578-lost-argon/data/pools"
OPUS_FINAL_ROWS = f"{WORKTREE}/results/agents/2026-11-08/sat578-opus/data/pools/final-rows.tsv.gz"

KM_BASE = f"{MY_SCRATCH}/bin/km-4bf690c8"
KM_FIX = f"{MY_SCRATCH}/bin/km-fix"

THREADS = int(os.environ.get("DIFF_THREADS", "2"))
CAP = int(os.environ.get("DIFF_KM_TIMEOUT", "60"))

RELEASE = {
    "KM_HT_DDB": "1",
    "KM_HT_NATIVE_FULL": "1",
    "KM_CACHE_CONFORMANCE": "1",
    "KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE": "1",
    "KM_FAST_IRI_GRAMMAR": "1",
    "KM_THREADS": "1",
    "KM_TIMING": "1",
}

NNR = f"{ROOT}/.work/worktrees/fix-bridge-nn-rule/results/agents/2026-11-04/bridge-nn-rule/data/reductions"


def gold_dir_for_pool(pool):
    if pool == "sat578-fam":
        return f"{SCRATCH}/sat578/famgold"
    if pool == "bridge-satcache-fam":
        return f"{SCRATCH}/bridge-satcache/famgold"
    if pool == "bridge-nn-rule-fam":
        return f"{SCRATCH}/bridge-nn-rule/fam/gold"
    if pool == "bridge-nn-term-fam":
        return f"{SCRATCH}/bridge-nn-term/fam/gold"
    if pool == "cb-nn1811-fam":
        return f"{SCRATCH}/cb-nn1811/fam/gold"
    if pool.startswith("bridge-self-pools-"):
        sub = pool[len("bridge-self-pools-") :]
        return f"{SCRATCH}/bridge-self/pools/{sub}/gold"
    if pool == "bridge-self-pool":
        return f"{SCRATCH}/bridge-self/pool/gold"
    if pool == "bridge-self-regress":
        return f"{SCRATCH}/bridge-self/regress/gold"
    if pool == "bridge-self-micro":
        return f"{SCRATCH}/bridge-self/micro/gold"
    if pool == "bridge-m413-respool":
        return f"{SCRATCH}/bridge-m413/respool/gold"
    if pool == "bridge-m413-k":
        return f"{SCRATCH}/bridge-m413/kgold"
    if pool == "bridge-m413-k2":
        return f"{SCRATCH}/bridge-m413/k2gold"
    if pool == "cb-s974-merge":
        return f"{SCRATCH}/cb-s974/fam-merge/gold"
    if pool == "cb-s974-vacuous":
        return f"{SCRATCH}/cb-s974/fam-vacuous/gold"
    if pool == "bridge-reflexive-fam":
        return f"{SCRATCH}/bridge-reflexive/fam/gold"
    if pool == "bridge-reflexive-seeds20":
        return f"{SCRATCH}/bridge-reflexive/seeds20/gold"
    if pool == "bridge-nn-rule-red":
        return NNR
    if pool == "bridge-satcache-red":
        return f"{SCRATCH}/bridge-satcache/gold"
    if pool == "bridge-satcache-self":
        return f"{SCRATCH}/bridge-satcache/selffix/gold"
    raise ValueError(f"Unknown pool: {pool}")


def strip(name):
    return name.lstrip(":").split("#")[-1]


GOLD_CACHE = {}


def load_gold(pool, seed):
    key = (pool, seed)
    if key in GOLD_CACHE:
        return GOLD_CACHE[key]
    stem = os.path.splitext(os.path.basename(seed))[0]
    gp = os.path.join(gold_dir_for_pool(pool), stem + ".json")
    if not os.path.exists(gp):
        GOLD_CACHE[key] = None
        return None
    with open(gp) as f:
        d = json.load(f)
    uns = frozenset(strip(c) for c in d["unsatisfiable"])
    subs = frozenset(
        (strip(a), strip(b))
        for a, b in d["subsumptions"]
        if strip(a) not in uns and strip(b) not in uns and strip(a) != strip(b)
    )
    res = (bool(d["consistent"]), subs, uns)
    GOLD_CACHE[key] = res
    return res


def run_km_one(args):
    km_bin, pool, seed, route, trace_dir = args
    h = load_gold(pool, seed)
    if h is None:
        return (pool, seed, route, "NOGOLD", 0.0, False)
    env = {k: v for k, v in os.environ.items() if not k.startswith("KM_")}
    env.update(RELEASE)
    if route != "auto":
        env["KM_ROUTE"] = route
    marker = None
    if trace_dir:
        stem = os.path.splitext(os.path.basename(seed))[0]
        marker = os.path.join(trace_dir, f"{pool}__{stem}.{route}.fired")
        if os.path.exists(marker):
            os.remove(marker)
        env["KM_HT_SAT578_GUARD_TRACE"] = marker
    t0 = time.time()
    p = subprocess.Popen(
        [km_bin, "classify", "--lines", seed],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
        start_new_session=True,
    )
    try:
        out, err = p.communicate(timeout=CAP)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        dt = time.time() - t0
        fired = bool(marker and os.path.exists(marker))
        return (pool, seed, route, "TIMEOUT", dt, fired)
    dt = time.time() - t0
    fired = bool(marker and os.path.exists(marker))
    cons, subs, uns = None, set(), set()
    for line in out.splitlines():
        t = line.split("\t")
        if t[0].startswith("CONSISTENT"):
            cons = t[0].endswith("1")
        elif t[0] == "SUB" and len(t) == 3:
            subs.add((strip(t[1]), strip(t[2])))
        elif t[0] == "UNSAT" and len(t) == 2:
            uns.add(strip(t[1]))
    if cons is None:
        return (pool, seed, route, "ERR", dt, fired)
    subs = frozenset(
        s for s in subs if s[0] not in uns and s[1] not in uns and s[0] != s[1]
    )
    if not h[0]:
        verdict = "ok" if not cons else "WRONG"
        return (pool, seed, route, verdict, dt, fired)
    ms, es = len(h[1] - subs), len(subs - h[1])
    mu, eu = len(h[2] - uns), len(uns - h[2])
    cm = int(cons != h[0])
    verdict = "ok" if (ms, es, mu, eu, cm) == (0, 0, 0, 0, 0) else "WRONG"
    return (pool, seed, route, verdict, dt, fired)


def main():
    os.makedirs(DATA_DIR, exist_ok=True)
    trace_dir = os.path.join(MY_SCRATCH, "fired-markers")
    os.makedirs(trace_dir, exist_ok=True)

    # 1. Load opus final-rows.tsv.gz
    # Columns in opus final-rows.tsv.gz:
    # pool, seed, route, fired_on_b1fcbb93, v_274faa6a, s_274faa6a, v_4bf690c8, s_4bf690c8
    opus_rows = []
    fired_jobs = []
    with gzip.open(OPUS_FINAL_ROWS, "rt") as f:
        for line in f:
            if line.startswith("#"):
                continue
            parts = line.rstrip("\n").split("\t")
            pool, seed, route, fired_flag, v_274, s_274, v_4bf, s_4bf = parts
            opus_rows.append((pool, seed, route, fired_flag, v_274, s_274, v_4bf, s_4bf))
            if fired_flag == "fired":
                fired_jobs.append((KM_FIX, pool, seed, route, trace_dir))

    print(f"Loaded {len(opus_rows)} opus pool rows ({len(fired_jobs)} fired to rerun on km-fix)", flush=True)

    rerun_cache_path = os.path.join(DATA_DIR, "fired-rerun.tsv.gz")
    fired_results = {}
    if os.path.exists(rerun_cache_path):
        with gzip.open(rerun_cache_path, "rt") as f:
            for line in f:
                p, s, r, v, dt, fd = line.rstrip("\n").split("\t")
                fired_results[(p, s, r)] = (v, float(dt), fd == "True")
        print(f"Loaded {len(fired_results)} cached fired-rerun rows", flush=True)

    todo_fired = [j for j in fired_jobs if (j[1], j[2], j[3]) not in fired_results]
    if todo_fired:
        print(f"Running {len(todo_fired)} fired rows on km-fix...", flush=True)
        with cf.ThreadPoolExecutor(THREADS) as ex:
            for idx, res in enumerate(ex.map(run_km_one, todo_fired), 1):
                p, s, r, v, dt, fd = res
                fired_results[(p, s, r)] = (v, dt, fd)
                if idx % 500 == 0 or idx == len(todo_fired):
                    print(f"  fired rerun: {idx}/{len(todo_fired)}", flush=True)
        with gzip.open(rerun_cache_path, "wt") as f:
            for (p, s, r), (v, dt, fd) in sorted(fired_results.items()):
                f.write(f"{p}\t{s}\t{r}\t{v}\t{dt:.2f}\t{fd}\n")

    # 2. Extra families from families.txt not in pools.sh: bridge-nn-term-fam and cb-nn1811-fam
    extra_fams = [
        ("bridge-nn-term-fam", f"{SCRATCH}/bridge-nn-term/fam/seeds", f"{SCRATCH}/bridge-nn-term/fam/gold"),
        ("cb-nn1811-fam", f"{SCRATCH}/cb-nn1811/fam/seeds", f"{SCRATCH}/cb-nn1811/fam/gold"),
    ]
    extra_cache_path = os.path.join(DATA_DIR, "extra-fams.tsv.gz")
    extra_rows = []
    if os.path.exists(extra_cache_path):
        with gzip.open(extra_cache_path, "rt") as f:
            for line in f:
                if line.startswith("#"):
                    continue
                extra_rows.append(tuple(line.rstrip("\n").split("\t")))
        print(f"Loaded {len(extra_rows)} cached extra-fams rows", flush=True)
    else:
        extra_jobs = []
        for pool, sdir, gdir in extra_fams:
            for sf in sorted(glob.glob(os.path.join(sdir, "*.ofn"))):
                stem = os.path.splitext(os.path.basename(sf))[0]
                if os.path.exists(os.path.join(gdir, stem + ".json")):
                    for route in ["ht_bridge", "auto"]:
                        extra_jobs.append((KM_FIX, pool, sf, route, trace_dir))
        print(f"Running {len(extra_jobs)} extra-family rows on km-fix...", flush=True)
        fix_extra = {}
        with cf.ThreadPoolExecutor(THREADS) as ex:
            for idx, res in enumerate(ex.map(run_km_one, extra_jobs), 1):
                p, s, r, v, dt, fd = res
                fix_extra[(p, s, r)] = (v, dt, fd)
                if idx % 500 == 0 or idx == len(extra_jobs):
                    print(f"  extra-fams fix: {idx}/{len(extra_jobs)}", flush=True)
        base_need_jobs = [
            (KM_BASE, p, s, r, None)
            for (p, s, r), (v, dt, fd) in sorted(fix_extra.items())
            if fd or v != "ok"
        ]
        print(f"Running {len(base_need_jobs)} marked/non-ok extra-family rows on km-base...", flush=True)
        base_extra = {}
        with cf.ThreadPoolExecutor(THREADS) as ex:
            for idx, res in enumerate(ex.map(run_km_one, base_need_jobs), 1):
                p, s, r, v, dt, _ = res
                base_extra[(p, s, r)] = (v, dt)
                if idx % 200 == 0 or idx == len(base_need_jobs):
                    print(f"  extra-fams base: {idx}/{len(base_need_jobs)}", flush=True)
        with gzip.open(extra_cache_path, "wt") as f:
            f.write("# pool\tseed\troute\tfired\tbase_4bf\tbase_s\tfix\tfix_s\n")
            for (p, s, r), (fv, fdt, fd) in sorted(fix_extra.items()):
                if (p, s, r) in base_extra:
                    bv, bdt = base_extra[(p, s, r)]
                    bs_str = f"{bdt:.2f}"
                else:
                    bv, bs_str = fv, "quiet"
                row = (p, s, r, "fired" if fd else "quiet", bv, bs_str, fv, f"{fdt:.2f}")
                extra_rows.append(row)
                f.write("\t".join(row) + "\n")

    # 3. Combine all rows and compare km-base (4bf690c8) vs km-fix
    all_combined = []
    for pool, seed, route, fired_flag, v_274, s_274, v_4bf, s_4bf in opus_rows:
        if fired_flag == "fired":
            fv, fdt, fd = fired_results[(pool, seed, route)]
            fs_str = f"{fdt:.2f}"
            f_str = "fired" if fd else "quiet_on_fix"
        else:
            fv, fs_str, f_str = v_4bf, s_4bf, "quiet"
        all_combined.append((pool, seed, route, f_str, v_274, s_274, v_4bf, s_4bf, fv, fs_str))

    for pool, seed, route, f_str, bv, bs_str, fv, fs_str in extra_rows:
        all_combined.append((pool, seed, route, f_str, bv, bs_str, bv, bs_str, fv, fs_str))

    diff_path = os.path.join(DATA_DIR, "final-diff.tsv")
    table_path = os.path.join(DATA_DIR, "final-table.txt")
    tab = {}
    flips_to_confirm = []
    with open(diff_path, "w") as df:
        df.write("# pool\tseed\troute\tfired\tv_274faa6a\ts_274faa6a\tv_4bf690c8\ts_4bf690c8\tv_fix\ts_fix\n")
        for row in all_combined:
            pool, seed, route, f_str, v_274, s_274, v_4bf, s_4bf, fv, fs_str = row
            k = (pool, route, v_4bf, fv)
            tab[k] = tab.get(k, 0) + 1
            if v_4bf != fv or fv == "WRONG":
                df.write("\t".join(row) + "\n")
            if v_4bf != fv:
                flips_to_confirm.append((pool, seed, route, v_274, v_4bf, fv))

    with open(table_path, "w") as tf:
        by_pool = {}
        for (pool, route, b, f), n in sorted(tab.items()):
            by_pool.setdefault(pool, []).append(f"{route}:{b}->{f}={n}")
        for pool, items in sorted(by_pool.items()):
            line = f"{pool} {' '.join(items)}"
            tf.write(line + "\n")
            print(line, flush=True)

    # 4. Run 3 confirming runs on any flip between km-4bf690c8 and km-fix
    flips_path = os.path.join(DATA_DIR, "flips-3runs.tsv")
    if flips_to_confirm:
        print(f"Confirming {len(flips_to_confirm)} flips (3 runs each on km-base and km-fix)...", flush=True)
        confirm_jobs = []
        for r_idx in range(1, 4):
            for pool, seed, route, _, _, _ in flips_to_confirm:
                confirm_jobs.append((KM_BASE, pool, seed, route, None, "km-4bf690c8", r_idx))
                confirm_jobs.append((KM_FIX, pool, seed, route, None, "km-fix", r_idx))

        def run_confirm(item):
            km_bin, pool, seed, route, tr, tag, r_idx = item
            p, s, r, v, dt, _ = run_km_one((km_bin, pool, seed, route, tr))
            return (tag, r_idx, p, s, r, v, dt)

        with open(flips_path, "w") as ff, cf.ThreadPoolExecutor(THREADS) as ex:
            ff.write("# binary\trun\tpool\tseed\troute\tverdict\tseconds\n")
            for tag, r_idx, p, s, r, v, dt in ex.map(run_confirm, confirm_jobs):
                line = f"{tag}\t{r_idx}\t{p}\t{s}\t{r}\t{v}\t{dt:.2f}"
                ff.write(line + "\n")
                ff.flush()
                print("  confirm:", line, flush=True)


if __name__ == "__main__":
    main()
