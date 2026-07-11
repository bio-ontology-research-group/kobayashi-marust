#!/usr/bin/env python3
import glob
import json
import os
import statistics
import sys
from collections import Counter


resdir = sys.argv[1] if len(sys.argv) > 1 else "/ibex/scratch/hohndor/km/trigger_sweep_20260710/res"
rows = {}
for path in glob.glob(os.path.join(resdir, "*.jsonl")):
    for line in open(path):
        try:
            row = json.loads(line)
        except (json.JSONDecodeError, OSError):
            continue
        rows.setdefault(row["ont"], {})[row["config"]] = row


def exact(row):
    return row is not None and row.get("status") == "ok" and row.get("verdict") in {"match", "nogold", "incons"}


def key(name):
    stem = name.removeprefix("ore_ont_").removesuffix(".owl")
    return int(stem) if stem.isdigit() else stem


onts = sorted(rows, key=key)
print(f"complete ontology records: {len(onts)}")
for config in ("default", "trigger"):
    config_rows = [rows[o].get(config) for o in onts]
    config_rows = [r for r in config_rows if r is not None]
    statuses = Counter(r["status"] for r in config_rows)
    verdicts = Counter(r["verdict"] for r in config_rows)
    walls = [r["wall_s"] for r in config_rows if exact(r)]
    mems = [r["peak_kb"] / 1024 for r in config_rows if exact(r) and r.get("peak_kb")]
    print(
        f"{config}: n={len(config_rows)} exact={sum(exact(r) for r in config_rows)} "
        f"status={dict(statuses)} verdict={dict(verdicts)} "
        f"median_wall={statistics.median(walls):.2f}s median_rss={statistics.median(mems):.1f}MB"
    )

newly_exact = []
lost_exact = []
changed_answer = []
faster = []
slower = []
for ont in onts:
    base = rows[ont].get("default")
    trigger = rows[ont].get("trigger")
    if base is None or trigger is None:
        continue
    if exact(trigger) and not exact(base):
        newly_exact.append((ont, base, trigger))
    if exact(base) and not exact(trigger):
        lost_exact.append((ont, base, trigger))
    if base["verdict"] != trigger["verdict"] or base["extra"] != trigger["extra"] or base["miss"] != trigger["miss"]:
        changed_answer.append((ont, base, trigger))
    if exact(base) and exact(trigger):
        delta = trigger["wall_s"] - base["wall_s"]
        item = (delta, ont, base, trigger)
        (faster if delta < 0 else slower).append(item)


def show_transition(title, values):
    print(f"\n{title}: {len(values)}")
    for ont, base, trigger in values:
        print(
            f"  {ont}: default={base['status']}/{base['verdict']} "
            f"({base['wall_s']}s,{base['peak_kb'] / 1024:.1f}MB) -> "
            f"trigger={trigger['status']}/{trigger['verdict']} "
            f"({trigger['wall_s']}s,{trigger['peak_kb'] / 1024:.1f}MB)"
        )


show_transition("newly exact", newly_exact)
show_transition("lost exact", lost_exact)
show_transition("changed correctness result", changed_answer)

print("\nLargest speedups among exact/exact:")
for delta, ont, base, trigger in sorted(faster)[:25]:
    print(f"  {ont}: {base['wall_s']}s -> {trigger['wall_s']}s ({delta:+d}s)")

print("\nLargest slowdowns among exact/exact:")
for delta, ont, base, trigger in sorted(slower, reverse=True)[:25]:
    print(f"  {ont}: {base['wall_s']}s -> {trigger['wall_s']}s ({delta:+d}s)")
