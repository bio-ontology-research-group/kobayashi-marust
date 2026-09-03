#!/usr/bin/env python3
"""Median wall and peak per ontology and arm of the paired EL context panel.

Reads the retained per-run records of IBEX array 51251013 (four arms x three
replicates x eighteen elc-routed ontologies) and writes one row per ontology
with the medians of every arm and the external per-ontology targets.

    build_panel_medians.py <panel-results-dir> <targets.tsv> <out.tsv>
"""
import json
import os
import statistics
import sys

ARMS = ("serial", "ctx2", "ctx4", "ctx8")


def main(results_dir: str, targets_path: str, out_path: str) -> int:
    runs: dict[tuple[str, str], list[dict]] = {}
    for name in sorted(os.listdir(results_dir)):
        if not name.endswith(".json") or name.endswith(".checkpoint.json"):
            continue
        record = json.load(open(os.path.join(results_dir, name)))
        # Every retained run must be a gold-matching completion on the EL route.
        assert record["status"] == "ok", name
        assert record["verdict"] == "match", name
        assert record["selected_route_trace"] == "elc", name
        ont, arm = name.split(".owl.")[0] + ".owl", name.split(".owl.")[1].split(".")[0]
        runs.setdefault((ont, arm), []).append(record)

    targets = {}
    for line in open(targets_path):
        fields = line.rstrip("\n").split("\t")
        if fields[0] == "ontology":
            continue
        targets[fields[0]] = (float(fields[1]), float(fields[3]))

    onts = sorted({ont for ont, _ in runs}, key=lambda o: int(o.split("_")[2].split(".")[0]))
    header = ["ontology", "replicates", "signature_sha256"]
    for arm in ARMS:
        header += [f"{arm}_wall_s", f"{arm}_peak_mib"]
    header += ["wall_target_s", "peak_target_mib", "serial_strict", "ctx8_strict"]
    rows = ["\t".join(header)]
    for ont in onts:
        signatures = {r["signature_sha256"] for arm in ARMS for r in runs[(ont, arm)]}
        # The parallel engine is byte-identical to the serial one.
        assert len(signatures) == 1, (ont, signatures)
        replicates = {len(runs[(ont, arm)]) for arm in ARMS}
        assert replicates == {3}, (ont, replicates)
        medians = {}
        for arm in ARMS:
            medians[arm] = (
                statistics.median(r["wall_s"] for r in runs[(ont, arm)]),
                statistics.median(r["peak_mb"] for r in runs[(ont, arm)]),
            )
        wall_target, peak_target = targets[ont]

        def strict(arm: str) -> str:
            wall, peak = medians[arm]
            return "pass" if wall < wall_target and peak < peak_target else "fail"

        row = [ont, "3", signatures.pop()]
        for arm in ARMS:
            row += [f"{medians[arm][0]:.4f}", f"{medians[arm][1]:.2f}"]
        row += [f"{wall_target:.4f}", f"{peak_target:.2f}", strict("serial"), strict("ctx8")]
        rows.append("\t".join(row))
    open(out_path, "w").write("\n".join(rows) + "\n")
    print(f"{len(onts)} ontologies, {sum(len(v) for v in runs.values())} runs")
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))
