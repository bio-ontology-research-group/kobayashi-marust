#!/usr/bin/env python3
"""Complete projection ledger for the EL context-parallel selector.

Joins three retained inputs, one row per ORE 2015 ontology:

* the selector projection emitted by
  `routing::tests::context_parallel_projection_over_the_retained_profiles`
  (route under full routing precedence, and the armed worker count),
* the current strict external audit (IBEX array 51242642) and the external
  per-ontology targets,
* the paired context panel medians (IBEX array 51251013) where the ontology
  was measured.

The projected verdict uses the panel's own ctx8 medians for a measured armed
ontology and holds the current measurement for every other row, which never
credits an unmeasured ontology with an improvement.

    build_projection_ledger.py <projection.tsv> <audit-results-dir>
                               <targets.tsv> <panel-medians.tsv> <out.tsv>
"""
import json
import os
import sys


def read_tsv(path):
    rows = []
    with open(path) as handle:
        header = handle.readline().rstrip("\n").split("\t")
        for line in handle:
            rows.append(dict(zip(header, line.rstrip("\n").split("\t"))))
    return rows


def main(projection_path, audit_dir, targets_path, panel_path, out_path):
    projection = read_tsv(projection_path)
    panel = {row["ontology"]: row for row in read_tsv(panel_path)}
    targets = {}
    for line in open(targets_path):
        fields = line.rstrip("\n").split("\t")
        if fields[0] == "ontology":
            continue
        targets[fields[0]] = (float(fields[1]), float(fields[3]))

    header = [
        "ontology",
        "route",
        "armed_workers",
        "logical_axioms",
        "distinct_classes",
        "object_properties",
        "existentials",
        "file_bytes",
        "current_wall_s",
        "current_peak_mib",
        "wall_target_s",
        "peak_target_mib",
        "current_strict",
        "panel_serial_wall_s",
        "panel_serial_peak_mib",
        "panel_ctx8_wall_s",
        "panel_ctx8_peak_mib",
        "projected_strict",
        "basis",
    ]
    rows = ["\t".join(header)]
    counts = {"armed": 0, "measured": 0, "recovered": 0, "regressed": 0, "unmeasured": 0}
    recovered, unmeasured = [], []
    for row in projection:
        ont = row["ontology"]
        audit = json.load(open(os.path.join(audit_dir, f"{ont}.json")))
        wall, peak = audit["wall_s"], audit["peak_mb"]
        armed = row["armed_workers"] != "serial"
        target = targets.get(ont)
        if target is None:
            wall_target = peak_target = None
            current = projected = "unadjudicated"
        else:
            wall_target, peak_target = target
            current = "pass" if wall < wall_target and peak < peak_target else "fail"
            projected = current
        measured = panel.get(ont)
        basis = "serial, unchanged"
        ctx8 = ("", "")
        serial = ("", "")
        if armed:
            counts["armed"] += 1
            if measured is None:
                counts["unmeasured"] += 1
                unmeasured.append(ont)
                basis = "armed, not in the panel: verdict holds the current measurement"
            else:
                counts["measured"] += 1
                serial = (measured["serial_wall_s"], measured["serial_peak_mib"])
                ctx8 = (measured["ctx8_wall_s"], measured["ctx8_peak_mib"])
                basis = "armed, measured ctx8 median (array 51251013)"
                if target is not None:
                    projected = (
                        "pass"
                        if float(ctx8[0]) < wall_target and float(ctx8[1]) < peak_target
                        else "fail"
                    )
                    if current == "fail" and projected == "pass":
                        counts["recovered"] += 1
                        recovered.append(ont)
                    if current == "pass" and projected == "fail":
                        counts["regressed"] += 1
        elif measured is not None:
            serial = (measured["serial_wall_s"], measured["serial_peak_mib"])
            ctx8 = (measured["ctx8_wall_s"], measured["ctx8_peak_mib"])
            basis = "in the panel, not armed: serial"
        rows.append(
            "\t".join(
                [
                    ont,
                    row["route"],
                    row["armed_workers"],
                    row["logical_axioms"],
                    row["distinct_classes"],
                    row["object_properties"],
                    row["existentials"],
                    row["file_bytes"],
                    f"{wall:.4f}",
                    f"{peak:.2f}",
                    "" if wall_target is None else f"{wall_target:.4f}",
                    "" if peak_target is None else f"{peak_target:.2f}",
                    current,
                    serial[0],
                    serial[1],
                    ctx8[0],
                    ctx8[1],
                    projected,
                    basis,
                ]
            )
        )
    open(out_path, "w").write("\n".join(rows) + "\n")
    print(f"rows {len(projection)}")
    print(counts)
    print("recovered:", " ".join(recovered))
    print("armed without a panel measurement:", " ".join(unmeasured))
    return 0


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:6]))
