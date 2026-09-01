#!/usr/bin/env python3
"""Render the complete profile-aware KM terminal-cause ledger for LaTeX."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


PROFILES = ("OWL 2 EL", "OWL 2 DL, non-EL", "outside OWL 2 DL")
CAUSES = (
    ("ok", "OK"),
    ("timeout", "Timeout"),
    ("memout", "Memory"),
    ("route_no_retry_internal_cap", "Route cap"),
    ("unsupported_inverse_role_position", "Inverse role"),
    ("unsupported_complex_rule_atom", "Rule atom"),
    ("cb_incomplete_fixpoint", "CB defer"),
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--summary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    summary = json.loads(args.summary.read_text(encoding="utf-8"))
    if (summary.get("complete") is not True or summary.get("terminal_records") != 189
            or summary.get("expected_records") != 189):
        raise ValueError("refusing incomplete KM cause summary")
    counts = Counter({(row["profile"], row["cause"]): row["count"]
                      for row in summary["counts"]})
    known = {name for name, _ in CAUSES}
    unknown = {cause for (_profile, cause) in counts if cause not in known}
    if unknown:
        raise ValueError(f"unrendered terminal causes: {sorted(unknown)}")
    if sum(counts.values()) != 189:
        raise ValueError("terminal cause counts do not sum to 189")

    lines = [
        f"% Generated from KM terminal-cause summary SHA-256 {sha256(args.summary)}",
        r"\begin{table*}[t]",
        r"\centering",
        r"\small",
        r"\setlength{\tabcolsep}{4pt}",
        r"\caption{KM v1.3 automatic-route outcomes on the frozen OBO snapshot, partitioned by independently checked profile.  Inverse role and rule atom denote fail-closed frontend rejections; route cap denotes a source-feature route that disabled adaptive retry before an internal cap; CB defer denotes refusal to publish without a complete fixpoint.}",
        r"\label{tab:km-obo-causes}",
        r"\begin{tabular}{lrrrrrrrr}",
        r"\toprule",
        "Profile & $n$ & " + " & ".join(label for _name, label in CAUSES) + r" \\",
        r"\midrule",
    ]
    for profile in PROFILES:
        population = sum(counts[profile, cause] for cause, _label in CAUSES)
        label = profile.replace("outside", "Outside")
        values = [counts[profile, cause] for cause, _label in CAUSES]
        lines.append(f"{label} & {population} & " + " & ".join(map(str, values)) + r" \\")
    totals = [sum(counts[profile, cause] for profile in PROFILES) for cause, _label in CAUSES]
    lines += [
        r"\midrule",
        "All & 189 & " + " & ".join(map(str, totals)) + r" \\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\end{table*}",
        "",
    ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    temporary.write_text("\n".join(lines), encoding="utf-8")
    temporary.replace(args.output)
    print(f"KM_CAUSE_TABLE_OK\t{sha256(args.summary)}")


if __name__ == "__main__":
    main()
