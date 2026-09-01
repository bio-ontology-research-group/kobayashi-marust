#!/usr/bin/env python3
"""Render reproducible LaTeX tables from a complete current-corpus aggregate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ORDER = ("km", "konclude", "hermit", "jfact", "openllet", "more", "elk", "whelk")
LABEL = {"km": "KM", "konclude": "Konclude", "hermit": "HermiT", "jfact": "JFact",
         "openllet": "Openllet", "more": "MORe", "elk": "ELK", "whelk": "Whelk"}
CASE_LABEL = {"ncit": "NCIt", "uberon": "Uberon", "chebi": "ChEBI"}
PROFILE_LABEL = {"OWL2": "OWL 2", "OWL2DL": "DL", "OWL2EL": "EL",
                 "OWL2QL": "QL", "OWL2RL": "RL"}


def latex(value: object) -> str:
    """Escape machine-generated scalar text before inserting it into TeX."""
    replacements = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%",
        "$": r"\$", "#": r"\#", "_": r"\_", "{": r"\{",
        "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(character, character) for character in str(value))


def number(value: float | int | None, places: int = 2) -> str:
    return "--" if value is None else f"{value:.{places}f}"


def stratum_cell(row: dict) -> str:
    okay = row["status_counts"].get("ok", 0)
    median = row["wall_s"]["median"]
    return f"{okay}/{row['population']} ({number(median, 2)} s)"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--aggregate", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    payload = args.aggregate.read_bytes()
    aggregate = json.loads(payload)
    if aggregate.get("missing_or_invalid_records") != 0:
        raise ValueError("refusing to render an incomplete aggregate")

    lines = [f"% Generated from aggregate SHA-256 {hashlib.sha256(payload).hexdigest()}",
             "\\begin{table*}[t]", "\\centering", "\\small",
             "\\caption{Current OBO snapshot completion and resource results. Metrics use each system's OWL~2~DL completions. Other fail collects named terminal statuses not represented by timeout, memout, or generic error; each status row sums to the independently profiled DL population. Tested artifacts are additionally bound by SHA-256 in the machine-readable aggregate.}",
             "\\label{tab:current-obo}",
             "\\resizebox{\\textwidth}{!}{%", "\\begin{tabular}{llrrrrrrrrr}", "\\toprule",
             "Reasoner & Tested version/commit & OK & Timeout & Memout & Error & Other fail & Mean s & Median s & Mean MiB & Median MiB \\\\",
             "\\midrule"]
    for baseline in ORDER:
        version = latex(aggregate["baseline_artifacts"][baseline]["version_or_commit"])
        statuses = aggregate["status_counts_owl2dl"][baseline]
        if sum(statuses.values()) != aggregate["profile_counts"]["OWL2DL"]:
            raise ValueError(f"status population mismatch for {baseline}")
        other = sum(count for status, count in statuses.items()
                    if status not in {"ok", "timeout", "memout", "error"})
        performance = aggregate["performance_on_own_completions"][baseline]["owl2dl_own_completions"]
        lines.append(f"{LABEL[baseline]} & {version} & {statuses.get('ok', 0)} & {statuses.get('timeout', 0)} & "
                     f"{statuses.get('memout', 0)} & {statuses.get('error', 0)} & {other} & "
                     f"{number(performance['wall_s']['mean'], 3)} & "
                     f"{number(performance['wall_s']['median'], 3)} & "
                     f"{number(performance['peak_mb']['mean'], 1)} & "
                     f"{number(performance['peak_mb']['median'], 1)} \\\\")
    lines.extend(["\\bottomrule", "\\end{tabular}}", "\\end{table*}", "",
                  "\\begin{table*}[t]", "\\centering", "\\small",
                  "\\caption{Pairwise performance on OWL~2~DL inputs for which KM and the comparison system returned the same full-IRI named-class relation.}",
                  "\\label{tab:current-obo-pairwise}",
                  "\\resizebox{\\textwidth}{!}{%",
                  "\\begin{tabular}{lrrrrrrrrr}", "\\toprule",
                  "Comparison & $n$ & Mean s KM & Mean s ext. & Median s KM & Median s ext. & Mean MiB KM & Mean MiB ext. & Median MiB KM & Median MiB ext. \\\\",
                  "\\midrule"])
    for external in ORDER[1:]:
        pair = aggregate["pairwise_relation_agreement"][f"km:{external}"]
        performance = pair["performance_on_relation_agreements_owl2dl"]
        left, right = performance["left"], performance["right"]
        lines.append(f"{LABEL[external]} & {pair['relation_agreements_owl2dl']} & "
                     f"{number(left['wall_s']['mean'], 3)} & {number(right['wall_s']['mean'], 3)} & "
                     f"{number(left['wall_s']['median'], 3)} & {number(right['wall_s']['median'], 3)} & "
                     f"{number(left['peak_mb']['mean'], 1)} & {number(right['peak_mb']['mean'], 1)} & "
                     f"{number(left['peak_mb']['median'], 1)} & {number(right['peak_mb']['median'], 1)} \\\\")
    lines.extend(["\\bottomrule", "\\end{tabular}}", "\\end{table*}", "",
                  "\\begin{table*}[t]", "\\centering", "\\scriptsize",
                  "\\caption{Completion by expressivity and logical-axiom size. Each cell reports successful terminal runs over inputs in the stratum, followed by median wall time for those runs. EL systems are complete references only in the independently verified EL column.}",
                  "\\label{tab:current-obo-strata}", "\\resizebox{\\textwidth}{!}{%",
                  "\\begin{tabular}{lrrrrrrr}", "\\toprule",
                  "Reasoner & OWL 2 EL & DL non-EL & Outside DL & $<1$k & 1k--10k & 10k--100k & $\\geq100$k " + r"\\",
                  "\\midrule"])
    for baseline in ORDER:
        expressivity = aggregate["stratified_results"]["expressivity"]
        size = aggregate["stratified_results"]["size"]
        cells = [
            stratum_cell(expressivity["OWL 2 EL"][baseline]),
            stratum_cell(expressivity["OWL 2 DL, non-EL"][baseline]),
            stratum_cell(expressivity["outside OWL 2 DL"][baseline]),
            stratum_cell(size["<1k"][baseline]),
            stratum_cell(size["1k--10k"][baseline]),
            stratum_cell(size["10k--100k"][baseline]),
            stratum_cell(size[">=100k"][baseline]),
        ]
        lines.append(f"{LABEL[baseline]} & " + " & ".join(cells) + " " + r"\\")
    lines.extend(["\\bottomrule", "\\end{tabular}}", "\\end{table*}", "",
                  "\\begin{table*}[t]", "\\centering", "\\scriptsize",
                  "\\caption{Named hard cases contained in the OBO snapshot. Each cell is the terminal classification status. The final column groups completing expressive systems with identical full-IRI named-class relations.}",
                  "\\label{tab:current-obo-hard}", "\\resizebox{\\textwidth}{!}{%",
                  "\\begin{tabular}{llrrrrrrrrl}", "\\toprule",
                  "Case & Profiles & KM & Konclude & HermiT & JFact & Openllet & MORe & ELK & Whelk & Expressive relation groups " + r"\\",
                  "\\midrule"])
    for case in ("ncit", "uberon", "chebi"):
        row = aggregate["named_obo_hard_cases"][case]
        profiles = ", ".join(PROFILE_LABEL[name]
                             for name, present in row["profiles"].items() if present)
        groups = "; ".join(
            ",".join(LABEL[baseline] for baseline in group["baselines"])
            for group in row["expressive_relation_groups"]
        ) or "--"
        statuses = " & ".join(latex(row["statuses"][baseline]) for baseline in ORDER)
        lines.append(f"{CASE_LABEL[case]} & {profiles} & {statuses} & {groups} " + r"\\")
    lines.extend(["\\bottomrule", "\\end{tabular}}", "\\end{table*}", ""])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(args.output) + ".part")
    temporary.write_text("\n".join(lines), encoding="utf-8")
    temporary.replace(args.output)
    print(f"CURRENT_TABLES_OK\t{args.output}")


if __name__ == "__main__":
    main()
