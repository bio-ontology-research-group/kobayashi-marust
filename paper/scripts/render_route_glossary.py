#!/usr/bin/env python3
"""Render the public route catalogue directly from engine/src/routing.rs."""

from __future__ import annotations

import csv
from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[2]
SOURCE = REPO / "engine/src/routing.rs"
OUT_TSV = REPO / "paper/generated/route-glossary.tsv"
OUT_TEX = REPO / "paper/generated/route-glossary.tex"


def block(text: str, pattern: str) -> str:
    match = re.search(pattern, text, re.S)
    if not match:
        raise ValueError(f"route catalogue block not found: {pattern}")
    return match.group(1)


def tex(value: str) -> str:
    return (
        value.replace("\\", r"\textbackslash{}")
        .replace("_", r"\_")
        .replace("&", r"\&")
        .replace("%", r"\%")
    )


def main() -> None:
    text = SOURCE.read_text(encoding="utf-8")
    named = re.findall(
        r"Route::(\w+)",
        block(text, r"pub const NAMED: \[Route; \d+\] = \[(.*?)\];"),
    )
    names = dict(
        re.findall(
            r"Route::(\w+)\s*=>\s*\"([^\"]+)\"",
            block(text, r"pub fn as_str\(self\).*?match self \{(.*?)\n\s*\}"),
        )
    )
    settings: dict[str, str] = {}
    settings_block = block(text, r"pub fn settings\(self\).*?match self \{(.*?)\n\s*\}")
    for lhs, expression in re.findall(r"^\s*((?:Route::\w+\s*\|\s*)*Route::\w+)\s*=>\s*(.*),$", settings_block, re.M):
        for variant in re.findall(r"Route::(\w+)", lhs):
            settings[variant] = expression.strip()
    constants: dict[str, list[tuple[str, str]]] = {}
    for constant, body in re.findall(
        r"const ([A-Z][A-Z0-9_]*): &\[\(&str, &str\)\] = &\[(.*?)\n\];",
        text,
        re.S,
    ):
        constants[constant] = re.findall(r'\("([^\"]+)",\s*"([^\"]*)"\)', body)

    common = constants["COMMON_SETTINGS"]
    rows: list[tuple[str, str, str]] = []
    for variant in named:
        route = names[variant]
        symbol = settings[variant]
        options = dict(common)
        if symbol.startswith("&["):
            options.update(re.findall(r'\("([^\"]+)",\s*"([^\"]*)"\)', symbol))
        elif symbol != "&[]":
            options.update(constants[symbol])
        bundle = "; ".join(f"{key}={value}" for key, value in options.items())
        rows.append((route, variant, bundle))

    OUT_TSV.parent.mkdir(parents=True, exist_ok=True)
    with OUT_TSV.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.writer(stream, delimiter="\t", lineterminator="\n")
        writer.writerow(("route", "rust_variant", "effective_option_bundle"))
        writer.writerows(rows)

    lines = [
        r"\begin{longtable}{@{}p{0.18\linewidth}p{0.76\linewidth}@{}}",
        r"\caption{Public v1.3 route glossary generated from \texttt{engine/src/routing.rs}. Common settings are expanded and route-local values take precedence.}\label{tab:route-glossary}\\",
        r"\toprule",
        r"Route & Effective option bundle \\",
        r"\midrule",
        r"\endfirsthead",
        r"\toprule Route & Effective option bundle \\",
        r"\midrule",
        r"\endhead",
    ]
    lines.extend(f"\\texttt{{{tex(route)}}} & \\texttt{{{tex(bundle)}}} \\\\" for route, _, bundle in rows)
    lines.extend((r"\bottomrule", r"\end{longtable}"))
    OUT_TEX.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"ROUTE_GLOSSARY_OK\t{len(rows)}\t{OUT_TSV.relative_to(REPO)}")


if __name__ == "__main__":
    main()
