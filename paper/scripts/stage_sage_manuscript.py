#!/usr/bin/env python3
"""Create a disposable Sage ``sagej`` build tree from the canonical paper.

The canonical manuscript remains ``paper/main.tex`` while experiments and
benchmark tables are still changing.  This script tests that the same content
can be typeset with Sage's class without maintaining a second, drifting paper.
The Sage template is supplied externally because its class file has separate
rules of use and is not part of KM's source distribution.
"""

from __future__ import annotations

import argparse
import re
import shutil
from pathlib import Path


TITLE = (
    r"Kobayashi-MaRust 1.3: A Proof-Carrying Hybrid OWL Reasoner\\"
    "\n"
    r"and an Agentic, Verification-Centred Development Method"
)

SAGE_FRONTMATTER = rf"""\begin{{document}}
\runninghead{{Hoehndorf}}
\title{{{TITLE}}}
\author{{Robert Hoehndorf\affilnum{{1}}}}
\affiliation{{\affilnum{{1}}King Abdullah University of Science and
Technology (KAUST), Saudi Arabia}}
\corrauth{{Robert Hoehndorf, King Abdullah University of Science and
Technology, Thuwal 23955-6900, Saudi Arabia.}}
\email{{robert.hoehndorf@kaust.edu.sa}}
"""


def stage(source: Path, template_dir: Path, output_dir: Path, class_options: str) -> Path:
    text = source.read_text(encoding="utf-8")
    text = text.replace(
        r"\documentclass[11pt]{article}",
        rf"\documentclass[{class_options}]{{sagej}}",
        1,
    )
    text = text.replace(r"\usepackage[margin=1in]{geometry}" + "\n", "", 1)

    header = re.compile(
        r"\\title\{Kobayashi-MaRust 1\.3:.*?\\date\{\}\n\n"
        r"\\begin\{document\}\n\\maketitle\n",
        re.DOTALL,
    )
    text, count = header.subn(lambda _: SAGE_FRONTMATTER, text, count=1)
    if count != 1:
        raise SystemExit("could not identify the canonical article frontmatter")

    keywords = re.compile(
        r"\\noindent\\textbf\{Keywords:\} (.*?)\n\n\\section\{Introduction\}",
        re.DOTALL,
    )
    text, count = keywords.subn(
        lambda match: (
            r"\keywords{" + match.group(1).replace("\n", " ") + "}\n\n"
            r"\maketitle" + "\n\n" + r"\section{Introduction}"
        ),
        text,
        count=1,
    )
    if count != 1:
        raise SystemExit("could not identify the canonical keyword block")

    text = text.replace(r"\bibliographystyle{plain}", r"\bibliographystyle{SageH}", 1)

    output_dir.mkdir(parents=True, exist_ok=True)
    output = output_dir / "main-swj.tex"
    output.write_text(text, encoding="utf-8")

    required = ("sagej.cls", "SageH.bst")
    for name in required:
        candidate = template_dir / name
        if not candidate.is_file():
            raise SystemExit(f"missing Sage template file: {candidate}")
        shutil.copy2(candidate, output_dir / name)

    shutil.copy2(source.parent / "references.bib", output_dir / "references.bib")
    for relative in ("generated", "benchmark/generated"):
        destination = output_dir / relative
        if destination.exists():
            shutil.rmtree(destination)
        shutil.copytree(source.parent / relative, destination)
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, default=Path("paper/main.tex"))
    parser.add_argument("--template-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument(
        "--class-options",
        default="Afour,sageh,times",
        help="sagej class options (default: published-style two-column A4)",
    )
    args = parser.parse_args()
    output = stage(
        args.source.resolve(),
        args.template_dir.resolve(),
        args.output_dir.resolve(),
        args.class_options,
    )
    print(f"SAGE_STAGING_OK\t{output}")


if __name__ == "__main__":
    main()
