#!/usr/bin/env python3
"""Verify venue-facing manuscript structure independently of LaTeX success."""

from __future__ import annotations

import argparse
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
REQUIRED_BASELINES = (
    "Konclude", "HermiT", "JFact", "Openllet", "MORe", "ELK", "Whelk",
    "Sequoia",
)
REQUIRED_SECTIONS = (
    "System architecture",
    "Evaluation",
    "Methods: how KM was developed",
    "Methods: Lean as an integration constraint",
    "Related work",
    "Limitations and threats to validity",
    "Reproducibility and availability",
)


def one_block(text: str, environment: str) -> str:
    matches = re.findall(
        rf"\\begin\{{{re.escape(environment)}\}}(.*?)"
        rf"\\end\{{{re.escape(environment)}\}}",
        text,
        flags=re.DOTALL,
    )
    if len(matches) != 1:
        raise ValueError(f"expected one {environment} environment, found {len(matches)}")
    return matches[0]


def plain_words(tex: str) -> list[str]:
    tex = re.sub(r"%.*", " ", tex)
    tex = re.sub(r"\\(?:cite|ref|label|href)\{[^}]*\}(?:\{([^}]*)\})?",
                 lambda match: match.group(1) or " ", tex)
    tex = re.sub(r"\\[A-Za-z@]+\*?(?:\[[^]]*\])?", " ", tex)
    tex = tex.replace("{", " ").replace("}", " ").replace("~", " ")
    return re.findall(r"[A-Za-z0-9]+(?:[.'+-][A-Za-z0-9]+)*", tex)


def verify(text: str) -> dict[str, int]:
    abstract_words = len(plain_words(one_block(text, "abstract")))
    if not 150 <= abstract_words <= 250:
        raise ValueError(f"abstract has {abstract_words} words; expected 150--250")

    keyword_match = re.search(
        r"\\noindent\\textbf\{Keywords:\}\s*(.*?)(?=\n\n|\\section)",
        text,
        flags=re.DOTALL,
    )
    if keyword_match is None:
        raise ValueError("keyword line missing")
    keywords = [item.strip() for item in keyword_match.group(1).split(";") if item.strip()]
    if not 3 <= len(keywords) <= 7:
        raise ValueError(f"found {len(keywords)} keywords; expected 3--7")

    sections = re.findall(r"\\section\*?\{([^}]+)\}", text)
    missing_sections = [section for section in REQUIRED_SECTIONS if section not in sections]
    if missing_sections:
        raise ValueError(f"required sections missing: {', '.join(missing_sections)}")

    evaluation_start = text.find(r"\section{Evaluation}")
    methods_start = text.find(r"\section{Methods: how KM was developed}")
    if evaluation_start < 0 or methods_start <= evaluation_start:
        raise ValueError("evaluation and methods sections are not in the expected order")
    evaluation = text[evaluation_start:methods_start]
    missing_baselines = [name for name in REQUIRED_BASELINES if name not in evaluation]
    if missing_baselines:
        raise ValueError(f"evaluation omits baselines: {', '.join(missing_baselines)}")

    for statement in (
        "Ethical considerations", "Author contributions",
        "Declaration of conflicting interests", "Funding", "Data availability",
    ):
        if rf"\paragraph{{{statement}.}}" not in text:
            raise ValueError(f"declaration missing: {statement}")

    forbidden = ("[TO COMPLETE", "[TO VERIFY", "still running at this manuscript cutoff")
    found = [marker for marker in forbidden if marker in text]
    if found:
        raise ValueError(f"unresolved manuscript markers: {', '.join(found)}")

    author_confirmations = text.count("[TO CONFIRM BEFORE SUBMISSION:")
    if author_confirmations > 2:
        raise ValueError(
            f"expected at most two author-confirmation markers, found {author_confirmations}"
        )
    return {
        "abstract_words": abstract_words,
        "keywords": len(keywords),
        "sections": len(sections),
        "baselines": len(REQUIRED_BASELINES),
        "author_confirmations": author_confirmations,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manuscript", type=Path, default=ROOT / "main.tex")
    args = parser.parse_args()
    result = verify(args.manuscript.read_text(encoding="utf-8"))
    print(
        "MANUSCRIPT_CONTRACT_OK"
        f"\t{result['abstract_words']} words"
        f"\t{result['keywords']} keywords"
        f"\t{result['baselines']} baselines"
        f"\t{result['author_confirmations']} author confirmations pending"
    )


if __name__ == "__main__":
    main()
