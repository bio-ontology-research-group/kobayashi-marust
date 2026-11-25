# KM system paper (arXiv preprint draft)

Full system description of Kobayashi-MaRust v1.7.0 with the benchmark
comparison (Konclude, OxidOWL, and the wider reasoner panel).

- `main.tex`, `sections/`: the manuscript. Build with `make`.
- `generated/heldout.tex`: numbers of the held-out comparison as macros.
- `references.bib`: copied from the KM methodology paper on 2026-11-25.
- Red `[...]` notes in the PDF mark numbers or statements still to be filled
  or checked against the v1.7.0 tag.

Sources: `sections/procedures.tex` and `sections/appendix.tex` are adapted
from the system description written for v1.5.3 (supplement of the methodology
paper); the other sections are written for v1.7.0 from
`docs/RELEASE-1.7.0.md`, the README and the measurement records.

OxidOWL comparison: Ibex directory
`/ibex/scratch/projects/c2014/hohndor/km/oxidowl-bench-20261125`
(runner `run_oxidowl.py`, checker `audit_oxidowl.py`); local copies of the
scripts and of the KM and Konclude records in
`/mnt/data1/leechuck/km-work/oxidowl-bench`.
