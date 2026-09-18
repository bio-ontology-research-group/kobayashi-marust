# Bounded early runtime/protocol review

This is a partial validation case, not the main benchmark result or an overall
performance claim. Selection used the first declared frozen case, MMO q000 STAR
module, after all six repetitions completed in baseline and final. No timing or
performance winner influenced selection. Slurm review51985085 copied terminal
results into isolated justification-early-case-review-v1, leaving live runs alone.

All234 extraction attempts (198 baseline,36 final KM) independently verify and
normalize to the same single logical-support family. There is no semantic
disagreement or duplicate-support inflation in this case. The39 dispersion rows
each contain exactly five measured repetitions; warmup is excluded. An independent
local recomputation matches every median, min/max, IQR and MAD and all195 eligible
paired wall-time ratios.

The renderer excludes75 incompatible comparisons:45 common-versus-library
mechanism mixtures, plus30 native-versus-library bounded comparisons where the
library exposes no enumeration-completion status. The latter are valid supports,
not reasoning errors. At bound1, a nonempty search frontier is also not an error:
first-justification timing does not claim exhaustive enumeration.

The report's matrix-complete flag applies only to this explicitly selected
234-attempt subset. Full benchmark arrays and final comparisons remain separate.
See selection.json, review-validation.json, comparison.md and evidence/ for the
scope, checks, normalized hashes and independent audit rows. Raw snapshot remains
on IBEX under dynamic-benchmark-20260917/justification-early-case-review-v1.
