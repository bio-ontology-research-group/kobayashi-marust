Bridge clause translation (KM_NO_SOURCE_TBOX=1): measurements, 2026-10-29
=========================================================================

Branch fix/v155-bridge-clause-path, forked from development/v1.5.4 at
9cf7c2cd. "before" = km built from 9cf7c2cd; "after" = km built from the fix
commit (337688ba).

Seeds: the 700 nominal-free ALCHIQ generator inputs and HermiT 1.4 answers
from 2026-10-28 (.work/agent-assets/2026-10-28-scratch/bridge/{seeds,gold};
seeds 1-300 under .../sq). Harness: results/agents/2026-10-28/bridge/eval.py
(60 s per seed, 8 parallel workers, ws). Verdicts: ok, WRONG(...) against
HermiT, ERR (no answer: timeout or worker crash), DEFER (bridge-only route
declined), hermit-error (no gold).

  seeds_{before,after}_auto_clause.txt    automatic route, KM_NO_SOURCE_TBOX=1
  seeds_{before,after}_auto_source.txt    automatic route
  seeds_{before,after}_bridge_clause.txt  --route ht_bridge, KM_NO_SOURCE_TBOX=1
  counts.tsv                              verdict counts of the six files
  site_attribution.txt                    which encoder site each failure needs
  causes.txt                              cause list and minimal examples
  auto_clause_path_inputs.tsv             inputs without class axioms
  corpus_times.tsv, corpus_compare.tsv    ORE regression check (top10 + flips)
  cb_incomplete_inverse_top.{ofn,hermit.json}  separate CB-engine finding

The 2026-10-28 measurement reported 235 clause-path failures (fixD_clause.txt).
The 9cf7c2cd binary measured here fails 302 on the same seeds and harness;
the difference was not investigated.
ERR in the auto files includes transient worker start failures (EAGAIN,
"Resource temporarily unavailable") when other jobs share the machine; the
remaining ERR seeds on the clause path after the fix are timeouts (189, 211,
285, 490, 588; 285 and 490 also time out on the source path).
