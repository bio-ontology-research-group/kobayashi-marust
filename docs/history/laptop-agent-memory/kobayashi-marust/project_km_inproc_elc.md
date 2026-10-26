---
name: project-km-inproc-elc
description: 2026-07-06 in-process elc fast path — small EL-safe onts skip the portfolio-race worker forks (byte-identical, sound); targets the 155 lighter-but-slower onts in the beat-Konclude speed band
metadata:
  type: project
  originSessionId: 35856588-304b-4786-a05c-4b601119991f
---

2026-07-06. Landed the **in-process elc fast path** (orchestrate/mod.rs,
`try_inproc_elc` + `INPROC_ELC_MAX=4MB` + `KM_NO_INPROC_ELC` opt-out),
pushed on payg-strategy.

**Why (from the 48105343 baseline win-band analysis):** km wins memory on
the median (0.63x) and 64% of ORE but loses speed on 63% (median 1.30x).
The near-term WIN band = **155 onts km already runs LIGHTER but slower**
(fixing speed flips them to a full WIN); only 1 the other way. 118 of the
155 are within 2x speed, 61 within 1.2x — the top loses by <1ms on trivial
~0.1s onts. KM_TIMING on trivial onts (ws) found the cause: **km forks the
HT worker (spawn_ht) AND the CB engine on EVERY ont**, even when CB fills
the slot in 0.02s and wins. On the loaded 192-core benchmark node (workers
oversubscribe km's 16-cpu allocation) those wasted forks are the contention
that ties/loses the trivial band to Konclude's single clean process.

**The fix (the RIGHT kind — eliminate the fork for a provable subset, NOT
re-time the race):** for small el_rbox_safe onts, call
`elcomplete::classify` as a LIBRARY function; when it fully certifies, use
its answer and SKIP the portfolio race entirely (no CB/HT/elc-cert forks).
Equivalent to the trusted non-portfolio bare-elc branch, so sound+complete
for exactly the onts elc certifies; `classify`→None (not EL) falls through
unchanged. Byte-identical to the subprocess elc (same ElResult→EngineOut
fields, same BTreeMap serialisation) — **validated 15/15 onts identical
with vs without KM_NO_INPROC_ELC, 0 DIFF** (11 took the in-process path, 4
non-EL fell through). 1399 tests green.

**Contrast with the DEAD-ENDS in [[project_km_beat_konclude_gap]]:** lazy-HT
(500ms grace, -29), CB-first-reorder (noise), lazy-elc (x2) all RE-TIMED
the race and failed. This change is structurally like the in-process
FRONTEND (+47, real) — it removes the fork for a provable subset. Whether
it moves WIN reliably is being measured: IBEX paired panel (konclude+km,
job 48107467, cmp_res_inproc) vs baseline WIN=213. IF it lands within noise
(±25) it is still a correct simplification with 0 risk (byte-identical);
IF it flips a chunk of the 118 near-tie EL onts it is a real gain. Result
pending.

Build/deploy: rsync laptop engine/src → ibex:/ibex/scratch/hohndor/km/
engine/src, `sbatch build_all.sbatch` (touches src for mtime, builds all 5
binaries into target/release). Panel: reasoner_cmp_inproc.sbatch (copy of
reasoner_cmp.sbatch, REASONERS="konclude km", cmp_res_inproc/cmp_out_inproc).
