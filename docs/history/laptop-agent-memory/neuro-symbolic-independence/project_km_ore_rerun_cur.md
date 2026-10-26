---
name: project_km_ore_rerun_cur
description: "ORE 2015 benchmark rerun (2026-06-08) with current payg-strategy KM binary vs reused Konclude/HermiT/Sequoia/ELK; honest coverage + correctness breakdown"
metadata:
  node_type: memory
  type: project
  originSessionId: 3e94cd1a-f3b7-4c1c-a08d-39c076fa2104
---

Reran KM on the ORE 2015 sweep with the CURRENT `payg-strategy` HEAD binary
(`kobayashi-marust-par-cur`, built locally GLIBC_2.34, copied to cluster — the
benchmark KM path is pure CB via owl_classify.py, no tableau). Reused
Konclude/HermiT/Sequoia/ELK from the original sweep. Job 4852 (30-chunk array,
592 onts, KM_THREADS=16, exclusive nodes, 240s timeout / 20GB cap). Harness:
`~/bench/ore_km_cur.sbatch` + `~/bench/ore_harness/ore_aggregate_cur.py`
(reads `ore_out_kmcur` + `res_kmcur_*.jsonl`). Report: `~/bench/ore_report_kmcur.md`.
Builds on [[project_km_reasoner_benchmark]] [[project_km_audit]] [[project_km_heap_profile]].

## cur == kmfix (no regression from e0f6e34 forward-subsumption fix)
On 106 both-ok shared onts: cur median 0.408s vs kmfix 0.463s; total wall 539.5
vs 542.3s (within 0.5%). Status transitions stable (129 timeout->timeout,
106 ok->ok, 20 error->error, 12 memout->memout); only flips are near-cap noise
incl. 1 gained solve (timeout->ok). Longer array wall-clock (~3h vs kmfix 76min)
was SLURM scheduling/node variance + a VPN drop mid-run, NOT a slower binary.

## Headline numbers
Coverage (ok / applicable): konclude 587/590, ELK 383/383 (EL only),
sequoia 336/479 (240 unsupported=nominals/dt), **hermit 239/592 (352 TIMEOUTS at
240s!)**, **km 214/592**.
Time+mem on the FAIR common-117 subset (all 5 ok), median wall / median peak MB:
konclude 0.248/22.9, **km 0.364/21.8 (lowest mem)**, elk 1.101/107.7,
hermit 1.692/198.1, sequoia 2.636/254.0. KM = 2nd-fastest, lowest memory.

## KM coverage gap is NOT soundness — it decomposes as:
- **55 "error" = frontend translator gaps** (owl_classify.py raises
  `ValueError: class: ObjectHasValue / DataMaxCardinality / DataExactCardinality`).
  33 are D+nom+inv. Missing OWL constructs in the Python OWL->clause translator,
  fixable, not an engine issue.
- **269 timeout + 54 memout = 323 = CB SIZE blow-up**, predominantly on LARGE
  PURE-LOGIC onts (213+42=255 are feature-free "-"). The architectural CB scaling
  limit (cf 47GB live-disjunction note in [[project_km_nominals_routing]]).

## Correctness: the "10-12 unsound vs konclude-gold" is mostly soft
12 flagged unsound; 8 are datatype onts (ALEHIF+(D)/SHIF(D)) — unsupported feature,
over-approximation. Cross-checked the 4 NON-datatype cases vs HermiT:
- **5940 (ALCH), 8135 (ALEH): KM = HermiT EXACTLY (0 extra); KONCLUDE is the
  outlier** (12 / 16 extra vs HermiT). KM not unsound — gold disagrees w/ HermiT.
- **6720 (ALCO): no konclude/hermit sig — spurious flag.**
- **3978 (ALEH+, no dt/nom): KM has 14 extra vs BOTH konclude AND hermit (which
  agree, 824 each). THE one genuine in-fragment discrepancy — INVESTIGATE.**
Gold itself unreliable: HermiT vs Konclude differ on 12/239 onts.
18 "incomplete" not yet investigated.

## ore_ont_3978 ROOT-CAUSED + FIXED (2026-06-08, commit c03bc78)
The one in-fragment unsound case was a FRONTEND bug, not engine/calculus:
`frontend.short()` mapped an IRI to its fragment, so two DISTINCT part_of IRIs
(`.../OBO_REL#part_of` in the class defs vs `.../obo#part_of` in the role
hierarchy) collapsed to one internal role `part_of`. Then `surrounds ⊑ obo#part_of`
wrongly applied to the OBO_REL part_of -> 14 spurious GO subsumptions (838 vs gold
824). Fix: collision-safe `short()` with a per-ontology IRI->name registry (reset
in `ofn_to_clauses`); unique local names returned unchanged so all 23 fixtures are
byte-identical (no cert re-gen needed — Lean cert covers the calculus, not IRI
naming). Result: 838->824 = HermiT = Konclude. Got the ontology WITHOUT cluster
(remotezip range-fetch from Zenodo rec 18578) + reproduced with local KM binary.
Proof: `docs/ore_ont_3978-iri-collision.demo.md` (showboat, `verify` passes).
NOTE: cluster benchmark used the OLD frontend, so its 3978 numbers still show 838;
the fix likely also helps some of the 8 datatype "unsound" + some "incomplete"
onts (same collision mechanism on classes), not yet re-measured.

## 55 frontend "errors" RESOLVED (2026-06-08, commit 1e2f39c)
Categorized: 30 ObjectHasValue-first (already handled in current repo frontend;
cluster had a STALE deployed copy ~/bench/km/py) + 25 Data*-first. Of the 30, 25
ALSO use datatypes -> only 5 datatype-free (cleanly recoverable). So 50/55 are
datatype onts. Fix: added `frontend.OutOfFragment`, raised for the Data* family in
BOTH `cls()` (was bare ValueError crash) and `add_axiom` (was SILENTLY skipped =
silent incompleteness); `owl_classify` catches it -> prints "unsupported: ..."
exit 3. KM now declines datatype onts like Sequoia. Deployed current engine/py to
cluster ~/bench/km/py (backup py.bak.*) + re-ran the 55 (job 4884): result
**0 crashes** -> 50 unsupported, 3 ok (15672/5107/5184), 2 timeout (12698/9540
nominal+inverse heavy). Matches estimate (5 datatype-free reach the reasoner).
23 fixtures unaffected. KNOWN GAP left: add_axiom still silently skips
NON-datatype unknown axioms (e.g. DisjointObjectProperties) -> may feed the 18
"incomplete" bucket; not changed to avoid regressions.

## TODO
- Investigate the 18 "incomplete" onts (some may be the add_axiom silent-skip of
  DisjointObjectProperties etc.; some the datatype/collision mechanisms).
- Optionally re-run the FULL ORE sweep with current frontend for an honest
  coverage table (error 55->0; +3 ok, +50 unsupported, +2 timeout; plus 3978 fix).
- ore_km_cur.sbatch + ore_aggregate_cur.py only on cluster — copy into repo
  oracle/ore/ for reproducibility ([[feedback_commit_push]]).
