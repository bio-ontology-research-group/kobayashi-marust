---
name: project_km_hermit_konclude_port
description: 2026-06-19 best-of-HermiT+Konclude port to crack the disjunction family — mechanisms built (M1/M3/M6) but empirically inert; family splits by expressivity (only 5303 is HT-fragment).
metadata: 
  node_type: memory
  type: project
  originSessionId: 17d1eba9-eaa6-4268-97ae-40756c219352
---

2026-06-19: User goal — fully implement the best of HermiT + Konclude (absorption
+ model-based classification) in KM to SOLVE the live ∀+⊔ disjunction family
(5303/10702/1603/12653/9540/15672/6934). Strategy (user-directed): first make
EVERY ont solvable by SOME config (routing deferred — added `KM_HT_FORCE` to
bypass the soundness routing guard for algorithm testing), then generalize routing
from structural properties AFTER all solved. Lean re-cert deferred to the very end.
Sweeps must report avg AND median time/mem (improve averages, not just failures).

**Built + committed (all sound, gated OFF, build green + 111 tests):**
- M1 trigger-keyed binary absorption `trigger_absorb` (KM_HT_TRIGABS, e7bdc12):
  ⊤ ⊑ ¬C1⊔…⊔¬Ck⊔rest → C1⊓…⊓Ck ⊑ rest. In Ht::new.
- M3 global common-disjunct harvest `harvest_global` (KM_HT_HARVEST, 83466c4):
  for ⊤ ⊑ d1⊔…⊔dk inject ⊤ ⊑ x for x in ⋂ definite(di), reusing QoSat's sound
  saturation (label_pos), not its residue test.
- M6 pairwise blocking `compute_blocked` mode 3 (KM_HT_BLOCK=3, 83466c4):
  (core-label(n), core-label(pred), pred→n edge roles).
- KM_HT_FORCE in race.rs spawn_ht: bypass ht_routable for algorithm testing.

**DECISIVE empirical findings (ws, the binary needs glibc; build on ws OR IBEX —
ws binary is GLIBC_2.39, incompatible with IBEX, so build on IBEX for IBEX runs):**
1. **All planned HT mechanisms are INERT/counterproductive on 5303** (the only
   HT-fragment family member): M1 absorbed=0 (positive exclusive disjuncts Q6∨DNA,
   nothing to move to body); M3 harvested 1 global fact (exclusive disjuncts share
   no consequences); M6 pairwise folds WORSE than subset (2173 vs 753 nodes — the
   parent+edge criterion can't match disjunction-choice nodes). Existing CDCL flags
   (KM_HT_LEARN/NEGTRIED/RESTART) inert too — **conflict learning is BROKEN**:
   no-goods are keyed on ephemeral (node, node_uid) that are destroyed+recreated on
   rollback, so learned_bcp never refires (learn_clause hypertableau.rs ~2650).
2. **5303's bottleneck is raw per-test branching search**: hard concept = 674 nodes
   / 18k branch_pushes / 14.8k backtracks (2/3 CHRONOLOGICAL, only 4.7k backjumps)
   on ONE concept; HermiT does the same in ~236 backtracks. The only remaining
   lever is effective per-test search (stable label/core-keyed conflict learning
   and/or dep-set precision) — deep, soundness-delicate, ~1 ont. User chose NOT to
   start this yet ("measure broad wins first").
3. **The family splits by EXPRESSIVITY** (km features + grep of the .owl):
   - **5303**: inverse=0 nominal=0 card=0 transitive=4 → ALC(H), HT-fragment. HT
     runs but per-test blows up; subset blocking also drops 1 transitive subsumption.
   - **10702**: nominal/hasValue=207, card=34, inverse=2 → CB-only.
   - **1603**: inverse=101, card=21 → CB-only.
   - **6934**: inverse=21, card=17 → CB-only.
   - **9540**: inverse=19, nominal=13, card=11 → CB-only.
   The current HT algorithm is ALC(H)Q; it CANNOT soundly handle inverse/nominals,
   and cb_to_ht DROPS them — so forcing HT on 10702/1603/6934/9540 yields a weakened
   approximation, never gold-clean. They are CB-engine territory (the original
   disjunctive-context blowup), NOT HT. Confirms [[project_km_config_union]]:
   existing CB configs already reach 572/587; this family is in the never-pass 15.

**So "solve the family" = TWO separate major efforts:** (a) 5303 → deep HT per-test
search (stable-keyed learning); (b) 10702/1603/6934/9540 → CB disjunctive-blowup
fix (the long-standing hard CB problem). The planned absorption/harvest/blocking
mechanisms do NOT reach any family ont.

**All-on sweep VERDICT (job 47650509, 2 arms, authoritative ore_canon):**
default=564 clean / 0 unsound / 0 incomplete (wall mean 16.8s/median 0.54s; mem
mean 857/median 79 MB). all-on (KM_HT_FORCE+race+TRIGABS+HARVEST+CONTRA)=557 clean
/ 4 unsound / 8 incomplete — net **-7**: +1 (4205) -8 regressions. Isolation:
- **M3 harvest_global is UNSOUND** (NOT M1): 9024 M1-only=CLEAN(908); 9024
  M3-only=462/908 (12 unsound, 458 incomplete); 4205 M3-only=CLEAN(366450,
  recovered). Root cause: harvest uses QoSat `label_pos`, a SHARED-MODEL
  over-approximation (all concept seeds coexist → definite(di) contaminated by
  other concepts' facts) — fine for subsumer pruning, UNSOUND for deriving ⊤⊑x.
  A sound harvest needs isolated per-disjunct saturation (non-trivial). 4205's
  recovery via the buggy harvest is UNRELIABLE (coincidentally clean).
- M1 trigabs: sound on 9024, inert on 5303 (absorbed=0). Keep gated.
- The -8 regressions were M3 (unsound) + force-off-fragment, NOT M1.
**Bottom line: no bankable sound corpus win from M1/M3/M6.** M3 (83466c4) commit's
"sound" claim is WRONG — gate stays OFF; fix needs isolated saturation or drop.
The family still needs the deferred deep work (5303 per-test search; CB blowup).

**DEFINITIVE (max-config probe job 47653750):** force+TRIGABS+HARVEST+CONTRA+race
on the 22 hard timeouts → **0 solved gold-clean.** 21/22 still timeout; 10908 = ok
but garbage (86 vs gold 6001, off-fragment forced-HT). Also: M3-harvest-only
FALLBACK sweep (47652421) = 565 clean, **0 recoveries / 0 regressions** (harvest is
neutral in fallback because HT is nice'd/CB-preferred; its speedup needs HT-priority
race mode + routing). 4205 is NOT a hard ont — it's borderline-240s (clean in base).
CONCLUSION: the planned best-of-HermiT/Konclude mechanisms (absorption/harvest/
pairwise-blocking/contra), in every combination, recover ZERO of the 22 hard
timeouts. M3 harvest is now SOUND (real bug fixed) but adds no coverage. The
residual genuinely needs the deferred deep work: (a) 5303 etc HT-fragment → effective
per-test search (stable label/core-keyed conflict learning; current learning inert);
(b) inverse/nominal family → CB disjunctive-blowup fix. Both major/uncertain, matching
the years-long history. Net session deliverable: 1 sound bug fix + exhaustive proof
the planned mechanisms don't crack the family. Baseline stays 564-565 / 0 unsound /
0 incomplete.

**Earlier in flight:** authoritative all-on full-corpus sweep (IBEX job 47650509, 2 arms
default vs all-on-forced-race, `km classify` + ore_canon canon_cmp.py compare to
gold + peak mem). Aggregator: /ibex/scratch/hohndor/km/allon_agg.py. NB IBEX /tmp
is node-local and `ssh dragon` load-balances login nodes — generate+consume tmp
files in ONE ssh session. The deployed harness ore_runone.py drives owl_classify.py
(old orchestrator, lacks these mechanisms) — must run `km classify` directly.
