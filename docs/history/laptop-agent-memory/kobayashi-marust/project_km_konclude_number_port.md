---
name: project_km_konclude_number_port
description: 2026-06-26 faithful full Konclude SHIQ number-restriction port into KM's Ht — the disjunction-family wall is cardinality non-folding, plan + architecture gap
metadata:
  node_type: memory
  type: project
  originSessionId: 666845f8-0818-4d3e-8e4f-a3e9496633db
---

User directive (2026-06-26, emphatic): "implement the Konclude route in KM! No
shortcuts! Full Konclude algorithm faithfully reproduced in KM's Ht!" Target =
the disjunction family. PORT from Konclude, do not invent. See [[feedback_port_from_konclude]].

**MEASURED root cause of the disjunction-family wall (this session, ws):**
The open family members are NOT blocked by routing or inverse-soundness. Expressivity
from the cb_to_ht TIN dump (KM_DUMP_TIN): **1603** = inverse=false nominals=0
number=true (ALCHQ, 2937 cl, 349 q); **12653** = inverse=false nominals=0 number=true
(ALCHQ, 596 cl, 21 q); **9540** = nominals=86 number=true. The decisive test:
`km tableau` on 12653 with EAGER+NEGTRIED **but NO cardinality flags** FINISHES <30s
(consistent:true, 10 subs, model folds). WITH KM_HT_NUMBER+KM_HT_QMERGE it explodes
to **12365+ nodes, 99% blocked, non-folding → timeout**. 1603 → 17182 nodes, 9540 →
46252 nodes, all 99% blocked, all timeout. ⇒ the wall is KM's CARDINALITY handling
(the QMERGE shortcut: multi-Eq bails, ∃-successors over-counted, no choose rule), NOT
the disjunctions and NOT the search per se. The disjunction+blocking machinery already
folds fine (5303/9024/12141/541 solved via EAGER+NEGTRIED+mode-3, in-fragment).

**Architecture gap (why a faithful port is non-trivial):**
KM has NO first-class ≥n/≤n concept in Ht. The frontend AST (`syntax.rs:32-33`) HAS
`AtLeast(n,Role,Concept)`/`AtMost(n,Role,Concept)`, but `normalise.rs:455-540`
CLAUSIFIES them into grounded pigeonhole clauses: ≤n → `r(x,y1)∧…∧r(x,y_{n+1}) ∧
[distinct] → ⋁ Eq(yi,yj)`; ≥n → `Body → ∃r.C` ×n + distinctness. cb_to_ht passes
the Eq-head clauses through (`cb_to_ht.rs:439-492`, sets number=true). Ht's current
scheme (`hypertableau.rs` apply_head ~1295): Eq-head ⇒ union-find `merge_into`
(~838) with `MergeDisj`/`push_card`/`branch_merge` (~6683) branches under
KM_HT_QMERGE. This is KM's OWN encoding, not Konclude's rules — and it does not
fold. This is the SHORTCUT the user wants replaced.

**Faithful port plan (Konclude rules on first-class cardinality concepts):**
1. Carry ≥n/≤n into Ht as first-class restrictions. Cleanest non-disruptive route:
   frontend `--meta` emits a structured cardinality list (trigger body → kind,n,role,
   filler); allocate a fresh internal concept id per distinct (kind,n,r,c); emit
   clause `body → card_concept(x)` + side-table card_concept→(kind,n,r,c). CB clause
   stream UNCHANGED (preserves CB byte-identity); only meta gains a field. cb_to_ht
   reads it into the TInput. (Alt: reconstruct from grounded clauses in cb_to_ht —
   fragile, avoid.)
2. Implement Konclude's rules (from CCalculationTableauCompletionTaskHandleAlgorithm.cpp):
   - **applyATLEASTRule** (:16066): ≥n r.C ⇒ create n r-successors each with C,
     pairwise DISTINCT (inequality/CDistinctEdge); refire-guard on existing distinct
     C-successors.
   - **applyAutomatChooseRule** (:9553): for ≤n r.C, label each r-successor C or ¬C
     (branch) so counting is exact.
   - **applyATMOSTRule** (:14859): count r-successors with C; >n ⇒ non-deterministic
     branch picking WHICH pair to merge; if the >n successors are all pairwise
     distinct (inequality) ⇒ CLASH (not merge). NN-rule for ≥/≤ interaction.
   - **mergeIndividual** (:20979): label union + edge re-target + distinct-edge
     propagation + dep union; clash if merged pair was asserted distinct.
   - Distinct/inequality edges + clash. Pairwise blocking mode-3 already exists
     (sound for SHIQ).
3. Gate behind a flag; UNIT-TEST each rule with small synthetic onts FIRST
   (see [[feedback_build_before_benchmark]] — do NOT run hard ORE onts mid-build).
   Then validate 12653→1603→9540 vs Konclude gold (sound+complete).

**IMPLEMENTATION PROGRESS (2026-06-26, uncommitted on ws + laptop, all gated KM_HT_CARD default off):**
- Increment 1 DONE+tested: distinct/inequality edges (`Ext.distinct`, `Trail::Distinct`,
  `add_distinct`/`are_distinct`, merge-on-distinct CLASH + distinct-propagation in
  `merge_into`). 4 unit tests (distinct_pair_merge_clashes, distinct_self_is_clash,
  distinct_backtrack_undoes_then_mergeable, distinct_propagates_through_merge).
- Increment 2+3 DONE+tested: first-class `CardDef{kind,n,role,filler}` + `card_defs`
  HashMap on Ht + `set_card_defs` + `card` flag; recognition hook in `propagate`
  Event::Concept; `≥n` = `CardReq` in `Ext.card_min`, processed in
  `process_card_min` (BLOCKING-GATED like ∃ — the fix for non-folding) with
  `distinct_filler_succ` refire guard. 3 tests incl. recursive A⊑≥1R.A blocking-fold.
- Increment 4 DONE (testing): `≤n` = `card_max` list, `card_max_step` at `Scan::Sat`
  (choose first unqualified succ via `branch_choose`; else >bound qualified: clash if
  all pairwise-distinct, else `push_card`+`branch_merge` over mergeable pairs). 4 tests.
- INCREMENT 5 DESIGN (next session, not yet started). Goal: feed `card_defs` for
  real onts + suppress the clausal pigeonhole. Pipeline findings:
  * Frontend clausifies in `normalise.rs::define(q,c)` (q = fresh marker name for the
    AtLeast/AtMost concept c). ≥n arm (:455): `q→r(x,f_i(x))`, `q→C(f_i(x))` ×n +
    distinctness `q∧Eq(f_i,f_j)→⊥`. ≤n arm (:509): one Eq-head clause body
    `[q, r(x,y0),C(y0),…,r(x,yn),C(yn)]` → head `[⋁Eq(yi,yj)]` (+Q recog).
  * cb_to_ht (`cb_to_ht.rs`): ≤n lives in the `eq_clauses` loop (:439-495, sets
    number=true on Eq head) — RECOGNIZABLE by shape (all-Eq head + body q+role/filler
    pairs; n = #role atoms − 1). ≥n lives in the MAIN clause loop as Skolem
    existentials — the n distinct `q→∃r.C` get deduped to ONE successor (has_rsucc),
    which is WHY ≥n is broken; count lost in Skolem→∃ conversion.
  * RECOMMENDED ROUTE (robust, avoids fragile ≥n Skolem grouping): collect
    `(marker q, kind, n, role, filler)` in the FRONTEND `define` arms (it has the
    exact data) into a new `cardinalities` meta list, AND tag the cardinality
    EXPANSION clauses (the ones define() emits for the ≥n/≤n body of q) so cb_to_ht
    can DROP exactly them (not all body-q clauses — q may appear in an enclosing
    concept's recognition body). Keep the `A→q` head clauses (assert the marker).
    cb_to_ht: map marker/role/filler names→ids, build `CardDef` map, `set_card_defs`,
    drop tagged clauses, set number=false for those. CB clause stream UNCHANGED
    (byte-identity preserved — meta-only addition). Gate the whole thing behind a
    frontend flag so default output is byte-identical.
  * CAVEAT (still holds): a restriction must reach Ht via EXACTLY ONE of {card_defs,
    clausal Eq/∃} — never both (else card_max_step AND the Eq-merge both fire).
  * Then increment 6: validate 12653→1603→9540 HT-forced+KM_HT_CARD vs Konclude gold
    (sound+complete), expect folding (no 12k-node blowup). Onts on ws:/tmp/*.tin.

**INCREMENT 5+6 DONE + VALIDATED (2026-06-26, uncommitted, gated KM_HT_CARD):**
The faithful number port now classifies the cardinality wall members GOLD-EXACT
and FOLDING. End-to-end pipeline wired:
- Frontend (`normalise.rs::define`): under `KM_HT_CARD` env, each ≥n/≤n (and the
  ≤n recognition proxy NQ ≡ ≥(n+1)) pushes a `json_io::CardMeta{marker,min,n,role,
  filler}` to `hooks.cardinalities`. Clause stream UNCHANGED (the pigeonhole is
  still emitted); only meta gains the field, `#[serde(skip_serializing_if=empty)]`
  ⇒ flag-off output byte-identical. VERIFIED on ws: clauses_off==clauses_on (minus
  the field) on 12653/1603/9540, off has no `cardinalities` key. Threaded via
  GroundHooks→FrontendResult→OfnClausesOnly/OfnOutput (cli.rs) + JInput (json_io).
- cb_to_ht (`convert`, new `cardinalities` param; callers km.rs/race.rs×2): when
  `card_active` (KM_HT_CARD + non-empty), `card_drop()` removes EXACTLY the 3
  clausal shapes per marker (≥n Skolem intro `body=[m(x)]`+fun head; ≥n
  distinctness empty-head+m+Eq-fun-pair; ≤n all-Eq head+max-marker body) and
  builds `TInput.card_defs:Vec<CardDefJson{marker,min,n,role,filler}>` (ids via
  cid/rid). emelim DISABLED under card (it would fold the q/NQ complementary pair).
  12653 596→425 cl / 54 defs; 1603 2937→2705 / 18; 9540 924→756 / 20.
- HT (`tableau.rs` run_json: TInput gains `card_defs:Vec<JCardDef>`; inside the Ht
  thread after set_number → `ht.set_card_defs_raw(&[(C,bool,u32,R,C)])`, the new
  pub shim building `HashMap<C,CardDef>`). Reached via KM_HT_FORCE (number=true).
- RESULT (ws, KM_HT=1 KM_HT_FORCE=1 KM_HT_CARD=1, vs Konclude gold w/ iri_map
  localname mapping): **12653 MATCH 10/10 (201 nodes, was 12365), 1603 MATCH
  1988/1988 (206 nodes, was 17182), 9540 MATCH 66/66 (64 nodes, was 46252)** —
  all consistent, 0 unsound, 0 incomplete, fold instantly (97%/92% blocked). The
  cardinality-non-folding wall is BROKEN for these three.
- 16 card/distinct unit tests pass; build clean (CardDef-privacy = pre-existing
  warning, harmless). NB raw `km tableau` output keys subs by cb_to_ht concept
  names incl. `X__<ont>.owl` import-disambiguation suffixes; must map via meta
  iri_map→localname before gold-compare (else false 'unsound', e.g. 1603 Foot vs
  Foot__gwsg.owl). cmp_gold2.py on ws:/tmp does this.

**ROUTING WIRED (2026-06-26, uncommitted):** `config.rs` `ht_card` flag
(KM_HT_CARD master switch, default off). `race.rs spawn_ht` `card_candidate` =
ht_card && !card_defs.empty && dropped==0 && fenced empty && !inverse &&
nominals empty && !datatype; computed FIRST so it takes PRECEDENCE over
qo_candidate/shoq_candidate (a card ont may carry inert inverse bridges → QO would
also fire, but QO's apply_head PANICS on the kept cardinality recognition Eq-heads
— "Eq s bound" at hypertableau.rs:4990). Card route sets worker env
KM_HT_FORCE+KM_HT_CARD+KM_HT_PAR=1 (single-threaded: card rules carry shared
distinct/merge state), excluded from the all-cores KM_HT_PAR override + fast_certify
(uses full CB budget → max CB-preference). cb_to_ht `card_active` ALSO gated on
`card_routable` (no __dt__/__nom__ atoms) so datatype/nominal onts KEEP the
pigeonhole + emit NO card_defs (else they route to QO/shoq/CB and lose the
cardinality / panic QO). run_json belt-and-suspenders: install card_defs only when
KM_HT_QO unset. **GOTCHA: under KM_HT_CARD the frontend emits cardinalities for ALL
number onts and cb_to_ht drops the pigeonhole for card-ROUTABLE ones only — a
datatype number ont (12653 has 116 __dt__ atoms) must NOT card-transform (no Ht
datatype oracle) → falls back to QO/CB.**

**VALIDATED end-to-end (ws):** `km classify` KM_HT_CARD=1 fallback (KM_HT_BUDGET_S=8):
1603 GOLD-EXACT 1988/1988 via the real orchestrator (card arm, 0 panics); 12653
(datatype) falls back cleanly NO PANIC (still timeout, not a regression). 170 cargo
tests pass; default-OFF byte-identical (no `cardinalities` key, clauses unchanged).

**COMMITTED 2026-06-27 (commit 70f8573, gated KM_HT_CARD, default OFF, byte-identical
when off, 170 tests):** the card port. cb_to_ht convert() now takes explicit
`card_enabled` bool (not env). card_active gated on `card_routable` (no __dt__) AND
`!has_inverse` (rbox-based; NB rbox=None in spawn_ht so inert there — inverse is
detected clause-side by has_inverse_bridge in race). card_candidate now ALLOWS
nominals (SHOQ); fast-certify arm (harvests at shoq_budget ~20s, not 225s).

**SWEEP VERDICTS (2026-06-27, definitive, full 587-ont card-on sweep @8thr, commit
20fa4f5 results/benchmarks/2026-06-27-cardsweep): 564 ok / 12 timeout / 2 incomplete,
0 UNSOUND. median wall 0.90s, median peak 88MB. Card closes THREE (all confirmed
card-OFF timeout -> card-ON ok at the SAME 8-thread config):**
- **1603 = CLOSED** (20.5s 2.3GB, SHQ).
- **7499 = CLOSED** (79s 18GB, SHQ; was never-pass in ANY prior deployed config).
- **7409 = CLOSED** (107s 3.2GB, SHOQ 18 nominals — few enough to finish).
- Real-hard not-ok (11): 541 3215 7914 9540 9663 9724 10702 12653 12698 14817 16444.
  Contested (3): 2669 15516 10621.
- **9540 = NOT closed.** card route IS taken (card_defs in TIN, 20 defs) + folds
  (66/66 forced, 64 nodes) BUT the production classify runs 50 per-concept SAT tests;
  with 86 nominals each is heavy → single-threaded TIMEOUT, all-cores PAR TIMEOUT too
  (4:00, 18GB peak). Needs GLOBAL/incremental classification (one model, read subs off)
  with card+nominals, NOT 50 rebuilds. Open.
- **10702 = NOT closed.** inverse=FALSE (it's SHOQ not SHOIQ!), card route taken but
  incomplete=23 unchanged — its incompleteness is disjunction+nominal, not cardinality.
- **CARD-ON REGRESSIONS ARE THREAD ARTIFACTS:** the 2-thread sweep showed 7 regress
  (9635/10750/13482/14042/15059/15803/16303) + "10702 unsound"; ALL vanish at
  KM_THREADS=8 (every one ok/ok; 10702 unsound was nondeterminism). Cause: card spawns
  an HT racer → ht_reserved_threads steals 1 CB thread → at 2 threads CB starves. At
  production thread counts the global card flag is CLEAN (0 regress/unsound).

**PARALLEL-CLASSIFY SOUNDNESS BUG FOUND + FIXED (UNCOMMITTED, hypertableau.rs
classify_parallel):** the per-thread workers did `Ht::new(template)` + set_anywhere
ONLY — they did NOT inherit `card_defs`/`nom_set`/`force_number`/`force_qmerge`. So a
parallel worker classified WITHOUT cardinality + WITHOUT the o-rule → wrong subsumers.
THIS is the real cause of the documented "10908 collapses to 86/6001 at PAR=8" (not a
race — workers missing the o-rule). FIX: capture those 4 from self, re-install into
each phase-1 AND phase-2 worker (each owns its Ht → per-thread, sound). VALIDATED on
unimatrix: 10908 PAR=8 now 6001/6001 (was 86/6001), 1603 PAR=8 1988/1988. 9540 PAR=8
becomes CORRECT but SLOW (workers now do full card+nominal → timeout; the earlier
"9540 PAR=8 20s 66/66" on the unfixed binary was card-SKIPPING = unsound-but-lucky).
Route relaxation (card all-cores) REVERTED (9540 doesn't close + oversubscribes sweep);
card stays PAR=1, propagation fix kept as latent soundness fix. Commit pending build
b7efgplqf + final mem/time sweep with km-card6.

**Files (committed 70f8573):** json_io.rs, frontend/{normalise,mod}.rs, cli.rs,
orchestrate/{cb_to_ht,config,race}.rs, bin/km.rs, tableau.rs, hypertableau.rs.
**Uncommitted (propagation fix):** hypertableau.rs classify_parallel. Binaries on
unimatrix ~/cardsweep/km-card{3,4,5}; km-card5=route-relaxed (don't deploy).
