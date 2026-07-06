# Solved ontologies: the playbook

How each once-failing ORE 2015 ontology was diagnosed and solved, in enough
detail to reproduce the reasoning and to apply the same mechanism to the next
ontology of its family. Newest first within each section. Gold = Konclude,
except where HermiT/ELK consensus shows Konclude is wrong (see
`CONTESTED-GOLD.md`); an ontology KM solves correctly counts as solved even if
Konclude fails on it.

Companion docs: `../CHANGELOG.md` (result tables per change),
`../engine/src/konclude_ht/STATUS.md` (port state), `PERF-LEDGER.md`.

---

## Solved via the konclude_ht bridge (Konclude's algorithm in Rust)

### ore_ont_12653 — path/universe QCR ontology (2026-07-06, `d64e78b`)

- **Symptom**: production km times out (240 s). Family: disjunction +
  qualified cardinality.
- **Diagnosis path**: `bridge_scale_probe` showed the bridge terminates each
  subject in ~8 ms (33 nodes, 4 backtracks) but full classify derived 0/10
  gold pairs with `unsupported=103` clauses dropped. `KM_BRIDGE_DUMP_UNSUP`
  categorised the drops: inverse-role axioms (`R(x,y) → S(y,x)`),
  domain/range axioms (`R(x,y) → C(x)` / `→ C(y)`), and qualified-cardinality
  pigeonhole clauses (`C(0) ∧ D(1) ∧ D(2) ∧ R(0,1) ∧ R(0,2) → eq(1,2)`).
- **Mechanisms** (all faithful Konclude ports, in `konclude_ht/bridge.rs` +
  `completion/u08.rs`):
  1. Domain/range: fill `Role::{domain,range}_linker` from the clausal forms;
     apply at EVERY link install (base role, each super-role, mirror-inverse)
     in `ht_apply_role_domain_range` — the exact
     `createNewIndividualsLink*` placement (Konclude cpp 22303–22334,
     22382–22395).
  2. Inverse-role hierarchy: `R(x,y) → S(y,x)` is `R ⊑ S⁻`; encode as a PLAIN
     super-role entry pointing at the concrete inverse-role object, closure
     over both polarities (`R ⊑ S` also yields `R⁻ ⊑ S⁻`). Never encode
     polarity in the linker's negated flag: `has_indirect_super_role`
     (the ∀-matcher) ignores it.
  3. Qualified number restrictions: `cb_to_ht::convert(card_enabled=true)`
     replaces the pigeonhole clauses with structured `card_defs`
     (`marker ⊑ ≥n/≤n R.filler`); the bridge builds CCATLEAST / qualified
     CCATMOST concepts and absorbs them onto the marker (CCSUB → AND rule).
  4. Pairwise fallback: a subject whose saturation made nondeterministic
     choices is not read-off-authoritative; each candidate subsumer is
     verified by `bridged_unsat(s ⊓ ¬sup)`, which is exact under any branch
     discipline.
- **Result**: missing=0 spurious=0 in 1.0 s (subjects=14). konclude_ht suite
  1208/1208; ore_ont_1016 read-off regression byte-identical.
- **Status**: bridge is test-only; production wiring pending.

### Read-off soundness gate (2026-07-06, follow-up to `d64e78b`)

Found while validating ore_ont_3215: the model read-off trusted
`or_backtrack_count == 0` as a determinism witness. Wrong — a drive can OPEN
OR branch points and commit to each first disjunct without ever clashing;
concepts added under those choices are branch-dependent, not consequences.
Measured: 86 spurious subsumptions on 3215. Fix: count branch-point openings
(`or_branch_open_count`); read-off is authoritative only if the drive opened
none and backtracked never. Konclude gates the same extraction on the
dependency track point's branching tag (cpp 4121); the open-count stands in
because the in-process OR adds disjuncts under the OR concept's own track
point. Nondeterministic subjects degrade to candidate extraction + pairwise
verification instead of being trusted.

**Rule for all future model read-offs: backtrack-free is NOT deterministic;
branch-open-free is.**

---

## Solved in production km (this branch, pre-bridge)

### ore_ont_10702 — wine/nominals (2026-07-05)

- **Symptom**: 23 missing FrenchWine subsumptions (incomplete).
- **Diagnosis**: `nominal_clauses` carried only the ClassAssertion half of the
  ABox; RoleAssertions between named individuals were dropped.
- **Mechanism**: add `{a} ⊑ ∃R.{b}` nomlink clauses (sound, additive).
- **Result**: 587/587 MATCH.

### ore_ont_12698 — colon-localname classes (2026-07-05, `03cdb8b`)

- **Symptom**: classes with `:` in the localname missing from output.
- **Diagnosis**: the HT arms passed an EMPTY named set to `cb_to_ht`, so
  colon-named classes were treated as internal and dropped.
- **Mechanism**: thread the real named set through. Residual 18 differences
  are gold localname collisions, not KM errors.

### ore_ont_2669, 15516, 10906 — SWRL DL-safe rules (2026-07-05, `0d20dd1`)

- **Symptom**: timeouts; gold says satisfiable.
- **Diagnosis**: the ontologies are inconsistent BECAUSE of their SWRL rules,
  which km (and Konclude's ORE config) ignored. HermiT agrees: inconsistent.
- **Mechanism**: `KM_HT_RULES` (default-on, rule-gated): ABox individuals as
  nominal nodes + rules as HtClauses in the HT arm. Inert on rule-free onts
  (14817 frontend output byte-identical).
- **Result**: correctly inconsistent in < 120 s. Counts as solved under the
  consensus-gold rule.

### ore_ont_1603, 9540, 7499 — cardinality + recognition (2026-07-05)

- **Symptom**: timeout family with `≥n/≤n` folding blowups.
- **Diagnosis**: clausal pigeonhole expansion of number restrictions explodes;
  unguarded `⊤ → Q ∨ NQ` recognition branches on every node.
- **Mechanism**: frontend CardMeta → first-class `card_defs` (`KM_HT_CARD`,
  default-on) + guarded/lazy recognition (`CARD_RECOG`). 7499's "missing
  3297" was a gold localname collision, not incompleteness.
- **Validation**: panel 48067625 clean, no regressions.

### ore_ont_541 — functional-role variant (2026-07-05)

- **Mechanism**: `KM_HT_CARD_FN` — functional data/object properties become
  first-class `≤1 R`. Validated 21 s MATCH standalone; the confirming panel
  was still pending as of 2026-07-05, and the ORE-config production route
  still lists 541 as a timeout. The konclude_ht bridge route on 541 thrashes
  (see "Diagnosed" below). Treat 541 as HALF-solved: mechanism exists, needs
  the panel + routing confirmation.

### ore_ont_5303 — deep-decision ALC+⊔ (2026-06)

- **Symptom**: timeout; decision depth 15k+.
- **Diagnosis path** (documented in `5303-ATTEMPTS.md`): conflict learning
  inert; EAGER refuted; the winning discipline was EAGER + NEGTRIED + ORD=1,
  then per-step cost elimination.
- **Mechanism**: `KM_HT_INCRBLOCK2` (incremental blocking) +
  `KM_HT_INCROBLIG` (incremental obligations), both result-identical.
- **Result**: 207 s → 5 s. Gotcha that cost 3 debug cycles: build fail-loud;
  a stale binary faked a null result.

### ore_ont_7581 — QoSat + router (2026-06, `16e6749`)

- **Mechanism**: INVCHAIN + GFCERT + short-QO-budget in the router sweep.
- **Result**: gold-exact, 0 regressions. ht-RACE mode measured UNSAFE
  (7216/7901) — keep fallback, never race.

### ore_ont_16461 — cardinality recognition (2026-06, `fd94c7e`)

- **Mechanism**: `≥n` recognition + fact-only successor cores.

### The three giants — 8737, 15059, 16744 (2026-06)

- **8737** (450–580 MB class): clone-free EL completion hot loop (`cd60ce3`):
  `in_edges` as flat `Vec<Vec<(parent,role)>>`, index-loop NF4, reused
  conclusion buffer. 252 → 221 s standalone; pipeline timeout → ok.
- **15059**: streaming frontend parse + compact DLClause (`ac153ef`):
  frontend peak 19.2 → 3.6 GB, byte-identical output.
- **16744**: Skolem-exclusion in EL-routing relevance (`72acb3a`) — the ont
  is EL-safe once Skolem-only symbols are excluded from the relevance check.

### Correctness family — the 4 "unsound" + contested gold (2026-06)

- All 4 apparent unsoundnesses were GOLD bugs; fixed data_abox precheck +
  complex-domain handling. 8941/13912/15516/2669 are genuinely inconsistent
  (HermiT agrees); proof in `CONTESTED-GOLD.md`.

---

## Diagnosed, not yet solved (the current frontier)

| Ont | Route | Signature | The path |
|---|---|---|---|
| 541 | bridge | nodes=4 FLAT, 2.6M chronological backtracks/120 s, branch depth 55–56 (≈2^56 space) | Port u29 `clashedBacktracking` (dependency-directed backjumping) + Unit 28/30 tracking-line records + arena watermark restore. Chronological search cannot finish; no constant factor helps. |
| 3215 | bridge | covered (unsupported=0), per-subject read-off terminates 0.4–6 s deterministic-after-gate; Konclude itself needs 22 s (-w8) | Correctness sample validating; the blocker is O(subjects) fresh saturations — needs databox-COW reuse per subject (Konclude reuses the preprocessed task). |
| 7914 | bridge | 46k nodes, hits the 5M drive cap, backtracks=0 | Model explosion, not search: blocking effectiveness + lazy-∀ extension (the giants' family). Production route: r-Succ completeness gap needs edge-conditioned forward push + Lean re-cert. |
| 9663, 9724 | production | central memory blowup (9663 saturation 115 GB) | Deterministic ≤n bounds in `saturate_global` + interning; see `KONCLUDE-SATURATION-CACHE-SPEC.md`. |
| 14817 | production | 71 missing = transitive `part_of` propagation | Role-automaton ∀-propagation is ported and live in konclude_ht tests (`6a7a67e`) but not production-wired: needs OntologyArenas-from-clauses + consistency classify. |
| 10621 | — | contested gold | Konclude-vs-HermiT disagreement; resolve gold first. |

## Reusable diagnostics

- `KM_BRIDGE_PROGRESS=1` — per-drive counters (`drives/backtracks/nodes/
  inserts/bp_depth` every 4096 drives; `PROGRESS-SAT` every 1M in-drive
  iterations). Distinguishes backtrack thrashing (nodes flat, backtracks
  climbing) from model explosion (nodes climbing) in one 120 s run.
- `KM_BRIDGE_DUMP_UNSUP=N` — shape of the first N clauses the bridge cannot
  encode; scopes the next coverage wave.
- `KM_BRIDGE_MAX_SUBJECTS=N` — bounded-sample classification against a
  (sampled) gold for correctness checks on deep taxonomies.
- `bridge_scale_probe` / `bridge_classify_full` (both `#[ignore]`d tests in
  `konclude_ht/bridge.rs`) — per-subject termination probe / full classify
  vs gold with MISSING/SPURIOUS attribution.
