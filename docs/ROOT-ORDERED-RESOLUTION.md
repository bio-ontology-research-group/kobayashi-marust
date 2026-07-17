# Root-context ordered resolution with a refutation residue readout (Direction A)

Status: implemented, gated `KM_ROOT_ORDERED` (default OFF). Branch
`codex/agent-ordered-resolution`. This is the Direction-A design of
docs/DISJUNCTION-SPLITTING.md §3, narrowed to the smallest sound + complete
step. Target: the live `∀ + ⊔` disjunction family that is CB-only
(ORE 10702, 15672, 6934, 9540 carry inverse / nominals / cardinality, so the
HT routes are unsound or fenced there; 5303 is solved on the HT side).

## 1. The problem this attacks

In the default regime, same-term concept literals are MUTUALLY INCOMPARABLE
in every context (`calc.rs::pred_lteq`, the `t1 == t2` branch). Every disjunct
of a derived disjunction is a maximal head literal, Hyper fires on all of
them, and the worked-off population grows as the product of the disjunction
widths; forward/back subsumption cannot prune incomparable disjunctions. The
incomparability exists for ONE reason: the classification readout takes the
subsumers of query `A` to be the named `B` with a derived unit `⊤ → B(x)` in
`A`'s root context, and with a total order an entailed unit can be TRAPPED:

    A ⊑ X ⊔ B,  X ⊑ B   ⊨   A ⊑ B

Under a total order with `B` maximal, `⊤ → X ∨ B` resolves only on `B`, which
no clause consumes; `X ⊑ B` never fires, `⊤ → B(x)` never surfaces. That is
the measured `KM_ORDERED_ALL` incompleteness (calc.rs verdict, jobs
6123/6125: recovered 12698/2313/5107 from timeout but with 1–5 missing
subsumptions each, and regressed 13383 by 1).

The key asymmetry: the UNSAT readout (deriving the empty clause) is
order-robust — refutational completeness of ordered resolution does not
depend on which literal is maximal (`CompletenessOrdered.lean` certifies this
on the ground core). Only the positive unit readout is order-fragile.

## 2. The mechanism

`KM_ROOT_ORDERED=1` (root contexts) or `KM_ROOT_ORDERED=all` (every context):

1. **Ordering** (`calc.rs::pred_lteq`): same-term concept literals are
   totally ordered — internal definers above named concepts, iri tie-break
   within each block — in root contexts (mode 1) or everywhere (mode 2).
   Pred-trigger atoms stay at the bottom and term-major comparison stays
   unchanged, so the order still satisfies the context-order conditions
   (Def 3 + appendix A of arXiv:1805.01396); the calculus is parameterised by
   a PER-CONTEXT order family, so mixing an ordered root regime with the
   incomparable successor regime is a legal instantiation. The mode is a
   thread-local (like `BRANCH_ORDERED`), set by the single-threaded driver.

2. **Complement guards** (`reasoner.rs::saturate_root_ordered`): for every
   named concept `B`, a fresh internal concept `__notb__B` and the guard
   clause `B ⊓ NotB ⊑ ⊥`. `NotB` occurs in no head, so it is never derivable:
   the guards are inert outside refutation cores, and jointly conservative
   (interpret each `NotB` as the complement of `B`).

3. **Refutation residue readout** (`engine.rs::ordered_residue_repair`):
   after the ordinary classification run, for each query root `A` that did
   not derive `⊥`: every named `B` occurring ORDERING-MAXIMAL in some
   worked-off head of `A`'s root context, and not already a unit, is decided
   by reduction to unsat — seed the context with core `{A(x), NotB(x)}` in
   the SAME engine (sharing the successor graph and the shared root closure)
   and report `A ⊑ B` iff that context derives the empty clause.

4. **Nominal-enumeration shortcut disabled** under any ordered mode
   (`complete_nominal_enumeration_queries` bails): the shortcut reads
   `⊤ → B(o)` units off the ground context and its completeness was validated
   under the default regime only. The affected queries fall back to ordinary
   CB classification, which the repair keeps complete.

The trapped example above: candidates of `A`'s root are `{B}` (`B` is maximal
in `⊤ → X ∨ B`); the `{A, NotB}` context fires the guard against `⊤ → X ∨ B`
(cutting `B`), derives `⊤ → X`, fires `X ⊑ B`, derives `⊤ → B`, fires the
guard again → `⊥`. `A ⊑ B` recovered, `A ⊑ X` correctly refuted-negative.

## 3. Why this is sound and complete

- **Soundness of positives.** A repaired pair is backed by a derived empty
  clause in the `{A(x), NotB(x)}` context, i.e. `O + guards ⊨ A ⊓ NotB ⊑ ⊥`
  (the existing calculus soundness, `Basic.lean` — restricting Hyper to
  maximal literals only removes rule instances, so every ordered derivation
  is a derivation of the certified calculus). Conservativity of the guards
  (O3) then gives `O ⊨ A ⊑ B`. Direct units are sound as before.

- **Completeness.** Suppose `O ⊨ A ⊑ B` and `A`'s root did not derive `⊥`.
  Then `O + guards ⊨ A ⊓ NotB ⊑ ⊥`, so by refutational completeness of the
  calculus under the (valid) ordered regime (O1) the `{A(x), NotB(x)}`
  context derives `⊥` — PROVIDED `B` is in the candidate set. Coverage (O2):
  a refutation of `{A, NotB}` must use the seed `⊤ → NotB(x)` (else it is a
  refutation of `{A}` alone, contradicting `A`'s root not deriving `⊥` —
  those derivations mirror into `A`'s context), and the ONLY rule that can
  consume `NotB` is Hyper on the guard `B ∧ NotB → ⊥` (`NotB` is in no other
  clause, is never a Succ or Pred trigger, and never leaves its core). Its
  first firing resolves a `NotB`-free side clause with `B(x)` ordering-
  maximal in the head; `NotB`-free derivations in `{A, NotB}` mirror into
  `{A}`'s saturation, so `A`'s saturated root contains a clause with `B(x)`
  maximal — exactly the candidate condition. (Heads over 64 literals fall
  back to "all maximal" in `max_head`, an over-approximation that only
  enlarges the candidate set.)

- **Unsat / inconsistency readout** is `⊥`-based and order-robust (O1).

## 4. Lean re-certification status — REQUIRED before default-on

This changes what is derived (the ordering prunes Hyper instances; the
readout adds refutation contexts), so per AGENTS.md it is calculus logic and
needs re-certification. The feature therefore stays GATED, default OFF, with
these precise obligations:

- **O1 (ordered refutational completeness).** The context calculus with the
  per-context order family {root: the total same-term concept order above;
  non-root: unchanged} derives the empty clause in the `{A(x), NotB(x)}`
  context whenever `O + guards ⊨ A ⊓ NotB ⊑ ⊥`. Ground core: DONE —
  `CompletenessOrdered.ordered_completeness` (Bachmair–Ganzinger candidate
  model, sorry-free). Paper level: any Def-3-valid order family, and §2.1
  shows the order is Def-3-valid. Clause-level mechanisation of the full
  context calculus is the SAME open theorem as for the default regime
  (lean/README "What is NOT claimed" item 2); this feature changes the
  instance, not the shape, of that obligation.

- **O2 (candidate coverage, the genuinely new lemma).** Propositional
  statement, targeted at `CompletenessOrdered.lean`:

      theorem covered_candidate {Atom} [LinearOrder Atom] [Fintype Atom]
          [DecidableEq Atom] (S : Finset (PClause Atom)) (b : Atom)
          (hsat : OrdSaturated S) (hbot : PClause.bot ∉ S)
          (hent : ∀ I, models I S → I b) :
          ∃ c ∈ S, c.strictMaxPosLit = some b

  Proof sketch: if no clause of `S` has `b` strictly-maximal positive, then
  `S ∪ {¬b}` admits no ordered inference involving `¬b` (the positive premise
  of a resolution on `b` would need `b` strictly maximal), so it is saturated
  and `⊥`-free, and `ordered_model_exists` yields a model of `S` with `b`
  false — contradicting `hent`. The first-order lift (the mirroring argument
  of §3) additionally needs: `NotB` is consumed only by the guard, and
  `NotB`-free derivations of the `{A, NotB}` context are derivations of the
  `{A}` context.

- **O3 (conservativity of the complement guards).** Every model `I` of `O`
  extends to `O + guards` via `NotB^I := Δ \ B^I`, and conversely a
  refutation under the guards yields `O ⊨ A ⊑ B`. Semantic bookkeeping over
  `Basic.lean`'s model relation.

The Lean build was not run in this session (no mathlib olean cache in this
snapshot); O2/O3 are sized as one short file addition once a cache is
available on `ws`.

## 5. Validation state and what remains

Focused synthetic tests (all passing, `cargo test --lib root_ordered`; full
lib suite 1529 passed / 0 failed):

- `root_ordered_recovers_trapped_named_unit` — the §1 trap, both modes;
  verified against the worker binary that the pair comes from the REPAIR
  (`KM_PROF root-ordered: repaired_pairs=1`), not from the ordered closure.
- `root_ordered_trap_other_interning_order` — opposite iri order (no trap).
- `root_ordered_recovers_chained_trapped_units` — two trapped supers.
- `root_ordered_no_spurious_subsumption` — refutation-negative candidates.
- `root_ordered_exclusive_global_disjunction` — the family's `⊤ ⊑ P ⊔ N` +
  disjointness shape.
- `root_ordered_unsat_query` — order-robust ⊥ readout.
- `root_ordered_disjunction_over_successor` — the historical
  `KM_ORDERED_ALL` probe (`A ⊑ ∃R.(C⊔D), C⊑E, D⊑E, ∃R.E⊑G ⊢ A⊑G`), both
  modes (mode 2 orders successor contexts too).
- `root_ordered_matches_default_engine` — subsumption-map equality with the
  default engine on a mixed ontology.

### 5.1 Family measurement (cycle 8, 2026-07-17) — MEASURED: does NOT recover the family

Ran mode 1 and mode 2 directly on the four shared timeout targets on the
workstation (`km engine` on the `ofn` clause set, isolated target dir), and a
differential vs the default engine on the local finishable onts. Two questions
from item 2 below are now answered, both NEGATIVELY for recovery.

**Recovery — NONE of 10702 / 15672 / 6934 / 9540 converges.** Both modes time
out at 240 s; the two tiniest still time out at 520 s; 10702 mode 2 was traced
to ~600 s. Peak RSS stays bounded (so this is search / propagation
non-convergence, not the arena OOM the default engine hits):

| ont | mode 1 (240 s) | mode 2 (240 s) | mode 2 peak RSS | shape at timeout |
|-----|----------------|----------------|-----------------|------------------|
| 10702 | timeout | timeout (also ~600 s) | 604 MB | disjunctive-product blow-up: worked_off 160k→620k+, wide heads h3 841→280k, h4+ 3→86k, max_head 5→7, still climbing (no plateau) |
| 6934  | timeout | timeout | 40 MB | intermediate |
| 15672 | timeout | timeout (also 520 s) | 21 MB | tiny bounded memory, no disjunctive growth — nominal/cardinality search spin |
| 9540  | timeout | timeout (also 520 s) | 18 MB | tiny bounded memory — SHOIQ cardinality search spin |

The decisive split: **15672 and 9540 are not disjunction-product-bound at all**
(≤21 MB, no wide-head growth — the "pure search non-convergence at tiny memory"
of docs/THROUGHPUT-SATURATION.md), so ordered resolution is simply orthogonal to
their bottleneck. **10702 is** disjunction-product-bound, but mode 2 only *slows*
the wide-head proliferation (it keeps the run under 604 MB where the default
OOMs, and caps max head width at 7 vs the default's 9) — it does not *bound* it;
worked_off keeps climbing. mode 1 (root contexts only) leaves the successor /
ground-context disjunctions incomparable, so it matches the default blow-up.

Root cause of the non-recovery: ordering prunes *which* Hyper instances fire but
still materialises the disjunctive closure of the hard part, exactly the lesson
of docs/DISJUNCTION-SPLITTING.md §1/§8. Recovering this family needs the
interleaved decision-trail + blocking capability (splitting *during* saturation,
DISJUNCTION-SPLITTING §8; or the SHIQ-completion re-architecture,
THROUGHPUT-SATURATION §3), not ordered resolution over the monotone engine.

**Correctness — sound + complete preserved (differential, 15/15 byte-identical).**
mode 1 and mode 2 produce the *exact* subsumption map of the default engine on
every finishable local ont tested: 178, 394, 1481, 2453, 2744, 5184, 5564,
11016, 13035, 13132, **13383** (368 keys, named disjunction), 3050, 148 (~3000
keys), and the disjunction-family **12698** (15 566 keys) and **5107** — 0
differing subjects, matching consistency. So the complement-guard residue readout
restores completeness with no regression: KM_ROOT_ORDERED is correct, just inert
on the target family. This partially discharges item 1 (byte-identical on the
finishable local subset; the full ORE corpus A/B still needs a sweep).

Verdict: **KM_ROOT_ORDERED stays gated OFF** — not because it is unsound (it is
not), but because it recovers 0 of the family it was designed for. Do not spend
a future cycle re-measuring ordered resolution on 10702/15672/6934/9540.

### 5.2 Still open (needs ws/ibex)

1. Corpus A/B (full ORE 2015) vs the default engine: byte-identical
   signatures on the finishable ontologies, soundness-vs-gold table must not
   regress (AGENTS.md). Partially done: 15/15 byte-identical on the local
   finishable subset (§5.1); the full-corpus sweep remains.
2. Lean obligations O2/O3 (and the O1 instance note) — §4.
3. Routing: moot for this family (§5.1 shows 0 recovery). If a *different*
   ontology class is ever found where the ordered closure converges strictly
   faster than the default AND the residue cost is bounded, only then wire a
   `root_ordered` procedure into the routing matrix.

## 6. Interactions and caveats

- `KM_SPLIT` takes precedence (checked first in `Reasoner::saturate`); the
  two experiments do not compose.
- The driver is single-threaded (the mode is thread-local). Parallelising
  needs the mode propagated to workers — do not lift the gate before that.
- `KM_ORDERED_ALL` / `KM_SEQ_ORDER` are untouched; the root-ordered branch in
  `pred_lteq` runs before both, so setting `KM_ROOT_ORDERED` supersedes them
  on the driver thread.
- The repair only patches the ROOT unit readout. It is NOT a license to
  order the ground context's readout consumers: the nominal-enumeration
  shortcut is disabled under the ordered modes for exactly that reason.
- Output note: repaired pairs are merged into `Reasoner::subs` after
  `Engine::subsumptions()`; the engine's own JSON output is unchanged.
