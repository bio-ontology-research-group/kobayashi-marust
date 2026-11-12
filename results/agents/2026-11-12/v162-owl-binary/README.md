# v162-owl-binary: `km-owl-reference` and `KM_FRONTEND_CHECK`

Branch `v162/owl-binary` (from `development/v1.6.2` at 083169b0), worktree
`/mnt/data1/leechuck/km-work/wt/v162-bin`. Plan: `docs/V1.6.2-FRONTEND-PLAN.md`, section 7 (phase A).

## What changed

| file | content |
|---|---|
| `lean/ContextCalculus/OWLFrontend/ReferenceReadout.lean` (new) | probes, `probeRequest`, `OWLExact`, `RouteAnswer`, the readout `owlReadout` and its theorem `owlReadout_exact` |
| `lean/KMOWLReferenceCheck.lean` (new), `lean/lakefile.toml` | the executable `km-owl-reference` |
| `lean/ContextCalculus.lean` | imports the new module |
| `engine/src/orchestrate/frontend_check.rs` (new) | the check: run the checker, normalise, compare, outcome lines |
| `engine/src/orchestrate/mod.rs` | `Classification::frontend_check_gate`, `JsonClassification::frontend_check_gate`; the grouped JSON pairs moved into `GroupedJsonTaxonomy::try_for_each_pair`, which the serializer now calls (same pairs, same order) |
| `engine/src/bin/km.rs` | `km classify` (JSON and `--lines`) calls the gate after the `KM_LEAN_CHECKERS` gate |
| `engine/src/frontend/conformance.rs` | `prefixes` is `pub(crate)` (the check expands km's names with it) |
| `engine/tests/frontend_check.rs`, `engine/tests/fixtures/frontend_check/` | integration tests, two new fixtures |
| `results/.../v162-owl-binary/tools/run_frontend_check_suite.py` | suite runner (`select`, `run`, `summarize`), Python 3.9, standard library |

No theorem statement of v1.6.0, v1.6.1 or the v1.6.2 capstone changed. `owlReference`, `owlReference_sound` and `owlReference_complete` are used as they are.

## Lean: the readout theorem

The executable requests `probeRequest O = O.classNames ++ [probeA, probeB]` with
`probeA = "urn:km:owl-reference:probe-a"`, `probeB = "urn:km:owl-reference:probe-b"`.

```lean
def OWLExact (O : OWL.Ontology) (requested : List OWL.IRI) (a : OWLAnswer) : Prop :=
  a.named = requested.eraseDups ∧
    ∀ i j (hi : i < a.named.length) (hj : j < a.named.length),
      (a.bit i j = true ↔ OWL.EntailsSub O a.named[i] a.named[j])

def RouteAnswer : OWLProcedure → OWL.Ontology → List OWL.IRI → OWLAnswer → Prop
  | .el, O, requested, a => owlELReference O requested = some a
  | .alc, O, requested, a => owlALCReference O requested = some a
  | .elThenAlc, O, requested, a => owlReference O requested = some a

theorem routeAnswer_exact {p O requested a} (h : RouteAnswer p O requested a) :
    OWLExact O requested a

theorem owlReadout_exact {O : OWL.Ontology} {a : OWLAnswer}
    (hexact : OWLExact O (probeRequest O) a)
    (hA : probeA ∉ O.classNames) (hB : probeB ∉ O.classNames) :
    let names := O.classNames
    let r := owlReadout names.length a
    (r.inconsistent = true ↔ OWL.Inconsistent O) ∧
    (r.inconsistent = true → r.unsat = [] ∧ r.rows = []) ∧
    (r.inconsistent = false →
      (∀ i ∈ r.unsat, i < names.length) ∧
      (∀ i (hi : i < names.length), (i ∈ r.unsat ↔ OWL.Unsatisfiable O names[i])) ∧
      (∀ i (hi : i < names.length), ¬ OWL.Unsatisfiable O names[i] →
        ∃ s, (i, s) ∈ r.rows) ∧
      (∀ p ∈ r.rows, ∃ hi : p.1 < names.length, ¬ OWL.Unsatisfiable O names[p.1] ∧
        ∀ j (hj : j < names.length), (j ∈ p.2 ↔ OWL.EntailsSub O names[p.1] names[j])))
```

Helper lemmas: `probeA_ne_probeB`, `eraseDups_of_nodup`, `classIRIs_eq_classNames`,
`mentionsClass_iff_mem_classNames` (the probe lemmas' hypothesis `¬ O.mentionsClass P` is
`P ∉ O.classNames`), `probeRequest_nodup`, `bitAt_toArray`. The probe reading uses
`OWL.inconsistent_iff_entailsSub_fresh` and `OWL.unsatisfiable_iff_entailsSub_fresh` unchanged.
In the executable, `owlELReference_of_translate` and `owlALCReference_of_translate` (both `rfl`
after unfolding) give the route equations for the phase-by-phase computation.

`#print axioms` (from `lake build`):

```
'ContextCalculus.OWLFrontend.probeA_ne_probeB' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.routeAnswer_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.mentionsClass_iff_mem_classNames' depends on axioms: [propext, Classical.choice, Quot.sound]
'ContextCalculus.OWLFrontend.owlReadout_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `native_decide`, new axioms, `partial`, or raised limits in the new files.

## `km-owl-reference`

```
km-owl-reference [--procedure el|alc|el-then-alc] <file.ofn>     (default el-then-alc)
```

read, `OWL.parse`, request `probeRequest O` (decline if the ontology mentions a probe), run the
route, publish. `publish` takes `RouteAnswer p O (probeRequest O) a` and the two freshness proofs,
so `owlReadout_exact (routeAnswer_exact h) hA hB` covers what it prints. The ALC route declines
with `alc budget: N concept names` when `conceptCount` of the ALC translation exceeds
`KM_ALC_REFERENCE_MAX_CONCEPTS` (default 16), before the type elimination.

Output (streamed, 4096 items per write):
`{"format":"owl-sparse-v1","procedure":"el"|"alc","inconsistent":b,"unsat":[IRIs],"rows":[{"sub":IRI,"sups":[IRIs]},...]}`.
Rows exist only for satisfiable classes; `sups` holds every class superclass, the class itself
included; an inconsistent ontology prints empty `unsat` and `rows`.

| exit | meaning (stderr) |
|---|---|
| 0 | published |
| 2 | usage, or `failed to read <path>: ...` |
| 3 | decline: `parse rejected: <parser reason>`, `probe IRI mentioned: <iri>`, `not recognised: not OWL EL (first: <axiom kind>)` / `not OWL ALC (...)` / `neither OWL EL (...) nor OWL ALC (...)`, `alc budget: N concept names` |
| 4 | `io error: ...` after the read (for example a failed stdout write) |

`KM_REFERENCE_TIMING=1`: phases `read`, `parse`, `names`, `translate` (twice under el-then-alc
when EL does not apply), `closure` (EL) or `types` (ALC), `rows` (sparse rows), `readout` (probe
readout), `output`, `total`.

Loops over input-sized lists are `foldl`, `filter`, `filterMap`, `map`, `append` (tail-recursive
twins) or `writeChunked` (tail call). Measured on ws with `LEAN_STACK_SIZE_KB=262144`:

| input | MB | classes | wall s | max RSS MB | output MB |
|---|---:|---:|---:|---:|---:|
| ore_ont_8021 | 0.16 | 606 | 0.18 | 74 | 0.1 |
| ore_ont_12405 | 1.0 | 4,238 | 1.0 | 99 | 0.5 |
| ore_ont_15099 | 8.5 | 33,609 | 1.6 | 160 | 4.0 |
| ore_ont_12387 | 51 | 137,334 | 11.4 | 599 | 34 |
| ore_ont_868 (NCBITaxon) | 178 | 981,151 | 96.3 | 3,542 | 836 |

ore_ont_868 phases (ms): read 1492, parse 4287, names 994, translate 1683, closure 59771, rows 20797, readout 2437, output 2632.

## `KM_FRONTEND_CHECK=1` in `km classify`

After the final answer (any route, JSON and `--lines`; not `--realize`), with
`KM_FRONTEND_CHECK=1`:

- checker `KM_OWL_REFERENCE_CHECKER`, else `lean/.lake/build/bin/km-owl-reference`; run through
  `lean_checkers::CheckerCommand` (256 MiB Lean stack, start-up retry, parent-death kill) with
  `--procedure el-then-alc` on the input file under `KM_FRONTEND_CHECK_BUDGET_S` (default 300);
- comparison in the normal form of the checkers-on digest (`parse_answer_digest`): the
  inconsistency verdict; for consistent answers the unsatisfiable set and the subsumptions with a
  satisfiable subclass, reflexive pairs and pairs with `owl:Thing`/`owl:Nothing` dropped; two
  inconsistent answers agree. km's names are expanded with the document's prefixes
  (`conformance::prefixes`), a name without a declared prefix is a full IRI;
- with `KM_TIMING`: `KM_TIMING KM_FRONTEND_CHECK agreed procedure=<p>`,
  `... disagreed: <first item> (procedure=<p>)` or `... declined: <reason>`, plus
  `KM_TIMING KM_FRONTEND_CHECK_PHASE phase=<name> ms=<ms>` and `KM_TIMING KM_FRONTEND_CHECK_WALL ms=<ms>`;
- disagreement: the `KM_LEAN_CHECKERS` convention (`lean_checkers::Run::finish`, docs/CHECKERS-ON.md
  section 2): nothing on stdout, `KM_FRONTEND_CHECK fail closed: km-owl-reference (procedure <p>)
  disagrees with the answer (<first>); no answer published` on stderr, exit
  `lean_checkers::REJECTED_EXIT` (6);
- decline (checker exit non-zero, budget, unreadable checker output, no checker, a km answer
  that is approximate or dropped axioms): the answer is published unchanged;
- off (`KM_FRONTEND_CHECK` unset or not `1`): the gate returns before any work.

## Tests

```
cd engine && CARGO_TARGET_DIR=$PWD/target CARGO_BUILD_JOBS=2 KM_REQUIRE_LEAN_CHECKERS=1 \
  KM_OWL_TEST_REFERENCE_CHECKER=$PWD/../lean/.lake/build/bin/km-owl-reference \
  cargo test --offline --test frontend_check            # 14 passed, 0 failed
cargo test --offline --lib orchestrate                  # 336 passed, 0 failed, 1 ignored (8 new frontend_check unit tests)
cargo test --offline --test graph_json_cli              # 3 passed (serializer refactor)
```

`frontend_check.rs`: agreement on 6 EL fixtures (existentials, role chain, two with unsatisfiable
classes, TBox inconsistency, full IRIs with `owl:Thing`/`owl:Nothing`) and 2 ALC fixtures
(disjunction, an unsatisfiable class through `∀`/`¬`), each in both output modes with the output
byte-identical to the unchecked run; declines outside the fragment (nominal, cardinality) and
over the ALC budget; three disagreements through fake checker scripts (verdict, subsumption,
unsatisfiability) failing closed with exit 6 and empty stdout in both modes; checker failure,
garbage output, budget and missing checker declining; off by default.

## Smoke run (ws, 2 processes, `nice`, `timeout 300`, checker budget 240 s)

Release km built with `CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`
(build speed only). Inputs `smoke-inputs.tsv` (`select`: F inputs of the v162-parse differential,
kind guessed from the survey heads, spread over sizes, plus 5 non-F), results
`smoke-results.tsv`, tables `smoke-summary.md`.

| kind | inputs | km ok | agreed | disagreed | declined |
|---|---:|---:|---:|---:|---:|
| EL (0.1 KB to 6.6 MB) | 15 | 15 | 15 (el) | 0 | 0 |
| ALC (0.2 KB to 2.2 MB) | 8 | 8 | 1 (alc) | 0 | 7 (alc budget: 18 to 13,799 concept names) |
| other F (inverses, ranges with role axioms) | 2 | 2 | 0 | 0 | 2 (not recognised: neither EL nor ALC) |
| non-F | 5 | 5 | 0 | 0 | 5 (parse rejected: out of fragment) |
| all | 30 | 30 | 16 | 0 | 14 |

The largest checker time was ore_ont_16746 (3.7 MB, 8,576 classes): 22.3 s, closure 20.8 s
(km itself about 1 s). km's wall time in the table includes the check.

## Open

- ALC agreement on real inputs is rare under the 16-concept budget (as for the v1.6.0 stage); the
  full suite will mostly show `alc budget` declines on ALC inputs.
- `km classify --realize` is not checked (realization is outside F; ABox assertions are stage 2).
- The checker's stdout is held in memory (836 MB on ore_ont_868), parsed with borrowed strings.
- Full suite on Ibex: the lead's run.

Lean build: `cd lean && LEAN_NUM_THREADS=2 nice lake build ContextCalculus km-owl-reference km-el-reference`: success (12,206 jobs).
