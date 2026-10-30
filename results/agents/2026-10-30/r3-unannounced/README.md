# R3 and disjunctive ground equalities across an unannounced individual

Question (docs/V1.5.4-STATUS.md, open defects): can a disjunctive ground
equality `→ Δ ∨ o ≈ o'` in the nominal ground context, with the receiving
context announcing only `o`, cause a missed consequence? Answer: yes. Four
HermiT-checked motifs, fixed in commit 7c238e52 on `fix/v155-r3-unannounced`;
argument and measurements in docs/PER-CONTEXT-ORDERING.md section 8.

## Binaries

- v1.5.4: `.work/pgo-v154/km-pgo-use`, sha256 `ac15b822…a71a` (PGO release).
- fix: `km.final` = `engine/target/release/km` at the tree of 7c238e52
  without the `KM_CONTEXT_NO_GUARD` diagnostic, sha256 `a18066b2…9e24`
  (non-PGO release, `cargo build --release`). `km.final2` adds the diagnostic
  (the committed tree), sha256 `c91bbe3c…c9f`; used for the guard-off check,
  the sorts fixtures, `gen_nomdata.py` and the tests. The two differ only in
  that env-gated diagnostic.
- "v1.5.4 rules": the fix binary with `KM_CONTEXT_UNIT_R3=1
  KM_CONTEXT_NO_EQ_R2=1`.
- Oracle: HermiT 1.4.3.456 through `oracle/Oracle.java` (classpath of
  `.work/agent-assets/2026-10-28-scratch/oracle/cp.txt`), `-Xmx1g`.

Binaries and the generated inputs stay in
`.work/agent-scratch/r3-unannounced/` (not committed).

## Generators and drivers

- `gen_tpl.py SEED OUT [--family2]`: motifs m1 to m5 (m6, m7 with
  `--family2`) with random names, shuffled axiom order and noise axioms.
- `gen_r3.py SEED OUT [--no-inverse]`: random small nominal ontologies
  (3 to 5 individuals, at-most restrictions alone or in unions, enumerations,
  functional and inverse-functional roles, query classes `Qi ⊑ {o}` or
  `Qi ≡ {o}`).
- `genall.py DIR`: writes `seeds/r0..r3999` (r3000 on without inverse roles),
  `tpl/t0..t1999`, `tpl2/u0..u999`.
- `diff_run.py KM ORACLE GOLD OUT ROUTES FILE...`: the 2026-10-29 runner with
  `-Xmx1g` for HermiT. `DIFF_KEEP` adds KM variables (the v1.5.4-rules runs).
- `bymotif.py`, `abl.sh` (ablation of the two rules on one file), `perm.py`
  (axiom-order permutations of a hand-written file), `ore_time.sh` (the
  2026-10-29 sequential timer).

## Data

- `diff-<binary>-<set>.tsv`: file, route, verdict, seconds, missed and extra
  subsumptions, missed and extra unsatisfiable classes, consistency mismatch.
  Sets: `tpl` (m1..m5, 20 s), `tpl2` (m6, m7, 20 s), `rand` (`gen_r3.py`,
  10 s), `nomdata` (`gen_nomdata.py` 1000-1099 with inverse roles,
  2000-2199 without, 30 s), `sorts` (fixtures, 60 s, routes auto, nominals,
  certified_nominals).
- `pair-slow.tsv`: the 73 random seeds answered under the v1.5.4 rules and
  not under the fix within 10 s, rerun pairwise at 60 s.
- `ore-auto-times-<stream>.tsv`, `ore-nominals-times-<stream>.tsv`, `ore-rerun600-times-<stream>.tsv` (9800, 11270 at 600 s), `ore-compare-*.txt`: the 112 nominal
  inputs of the paired design half (`ore-design-nominal.txt`), automatic
  route at 300 s and forced `nominals` at 120 s, three or two streams side by
  side on the shared workstation (load 75 to 100).
- `open_r1600.ofn`, `open_r1646.ofn`, `open_r3403.ofn`, `open_r3602.ofn` with
  `*.hermit.json`: random seeds the `nominals` route still answers
  incompletely under every rule set and with the guard off; not caused by the
  guard (docs/PER-CONTEXT-ORDERING.md section 8.5). `open_r1600` is also
  incomplete on the automatic route.

## Reproduce

    S=.work/agent-scratch/r3-unannounced
    python3 -I genall.py $S
    DIFF_THREADS=8 DIFF_KM_TIMEOUT=20 python3 -I diff_run.py $S/km.final \
        $S/oracle $S/gold out.tsv nominals $S/tpl/*.ofn
    DIFF_KEEP=KM_CONTEXT_UNIT_R3=1,KM_CONTEXT_NO_EQ_R2=1 ...   # v1.5.4 rules
    ore_time.sh $S/km.final ore-design-nominal.txt OUT final KM_ROUTE=nominals

## Results in brief

| set | v1.5.4 | v1.5.4 rules, same binary | fix |
|---|---|---|---|
| tpl m1-m5 (2,000, 20 s) | 1,520 ok, 480 wrong | | 1,999 ok, 1 timeout |
| tpl2 m6, m7 (1,000, 20 s) | 842 ok, 155 wrong | | 997 ok, 3 timeouts |
| rand (4,000, 10 s) | 2,217 ok, 4 wrong | 2,259 ok, 6 wrong | 2,205 ok, 4 wrong |
| nomdata (300, 30 s) | | 183 ok, 0 wrong | 186 ok, 0 wrong |
| sorts fixtures (33 runs) | | | 33 ok |
| ORE design nominal, auto, 300 s | 105 common answers identical | 104 common with fix identical, ratio fix/old 0.946 mean, 0.950 median | |
| ORE design nominal, forced nominals, 120 s | | 76 answered, identical, ratio 0.978 / 0.974 | |

Cost on `rand`: both-answered seeds 1.21 times the total time (median 1.13),
36 of 73 rerun seeds answered only under the v1.5.4 rules at 60 s; the
ablations put the cost on R2 for equalities (docs/PER-CONTEXT-ORDERING.md
section 8.5).
