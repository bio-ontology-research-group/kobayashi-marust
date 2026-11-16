# KM 1.6.5 release notes

Released 2026-11-16 from commit `55117da2`. v1.6.4 was not tagged; its changes
(issue #5) ship in 1.6.5.

## What changes

KM 1.6.5 is v1.6.4 (the issue #5 fix, `docs/RELEASE-1.6.4.md`) plus the
fixes for wrong answers found on the v1.7.0 line by the Protégé parity
harness and by random differential testing against HermiT. No new
features; no theorem changes; the Lean development is that of v1.6.3.

Each fix below names the smallest example, the versions affected and the
inputs it touches. "Affected" means the clause stream or the answer can
change; the corpus checks are in "Checks".

- **Empty domain or range (E7).** `ObjectPropertyDomain(r owl:Nothing)`
  and `ObjectPropertyRange(r owl:Nothing)` produced no clause, so
  `C ≡ ∃r.⊤` was not reported unsatisfiable. Present in every release
  that has the RBox side path (`rbox::plain_class` maps `owl:Nothing` to a
  complex domain); the earliest affected release was not determined.
  Affects inputs with such an axiom.
- **The universal role in property axioms (E8).** `owl:topObjectProperty`
  as a sub-property, in a chain, in equivalent or inverse property
  axioms, in characteristics, assertions, rule atoms and keys was read as
  an ordinary property, so for example `SubObjectPropertyOf(U r)` with
  `⊤ ⊑ ∀r.C` did not give `⊤ ⊑ C`. Every such position is now encoded
  exactly through the universal-role rewrite or removed as a tautology.
- **Consumers of role chains (E12).** The CB clause stream lost the
  consequences of a role chain for every consumer of the chain's
  super-role other than a plain existential over roles of the same
  orientation. Smallest example: `s ∘ t ∘ t⁻ ⊑ r`, `⊤ ⊑ ∃t.{g}`,
  `A ⊑ ∃s.⊤`, `A ⊑ ∀r.C` entails `A ⊑ C`; km did not report it. Answers
  were wrong whenever the CB route answered: chains of three or more
  roles, nominal inputs, and bridge deferrals. The frontend adds a
  role-automaton encoding for these consumers; the CB rules are unchanged.
- **Negative role assertions (E17, since v1.4.4).** `{r(a,b),
  ¬r(a,c)}` was reported inconsistent: the CB worker read `¬r(a,c)` as
  `r(x,c) → x ≉ a` and bound `c` like a variable.
- **Transitive roles over ABox edges (E18, since v1.4.4).**
  `Transitive(p)`, `p(a,b)`, `p(b,c)`, `a : ¬∃p.{c}` was reported
  consistent when the assertions came in one order.
- **Shared data values and nominals (E19).** With `g` functional,
  `g(a,0)`, `g(b,255)` and `h(b,0)`, the native bridge reported
  `{a} ⊓ {b}` satisfiable. A merge of two equal data values made a child
  of `b` the witness of `a`'s `∃g.{0}`; merging `b` into `a` removed that
  child, and the existential was never applied again. Found on
  ore_ont_15667 (`ColorBlue`, `ColorCyan`).
- **Negated definitions over data counts.** `{Functional(k),
  {c} ⊑ ¬C, C ≡ =1 k.xsd:integer, k(c,2)}` was reported consistent: the
  bridge made `C` a lazily unfolded definition and absorbed `{c} ⊑ ¬C`
  onto `C`, which a node satisfying the definition never receives.
- **Smaller fixes.** A repeated ABox axiom no longer makes the bridge
  decline (and no longer publishes a spurious `DROPPED` count); the CB
  translation drops and counts a body equality between an individual and
  a non-central variable; `km classify --realize` no longer runs its
  workers with more threads than the caller's `KM_THREADS` (E20).

## Backported commits

From `development/v1.7.0` (`git cherry-pick -x`): 19226c0c (E7), 948824ab
(E8), 15932b8e (E12), ee662a62 (E17, E18, E20), 8fd18c59 (repeat count,
chain-consumer marker cost), 7a743bf5 and 3eaa2cdd (E19: the routing gate
of the first is removed by the second), 06f5b9b4 (CB guard), 6f2c0a8e
(negated definitions). CHANGELOG conflicts were resolved by hand; files of
features this branch does not carry (`docs/PROPERTIES.md`,
`tests/properties_cli.rs`) were left out.

## Checks

Ibex certification and measurement from commit `55117da246937d9a1b3cf76613d24fbf954027d0`
(tag `v1.6.5`), 2026-11-16:

- PGO build: completed; binary sha256 `e5a9242274ac97ad849b1aad7b4e12b77978cdc6c767c1e3234a2a18bee6e416`.
- Lean gates (CB, ELC, HT, routing, rules, and the overall gate): passed.
- Rust suite with the Lean checker binaries (`full-rust.json`): passed.
- Java plugin and checkers: passed (86 tests, no failure).
- C1, wrong answers: none in the full regression pool (1,708 admitted inputs
  measured, 1,684 verified).
- S1, held-out half against the same-day v1.5.3 protocol run, two paired runs:

  | Run | Verified | Mean ratio | Median ratio | Konclude (same day) |
  |---|---:|---:|---:|---|
  | pair 55632919 | 576 | 0.904 | 1.110 | 576 against 575 |
  | pair 55633977 (repeat) | 577 | 0.909 | 1.078 | 577 against 575 |

  The first run misses the median bound of 1.1 by 0.010; the repeat meets
  every clause. On that day the unchanged v1.5.3 reference measured 29%
  slower than on 2026-11-14 (median 0.201 s against 0.156 s), and v1.6.4-rc1
  scored 1.094 on the same clause, so the two runs bracket the bound within
  node noise. The repeat is the run of record.
- Against the v1.6.4-rc1 measurement of 2026-11-14, input by input: no
  changed answer; `ore_ont_10838` (96 to 108 s before) times out at 240 s in
  the pool run and the first paired run and is verified in neither;
  `ore_ont_15846` (202 s) and `ore_ont_3087` (123 s) time out in the pool run
  only. Two inputs cost more memory: `ore_ont_9540` (1.05 GB to 11.0 GB,
  8.6 s to about 40 s), from the definition fix in the native bridge
  ("Negated definitions over data counts"), and `ore_ont_13242` (3.0 GB to
  4.8 GB), from the complete role-chain encoding (E12).
- An earlier candidate (`60383939`) passed the same certification but lost
  three inputs to a leftover diagnostic gate in the native bridge (about
  100 inputs were two to five times slower); `55117da2` removes the gate.
- Full-pool comparison on the workstation, v1.6.4-rc1 against `55117da2`
  under the release flags (1,708 inputs, 240 s): no status change, no
  changed answer; time or memory growth above 1.5x only on `ore_ont_9540`
  and `ore_ont_13242`. Under the release flags the answer on `ore_ont_7203`
  is identical in both builds (the 12 extra subsumptions listed below show
  only without them).

Workstation checks (2026-11-15, binary built from `development/v1.6.5`,
compared with a build of `v1.6.4-rc1`, `KM_THREADS=1`):

- `cargo test --release --lib`, two runs: 28 and 21 failures, all in the
  list of 27 that v1.6.4-rc1 fails without the Lean checker binaries,
  except, in the first run,
  `elcomplete::tests::positive_abox_completion_respects_identity_and_conjunction_clashes`,
  which passes alone, in its module and in a second full run (the
  environment race fixed on the v1.7.0 line by the test lock, not
  backported). Integration suites, including the new `role_chain_consumers`,
  `abox_assertions` and `builtin_roles_cli`: all pass after one test
  update (`symbolic_source_classification`: the universal role as a
  sub-role is now encoded, E8, so the decline test uses another construct).
- `km ofn --meta` on 839 corpus inputs (300+ sampled plus every input of
  the affected sets): 764 byte-identical, 74 changed, one (ore_ont_15687)
  aborts on both binaries. Every changed input is in an expected set: 72
  have role chains (E12), 38 the universal role or an empty domain or
  range (E7/E8), 16 negative or transitive ABox assertions (E17/E18).
- Classification answers, before and after, on the 532 inputs of the
  affected sets (60 s per run): 498 identical, 31 without an answer on
  both, 2 answered only after (ore_ont_12743, ore_ont_9151: about 60 s on
  both binaries), and one changed answer: ore_ont_7203 gains 12
  subsumptions `X ⊑ CL_0000520`; HermiT confirms them (one is asserted;
  the source has `SubObjectPropertyOf(hasDisease owl:topObjectProperty)`,
  E8), so v1.6.4 was wrong there.
- Random differential sets against HermiT, 10,000 knowledge bases (five
  sets of 2,000): no km wrong answer. Every difference is a HermiT error
  confirmed by HermiT's own consistency check (type rows HermiT reports
  but refutes when the negation is added, `DifferentIndividuals(a a)`
  treated as vacuous, `"1"^^xsd:int` and `"1"^^xsd:integer` treated as
  different values) or a km timeout at 30 s.
- Issue #5 reproducer: 18.2 s (v1.6.4-rc1: 18.5 s), same answer.

## Known issues

As in `docs/RELEASE-1.6.4.md`, plus:

- `ore_ont_9540` needs about 11 GB (1 GB in v1.6.4) and `ore_ont_13242`
  4.8 GB (3.0 GB); the first is a cost of the bridge definition fix, the
  second of the complete role-chain encoding (already removed on the v1.7.0
  line). Both are planned for the next release.
- `ore_ont_10838` no longer finishes inside 240 s on Ibex.

## Assets

`kobayashi-marust-protege5-1.6.5.jar`, `kobayashi-marust-protege6-1.6.5.jar`
(attached by CI), and the km executables built by CI for the five
platforms (release profile, not PGO).
