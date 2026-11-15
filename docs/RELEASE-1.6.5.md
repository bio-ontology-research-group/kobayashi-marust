# KM 1.6.5 release notes

Not yet released (no tag). v1.6.4 was not tagged; its changes (issue #5)
ship in 1.6.5.

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

PENDING (maintainer): Ibex certification from the tag (PGO build, five
Lean gates, Rust suite, Java and checkers) and the S1/C1 speed and
correctness runs.

Workstation checks before the tag: see the interim report; to be filled
in here.

## Known issues

As in `docs/RELEASE-1.6.4.md`.

## Assets

`kobayashi-marust-protege5-1.6.5.jar`, `kobayashi-marust-protege6-1.6.5.jar`
(attached by CI), and the km executables built by CI for the five
platforms (release profile, not PGO).
