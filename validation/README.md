# Validating the actual reasoner against the Lean spec

This directory cross-checks the **actual Rust reasoner** (`kobayashi-marust` (the `engine/` crate),
the compiled `kobayashi-marust` binary) against the **Lean soundness spec**
(`lean/ContextCalculus/Basic.lean`), per run, by a *Lean-verified certificate
checker*.  Proving the Rust source itself in Lean is out of scope; instead every
verdict the reasoner emits is turned into a machine-checked theorem.

## How it works

Three Lean-verified checkers (all `sorry`-free, reusing the generic
`resolution_sound` from `Basic.lean`):

- `ContextCalculus/Checker.lean` — propositional resolution checker;
- `ContextCalculus/CheckerFO.lean` — first-order checker with one-level
  successor terms `fₖ(x)` (universal instantiation + paramodulation into a
  literal);
- `ContextCalculus/CheckerTerm.lean` — **first-order over a term algebra**
  `FTerm` (`var i` / `app f t`), so **nested** successors `f(g(x))` are
  first-class.  This is the checker the validation now uses.  It covers **Succ**
  (existential successor / value restriction), **number restrictions**, **subterm
  paramodulation** (superposition), and the transitive-role / successor-chain
  verdicts that build a successor of a successor.  `certifies_subsumptionT` /
  `certifies_unsatT` turn an accepted certificate into `O ⊨ A ⊑ B` / `O ⊨ A ⊑ ⊥`
  over every first-order model.

A certificate is an ordered derivation of the verdict clause from the **genuine
premises** (ontology clauses, used via universal instances, plus the context core
`→ A(x)`); engine output is *never* assumed as an axiom — each verdict is
independently re-derived.

`engine/py/certgen_term.py` runs the real engine, and for every
verdict re-derives it with a layered search (each layer emits steps the checker
re-checks): (a) propositional resolution; (b) unit-driven **Horn forward
chaining** over the term algebra (instantiating rules at the successor terms
their bodies match, with Factor equalities and paramodulation); and (c) the
**complete disjunctive saturation** -- ground resolution over matching-driven
instance generation (positive hyperresolution), which handles disjunctive heads
*and* nested successors *together* (not just Horn).  It emits:

```lean
theorem exists_0_A_sub_D {D : Type} (M : TModel D)
    (hO : ∀ p ∈ O_exists, valid M p) (a0 : D) (hA : M.conc 1 a0) : M.conc 4 a0 :=
  certifies_subsumptionT O_exists 1 4 cert_exists_0 (by decide) M hO a0 hA
```

The `by decide` is discharged by the **kernel** (no `native_decide`, no `sorry`):
`#print axioms` reports only `[propext, Quot.sound]`.  So a green
`lake build Validation` means the verified checker has certified each verdict as a
genuine logical consequence — the reasoner's output is correct on these runs.

## Run it

```sh
./validation/run.sh        # build engine, regenerate certificates, kernel-check
```

The generated proofs live in `lean/Validation/` and are part of the default
`lake build` (the `Validation` library), so they are re-checked with the rest of
the formalization.

## What is validated, and the honest boundary

Validated (kernel-checked theorems over real engine runs):

| input        | verdicts certified                                              |
|--------------|----------------------------------------------------------------|
| `disj`       | `A ⊑ D`, `B ⊑ D`, `C ⊑ D` — **disjunctive** subsumption (the case the old Horn reasoner got wrong) |
| `disjoint`   | `A ⊑ ⊥` (disjointness clash), `A ⊑ C`                          |
| `hierarchy`  | 12 subsumptions of a kinship-style class hierarchy (`Father ⊑ Person`, `Mother ⊑ Female`, …) |
| `exists`     | `A ⊑ D` via **`∃R` / value restriction** (Succ), `B ⊑ C`       |
| `numrestr`   | `A ⊑ ⊥` via **number restrictions** (`≥2 R.C ⊓ ≤1 R.C` clash, Eq/Factor) |
| `paramod`    | `A ⊑ D` via **paramodulation into a literal** (functional role rewrites `C(f₂)→C(f₁)`) |
| `disjsucc`   | `A ⊑ D` from `A ⊑ ∃R.(B⊔C), ∃R.B ⊑ D, ∃R.C ⊑ D` — **disjunction over a successor** (only the complete disjunctive engine derives it; the propositional and Horn layers both fail) |

Sourced from **real `.ofn` ontologies** through the front-end (`py/frontend.py`,
an OWL functional-syntax parser reusing moose's real `normalise` + `augment`):

| `.ofn` input          | verdicts certified                                    |
|-----------------------|-------------------------------------------------------|
| `trans_test.ofn`      | `B ⊑ D` and **`A ⊑ D`** (transitive role; `A ⊑ D` is built through the **nested** successor `f(g(x))`) |
| `kinship.ofn`         | **all 21** subsumptions, incl. `Queen ⊑ Royal`, `Queen ⊑ Female` (**nominal** `Queen≡{Elizabeth}`), the `…⊑Narcissist` / `Grandparent⊑…` successor chains, … — matching the HermiT oracle exactly |

Coverage and boundary:

- **Rules covered.**  Resolution (Core / Hyper / Pred / Elim — disjunctive
  reasoning), **Succ** (existential successors / value restrictions), **number
  restrictions** (`Eq` / `Factor`), **subterm paramodulation** (superposition,
  `CheckerTerm.paraResolvent_sound` + `evalL_rwL`), **nominals** (ABox-grounded,
  via `kinship.ofn`), **nested successor terms** `f(g(x))` (transitive-role /
  successor-chain subsumptions), and **disjunction over a successor**
  (`disjsucc`), via the term algebra in `CheckerTerm`.
- **Re-derivation is complete, not Horn-limited.**  The generator's third layer
  is a complete disjunctive saturation (positive hyperresolution over the term
  algebra): it instantiates rules at the successor terms their bodies match and
  resolves the resulting ground clauses *carrying residual disjunctions*, so it
  certifies verdicts needing disjunctive case-splitting and nested successors at
  once (the `disjsucc` benchmark).  The earlier Horn layer is a performance
  fast-path, not a coverage limit.
- **Front-end.**  `py/frontend.py` parses `.ofn` to moose's SROIQ AST and runs
  moose's real `normalise`/`augment` (no `pyhornedowl`): the `.ofn → normalised
  clauses` step *runs*, and the verified checker certifies the engine's verdicts
  on the resulting clauses.  The certified verdict set equals the HermiT oracle's
  after filtering normalisation-internal concepts `Q_*`/`__*` (e.g. `kinship`
  21/21).
- **Residual.**  The disjunctive layer is *bounded* (a clause cap): for an
  ontology with very many excluded-middle definitions it may give up rather than
  exhaust memory — the classical remedy is the ordered / pay-as-you-go strategy
  (Bachmair–Ganzinger), which we do not re-mechanize.  All present benchmarks are
  certified within the bound.
