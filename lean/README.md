# Lean formalization of the disjunctive context calculus

Lean 4 (`v4.30.0-rc2`) development accompanying `../engine`.
`Basic.lean` is self-contained (Lean core only); `CompletenessProp.lean` uses
mathlib.

## What is proved (`sorry`-free)

### Soundness — `ContextCalculus/Basic.lean`
Mirrors the Rust datatypes (`Term`, `Pred`, `Lit`, `Clause`) and proves the
engine derives only entailed clauses:

- `resolution_sound` — one resolution step is model-preserving;
- `derivable_sound` — every derived clause is a logical consequence
  (Core / Hyper / Pred / Succ / Elim are resolution instances);
- `subsumption_sound` — deriving `→ B(x)` in the context of `A` gives `O ⊨ A ⊑ B`;
- `unsat_sound` — deriving the empty clause gives `O ⊨ A ⊑ ⊥`;
- `paramodulation_sound` — the `Eq` rule (rewriting under a derived equality, the
  `Factor`/number-restriction machinery) is sound under a congruence model.

Axiom audit: every theorem reduces to `[propext]` only.

Completeness is proved for the **two foundational directions** the calculus
combines — disjunction and existentials — by the two methods the thesis uses.

### Completeness, disjunction direction — `ContextCalculus/CompletenessProp.lean`
**Refutational completeness of propositional resolution** (the fragment on which
the earlier Horn-only reasoner was unsound):

- `completeness : Unsat S → Derivable S ⊥` — every unsatisfiable finite clause
  set is refuted by resolution.

Proof: induction on the number of atoms, Davis-Putnam conditioning
(`condTrue`/`condFalse`), lifting lemmas `lift_true`/`lift_false`, invariants
`condTrue_pos_no_p`/`condFalse_neg_no_p`.  `sorry`-free; axioms `[propext,
Classical.choice, Quot.sound]`.  On the function-free fragment the engine's
saturation *is* propositional resolution, so this is soundness + completeness of
the disjunctive core.

### Clause-level completeness, on the engine's own clauses — `ContextCalculus/CompletenessClause.lean`
`CompletenessProp` proves completeness over a *separate* set-based clause type;
this file transports it onto the engine's actual `Clause Lit` / `Derivable` (the
ones `Basic.lean` proves *sound*), via a clause map `toP` (lists→finsets) that
commutes with resolution (`toP_resolvent`) and a step-for-step lifting (`lift`):

- `completeness` — `Basic.Derivable` refutes any propositionally unsatisfiable
  finite clause set (derives the empty clause);
- `unsat_complete`, `subsumption_refut_complete` — the classification corollaries
  (`O ⊨ A ⊑ ⊥` / `O ⊨ A ⊑ B` ⇒ the engine derives `⊥`);
- `subsumption_refut_iff`, `entails_refut_iff` — the **decidability capstone**:
  pairing these with `Basic`'s soundness, `O ⊨ A ⊑ B` (and more generally `O ⊨ C`
  for any ground clause `C`) holds **iff** the engine refutes `O` + ¬`C`;
- `model_existence` — contrapositive: a clause set the engine cannot refute has a
  model.

`sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`.  This is the
completeness counterpart of `Basic`'s soundness on the **ground/propositional**
layer (Core/Hyper/Pred/Elim).  The orthogonal term-generating `Succ` layer
(instantiating clauses at fresh successor terms `f(x)`) is the existential
direction below; fusing the two into one first-order completeness theorem over a
saturated term set remains open.

### Completeness, existential direction — `ContextCalculus/CompletenessEL.lean`
**First-order completeness of consequence-based reasoning for EL**, via a
canonical model with genuine existential witnesses (the ELK case the
Tena-Cucala calculus generalises, and the existential/Succ–Pred direction the
propositional theorem does not cover):

- closure `Sub`/`Edge` = the engine's Core/Hyper/Succ/Pred on Horn EL clauses;
- `canon_models : models (canon O) O` — the canonical interpretation (domain =
  concept names, existentials witnessed by `Edge`) models the ontology;
- `completeness : (O ⊨ a ⊑ C) → evalN (canon O) C a` — semantic entailment is
  derived by the closure;
- `sub_sound` — soundness of the closure (mutual recursor).

All of `CompletenessEL` is **fully constructive — no axioms at all**, `sorry`-free.
This is genuinely first-order (∃R.C, roles, role hierarchy, canonical model),
not propositional.

### Completeness, disjunction × existential interaction — `ContextCalculus/CompletenessContext.lean`
The propositional and EL files settle the two directions *separately*.  Their
**interaction** — disjunction *and* existentials at once — is the genuinely open
case, because a disjunctive ontology has no least model (the EL construction
breaks) while the propositional theorem has no witnesses.  This file closes it
for ALC by the construction the context calculus actually computes: a **finite
filtration / good-type model** over a saturated context structure.

- a *context* is a `type` (a finite set of concept names — a propositional model
  of the GCIs); disjunction lives here, a type having chosen its disjuncts;
- an *edge* is a `compat`ible pair of types (∀-consequences forward, `∃r.d⊑c`
  back) — the Succ/Pred coherence;
- a type is **`Good`** when it lies in a self-realising set (every existential it
  forces has a witnessing edge inside the set); the good types are exactly the
  contexts surviving saturation, and type-elimination *is* the saturation.

Theorems (`sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`):

- `canon_models : models (canon O) O` — the canonical interpretation (domain =
  good types, existentials witnessed by genuine good-type edges) is a first-order
  model of the ontology;
- `sat_iff_good` — a concept is satisfiable over **all** interpretations iff it
  lies in some good type.  The `→` direction is the *filtration*: any model,
  however large or infinite, collapses to the finite self-realising good-type
  set.  So the construction is sound **and refutation-complete**;
- `subsumption_complete` — `O ⊨ A ⊑ B` iff every good type with `A` has `B`;
- `unsat_iff_no_good` — `O ⊨ A ⊑ ⊥` iff no good type contains `A` (precisely what
  saturation reports when it eliminates every context whose core contains `A`).

This is strictly more than the two earlier files (it handles disjunction *and*
existential witnesses together) and more engine-faithful than the prior moose
ALC proof, which uses *infinite* Lindenbaum/Zorn maximal types rather than the
finite good-type structure the reasoner actually computes.

### The merging features — `ContextCalculus/CompletenessEq.lean`
The filtration above is the ALC slice; it breaks once the language can force two
successors to be the **same** element (`≤1 R`, `{o}`, inverse roles), because the
model becomes a **quotient** of the Herbrand universe by an equality relation,
not a set of independent types.  This file builds that equality-quotient Herbrand
model — the construction the context calculus computes after grounding a
saturated, terminated (blocked) context structure to ground clauses over the
atoms `C(x)`, `R(x,y)`, `x≈y`:

      π ⊨ G  (a propositional model of the grounding; exists iff G is clash-free)
        ⟶  the quotient  T / ≈π  with  x ≈π y := π(x≈y),
            the congruence the equality axioms in G force π to respect.

Merging *is* the quotient; functional roles are a binary equality clause `π`
satisfies; nominals are `C(x)→x≈o`; inverses are role-atom clauses.  Theorems
(`sorry`-free; axioms `[propext, Classical.choice, Quot.sound]`):

- `congruenceModel_models` — the quotient of any `π ⊨ G` is a genuine first-order
  model of the ontology, **including functional roles (`≤1 R`), nominals, inverse
  roles**, and role hierarchy, on top of the disjunctive ALC core;
- `respectsEq_of_grounds` — the congruence is **derived** from the equality
  axioms in `G`, never assumed;
- `congruenceModel_models` also covers **general qualified number restrictions
  `≤n R.C`** (`OClause.atMost`): the quotient satisfies `≤n` because the `Factor`
  distinctness clauses, instantiated over every `(n+1)`-tuple, force a pigeonhole
  collapse of any `n+1` successors into `≤n` merge-classes;
- `ground` / `grounds_ground` — a **concrete grounder**: over a finite vocabulary
  and Herbrand universe it emits the equality axioms and every ontology instance,
  and `grounds_ground` proves the emitted set satisfies `Grounds`.  So `Grounds`
  is *realised by a verified function*, not an assumed interface;
- `herbrand_complete` / `herbrand_complete_ground` — if the (concrete) grounding
  is **clash-free** (propositional resolution does not derive `⊥`) then `O` has a
  model.  Model existence is supplied by `PropRes.completeness` (clash-free ⟹
  satisfiable); there is **no assumed Herbrand lemma and no assumed grounding**.
  Contrapositively, an unsatisfiable ontology is refuted.

`herbrand_complete_ground` is the capstone: over a finite vocabulary/universe,
clash-freedom of the concrete grounding yields a first-order model covering
disjunction, existentials, universals, role hierarchy, inverse roles, nominals,
and qualified number restrictions `≤n R.C` — the full NExpTime feature set, as a
single quotient construction.

### Blocking termination — `ContextCalculus/Termination.lean`
Discharges the `Fintype` (finite Herbrand universe) premise of `CompletenessEq`.
The engine attaches a **core** (a `Finset CN`) to each context; blocking refuses
to expand a context whose core already appeared on the branch, so every branch is
a list of *distinct* cores.  Since cores live in the finite `Finset CN`:

- `branch_depth_bound` / `context_branch_bound` — every branch has length
  `≤ Fintype.card (Finset CN) = 2^|CN|`;
- `no_infinite_branch` — there is no infinite branch (it would inject `ℕ` into the
  finite core type);
- `reachable_finite` — the set of all branches is finite, and `blockedUniverse`
  is a `Fintype` — exactly what `CompletenessEq.herbrand_complete_ground` needs.

This is the König argument behind blocking (finite branching + finite depth ⟹
finite completion ⟹ saturation halts).

### Optimized saturation ≡ ground resolution — `ContextCalculus/Equivalence.lean`
The engine saturates a context structure, not a flat clause set.  We model its
output faithfully as a `Saturation S N`: the finite set `N` it produces is a
superset of `S`, **resolution-closed**, and **sound** (every produced clause is
resolution-derivable from `S` — every context rule is a resolution/paramodulation
step, the content of `Basic.lean`).  Then (`sorry`-free):

- `derivable_bot_iff_unsat` — ground resolution decides satisfiability:
  `Derivable S ⊥ ↔ Unsat S`;
- `saturation_refutes_iff_derivable` — `⊥ ∈ N ↔ Derivable S ⊥`: the saturation
  refutes exactly when ground resolution does;
- `saturation_refutes_iff_unsat` — and exactly when `S` is unsatisfiable;
- `engine_agrees_ground` — on the concrete grounding: the engine's saturation
  refutes iff ground resolution does, and non-refutation yields a genuine model
  (the congruence quotient), so a non-refutation is justified, not a missed proof.

The full resolution closure is finite (ground atoms are finite) and is what the
engine's **complete (trivial-strategy)** configuration computes, so the model is
non-vacuous and faithful.

### Validating the actual reasoner — `Checker.lean`, `CheckerFO.lean`, `CheckerTerm.lean` + `../../validation/`
The files above formalize the *calculus*; these validate the *actual Rust binary*,
per run, with Lean-verified certificate checkers:

- `Checker.lean` (propositional) — `checkCert_sound`, `certifies_subsumption`,
  `certifies_unsat`: a resolution certificate over the genuine premises certifies
  the verdict (`O ⊨ A ⊑ B`, `O ⊨ A ⊑ ⊥`), reusing `resolution_sound`;
- `CheckerFO.lean` (first-order, one-level successors) — adds sound **universal
  instantiation** (`inst_valid`) and **paramodulation into a literal**
  (`paraResolvent_sound`), encoding a successor as a one-level term `fₖ(x)`;
- `CheckerTerm.lean` (first-order over a **term algebra**) — generalises
  `CheckerFO` by replacing the integer term code with a genuine term algebra
  `FTerm` (`var i` / `app f t`), so **nested** successors `f(g(x))` are
  first-class.  It reuses the *generic* resolution core of `Basic.lean`
  (`resolvent`, `resolution_sound`) at `Atom := FLit`, and adds, all over the
  term algebra: substitution soundness `inst_valid` (now **unconditional** — no
  `clFree` restriction, since substitution into a term algebra always commutes
  with evaluation), subterm paramodulation `paraResolvent_sound` /
  `evalL_rwL` / `evalT_rwT`, and the checker `certifies_subsumptionT` /
  `certifies_unsatT`.  This is what closes the transitive-role / successor-chain
  verdicts that needed a successor *of* a successor.

`validation/run.sh` runs the real engine, has `certgen_term.py` independently
re-derive every reported verdict from the genuine premises with a layered search
(engine output is *never* an axiom): (a) propositional resolution; (b) unit-driven
Horn forward chaining over the term algebra; and (c) a **complete disjunctive
saturation** — ground resolution over matching-driven instance generation
(positive hyperresolution), which carries residual disjunctions, so it handles
disjunctive case-splitting *and* nested successors **together** (not just Horn).
It emits the `Validation` library where each verdict is a theorem proved
`by decide` — kernel-checked, `#print axioms` = `[propext, Quot.sound]` only.
A green `lake build Validation` certifies the actual reasoner's verdicts:
disjunctive subsumption, disjointness `⊥`, a hierarchy, `∃R`/value restriction,
a number-restriction clash, **paramodulation into a literal**, **disjunction over
a successor** (`disjsucc`: `A ⊑ ∃R.(B⊔C), ∃R.B ⊑ D, ∃R.C ⊑ D ⊢ A ⊑ D`, which only
the complete engine derives), **nested-successor subsumptions**
(`trans_test.ofn`'s `A ⊑ D`, built through `f(g(x))`), and — through the real
**`.ofn` front-end** (`py/frontend.py`, reusing moose's `normalise`) — all **21**
subsumptions of `kinship.ofn` (incl. the nominal `Queen ≡ {Elizabeth}`, and the
`…⊑Narcissist`/`Grandparent⊑…` chains), matching the HermiT oracle exactly
(45 verdicts total).

## What is NOT claimed

The mathematical core is fully mechanized: the Herbrand construction (soundness
`congruenceModel_models`, completeness `herbrand_complete_ground`), blocking
termination (`reachable_finite`), the saturation/ground-resolution agreement
(`saturation_refutes_iff_unsat`), and a verified checker that validates the actual
reasoner's verdicts per run (`checkCert_sound`).  The remaining boundary:

1. **Checker coverage.**  The per-run validation certifies verdicts by resolution
   (Core / Hyper / Pred / Elim), **Succ** (existentials / value restrictions),
   **number restrictions** (`Eq` / `Factor`), **paramodulation into a literal**
   (superposition), **nominals** (ABox-grounded), and — via `CheckerTerm`'s term
   algebra — **nested successor terms** `f(g(x))` (transitive-role and
   successor-chain subsumptions: `trans_test.ofn`'s `A ⊑ D`, the
   `kinship.ofn` `…⊑Narcissist`/`Grandparent⊑…` chains), and **disjunction over a
   successor** (`disjsucc`).  The `.ofn → clauses` front-end *runs*
   (`py/frontend.py`, reusing moose's `normalise`).  The certified verdict set
   equals the HermiT oracle's on every benchmark (e.g. `kinship` 21/21).  The
   re-derivation is **not Horn-limited**: its third layer is a complete
   disjunctive saturation (positive hyperresolution over the term algebra) that
   carries residual disjunctions, certifying verdicts needing disjunctive
   case-splitting and nested successors at once.  That layer is *bounded* (a
   clause cap), so on an ontology with very many excluded-middle definitions it
   may give up rather than exhaust memory — the classical remedy is the ordered /
   pay-as-you-go strategy (item 2), which we do not re-mechanize; the Horn
   fast-path keeps the common case efficient.
2. **The saturation-strategy completeness — now machine-checked (`sorry`-free).**
   The engine classifies by consequence-based *type-elimination*: seed the
   consistent candidate contexts and repeatedly discard any context whose
   existential demands are no longer realised by a surviving context, to a
   fixpoint.  `ContextCalculus/CompletenessStrategy.lean` (now imported by the
   root module, so it is part of the default `sorry`-free build) proves the
   whole chain unconditionally:
   - `good_iff` — the fixpoint equation an elimination round checks (a type is
     good iff consistent and every existential it forces has a *good* witness);
   - `goodFS_selfReal` + `selfReal_subset_goodFS` — the good types are the
     **greatest** self-realising set (the gfp of the elimination operator `step`);
   - `exists_fixed` + `saturate_fixed` — iterating `step` from the candidates
     **converges** to a fixpoint in ≤ `|candidates|` rounds (a strictly
     shrinking finite chain);
   - `mem_saturate_iff_good` — that computed fixpoint *is* the set of good types;
   - `saturate_decides` — hence the strategy's materialised set decides `A ⊑ B`
     (composing the above with `subsumption_complete`).

   `engine_decides` generalises this to an arbitrary materialised candidate set
   `U` (iterating `step` from any `U` with `goodFS O ⊆ U ⊆ cand O` converges to the
   good types and decides `A ⊑ B`).  **`engine_complete` discharges the `coverage`
   hypothesis outright**: the engine's pre-elimination candidate space, *at the
   type level*, is all of `cand O` (its disjunctive context clauses represent the
   whole consistent-type space — a few contexts standing in for it — which
   elimination trims to `goodFS`), and `goodFS O ⊆ cand O` is `goodFS_subset_cand`.
   So type-level completeness carries **no residual hypothesis** (`engine_complete`
   is in fact defeq to `saturate_decides`).  `coverage_of_seeds` records the
   reason coverage is free: a good type is consistent, and the engine seeds a root
   for every named concept.

   The **one** thing left between this and the running Rust binary is therefore
   *not* coverage but the **representation refinement**: the engine manipulates
   disjunctive context *clauses*, not enumerated types, and that its clause
   saturation computes the same `goodFS` is the disjunctive-saturation
   completeness.  Soundness of that clause engine is hypothesis-free and
   re-established on every run by the certificate checker
   (`CheckerTerm.certifies_subsumptionT`); its completeness is validated
   empirically against HermiT (byte-identical verdicts on every benchmark, and
   identical to the exhaustive trivial strategy).  Mechanising the clause-level
   disjunctive-saturation completeness is the remaining (genuinely substantial)
   theorem; it is **not** claimed here.

For context on the state of the art: the prior Lean attempt under
`moose/proofs/lean-sroiq-sdd/` proves **ALC** completeness via *infinite*
Lindenbaum types (`ALC.satC_complete`, sorry-free), but its unconditional
context-calculus statement (`TenaCucalaCompleteness`) is *proved false as stated*
(`not_TenaCucalaCompleteness`), and its context-completeness theorems **assume**
the Herbrand construction as a hypothesis (`CompositeRefutationLemma`,
`herb_models_O`) rather than building it.  The files here *build* the
construction with no assumed Herbrand lemma and no assumed grounding: the finite
filtration for disjunctive ALC (`CompletenessContext`) and the full
equality-quotient Herbrand model — disjunction, existentials, inverses, nominals,
`≤n R.C` — for the merging features (`CompletenessEq`).

## Build

```sh
lake exe cache get      # fetch prebuilt mathlib oleans
lake build
```
