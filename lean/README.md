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

### Full pure ELC normal forms — `ContextCalculus/ELCompletion.lean`

The Rust ELC worker's pure route accepts this normal-form vocabulary: NF1–NF7,
explicit top and bottom, existential bottom propagation, role hierarchy,
reflexive roles, and role chains.

- `sub_sound` / `edge_sound` prove soundness of every completion rule;
- `canon_models` constructs the canonical model over contexts not labelled
  bottom and proves that it satisfies every normal form;
- `top_bottom_sound` / `top_bottom_complete` justify the ELC inconsistency
  readout;
- `subsumption_complete` proves named-concept completeness, with an
  unsatisfiable subject represented by its bottom label.

These results certify the mathematical closure relation. The executable wire
checker connects the optimized materialization and ID-level output filter to
this relation. The normal-form recognizer, OWL translation, residual certificate
modes, and ID-to-IRI presentation remain separate obligations.

### ELC frontend normalization — `ContextCalculus/ELNormalization.lean`

`SourceAxiom` gives semantics to the EL axioms reconstructed from normalized
frontend Horn clauses. `normalizeDirect` covers top inclusion, unary and binary
conjunction, bottom, existential introduction and elimination, role inclusion,
role chains, and reflexivity. `normalizeDirect_sat_iff` proves each successful
translation preserves and reflects satisfaction, while `models_direct_iff`
lifts the result to complete directly normalized axiom lists. N-ary conjunction
expansion uses an extended concept signature whose fresh concepts denote exact
prefix intersections. `compileConjunction_sub_reflects` and
`compileConjunction_sub_preserves` prove subclass expansion in both directions;
the corresponding bottom theorems prove the same for disjointness chains.
Executable whole-list normalization, deterministic sorting, auxiliary-name
validation, and certificate-wire integration remain open parts of the frontend
refinement.

`ContextCalculus/ELRawNormalization.lean` models the recursive raw term and
equality-free atom envelope and supplies executable recognizers for direct ELC
clauses and paired existential-introduction clauses. The recognizers reject
split or collapsed variables, reversed role wiring, nested Skolem arguments,
and mismatched source/function pairs. `rawExistentialPair_sat_iff` proves the
paired raw clauses equisatisfiable with `A ⊑ ∃R.B` by extracting and extending
the Skolem function interpretation. The same module proves semantic
equivalence for every canonical direct raw family: subclass and bottom bodies,
existential elimination in both atom orders and its top-filler form, role
inclusion, reflexivity, and connected role chains in both orders. The remaining
`RawDirectEvidence` and `RawDirectCertificate` types make normalization
proof-producing: `certifyRawDirect` returns the source axiom together with the
exact canonical input equality and semantic witness, or fails closed. Whole-list
normalization is certified for direct forms by `RawDirectListEvidence.models_iff`
and executable `certifyRawDirectList`. For already paired existential entries,
`modelsRawExistentials_sat_iff` proves that globally unique Skolem IDs permit
one shared raw interpretation and preserve and reflect the complete source
existential list. `certifyRawELList` then produces indexed evidence for a mixed
list of direct clauses and frontend-adjacent existential pairs, rejects orphaned
halves and reused function IDs, and yields the whole-list equivalence theorem
`RawELListCertificate.models_iff`. Proving the adjacency invariant against the
Rust stream and the certificate-wire connection remain open. For conjunction
normalization, `certifyNaryConjunction` validates the exact NF2 prefix chain and
`NaryConjunctionCertificate.sat_iff` proves that the chain preserves and
reflects source models while fixing all source symbols. Whole-ontology
composition is carried by `SourceOntologyNormalEvidence.models_iff`, and
`RawToNormalCertificate.models_iff` connects an exact mixed raw stream to its
complete shared NF1–NF7 ontology. Wire version 5 carries that raw stream,
finite variable signature, Rust's symbol table, and exact conjunction-prefix
origins. `ELCompletionWire` checks the reconstructed normal ontology against
Rust's emitted ontology before accepting its completion certificate.

### Fail-closed portfolios and routing — `ContextCalculus/Certification.lean`

Workers have four explicit outcomes: publish, defer, error, and timeout. The
module proves that sequential fallback preserves soundness and completeness
when the selected portfolio is sound and covers the input. It proves the same
for races under explicit faithfulness and liveness obligations, then composes
the result through profile-based routing. Engine-specific and router-refinement
proofs must discharge those obligations; the generic theorems do not assume
that the Rust implementations already do so.

### Exact ELC state contract — `ContextCalculus/ELCompletionRefinement.lean`

This module isolates the representation-refinement target for
`elcomplete.rs`. `ClosedState` says that a materialized pair of subsumption and
edge relations contains Rust's initialization facts and is closed under every
pure ELC rule. `SoundState` says every stored fact has a derivation.

- `ClosedState.sub_complete` / `edge_complete` prove closure completeness;
- `sub_iff_of_exact` / `edge_iff_of_exact` prove extensional equality when the
  state is also sound;
- `entails_iff_materialized` proves the taxonomy readout exact;
- `unsat_iff_materialized` proves the inconsistency readout exact.

The executable proof must still show that Rust's recognizer and worklist
produce a state satisfying these two structures. The contract makes this a
finite list of implementation obligations rather than another semantic-model
proof.

### Executable ELC proof traces — `ContextCalculus/ELCompletionCertificate.lean`

This module defines a finite certificate step for every pure ELC inference and
an executable `checkTrace`. The checker validates source normal forms and
requires each premise to occur later in the reverse dependency trace.
`checkTrace_sound` proves every accepted fact derivable, while
`checkedTrace_soundState` turns acceptance into the `SoundState`
obligation used by the materialization theorem. `checkClosedTrace` exhaustively
checks the complementary `ClosedState` obligation over finite interned
signatures. `checkedTrace_exact` proves that passing both executable checks
yields exact taxonomy and inconsistency answers. `ELCompletionWire.lean`
discharges the finite Rust certificate wire obligation for normalized pure ELC.

### ELC wire checker — `ContextCalculus/ELCompletionWire.lean`

The versioned JSON decoder validates every numeric id against a finite `Fin n`
signature before constructing clauses or proof steps. Version 4 also validates
the exact raw ontology, variable IDs, and collision-free semantic origin table,
then invokes `certifyRawToNormal` and compares the resulting normal ontology
extensionally with Rust's emitted forms. The native
`elc-cert-check` executable checks the trace, closure, complete active Rust
context set, materialized Rust subsumption and edge stores, ID-level output,
finite symbol table, named output, and inconsistency flag.
It decodes residual source clauses, local variable/function origins, compiled
atoms, and canonical witness pins, then independently checks the exact formal
compilation relation. The production worker does not yet publish residual
answers through this certificate.
`active_subsumption_exact` proves the active materialization semantically
exact. `public_subsumption_sound` and
`public_named_subsumption_sound` prove publication soundness; their
`complete_of_satisfiable` counterparts prove completeness for reportable
subsumptions of satisfiable subjects. `public_inconsistent_exact` proves the
published flag equivalent to semantic unsatisfiability. The Rust worker invokes this executable when
`KM_ELC_LEAN_CERT_CHECKER` is set and declines without output if generation,
serialization, process execution, or verification fails. On acceptance it
publishes the checked named relation directly.

### Hypertableau certificate checkers — `ContextCalculus/HypertableauWire.lean`

`HypertableauEqualityNormalization.lean` proves the preprocessing step used for
positive equality premises. A certificate supplies equality paths from every
variable to its selected representative and checks that every removed premise
collapses. `BodyEqualityNormalization.modelsClause_iff` proves per-clause model
equivalence, and `models_iff` lifts it to whole ontologies. The Rust producer now
performs this normalization before trigger indexing. Encoding the source
ontology and paths in the executable wire checker remains open.

`Hypertableau.lean` defines the guarded finite-branch semantics, sound
hyper-rule branching, exhaustive refutation trees, and canonical-model endpoint.
`HypertableauCertificate.lean` checks finite saturated SAT branches, while
`HypertableauRefutationCertificate.lean` checks every child of a finite UNSAT
refutation. `HypertableauWire.lean` bounds-checks versioned JSON and dispatches
only decoded evidence to those proved checkers. Build the native executable with
`LEAN_NUM_THREADS=2 lake build ht-cert-check`. The separate complete-taxonomy
decoder is built with
`LEAN_NUM_THREADS=2 lake build ht-taxonomy-cert-check`.
The SAT checker is exact for its endpoint contract:
`checkSat_eq_true_iff_valid` proves acceptance equivalent to guardedness, clash
freedom, witness completion, and saturation. For a blocked fold,
`FiniteFoldCertificate.check_complete_of` makes those same four properties the
complete concrete acceptance obligation.

`HypertableauEqualityCertificate.lean` and
`HypertableauEqualityWire.lean` add version-2 evidence with exact
finite equality closure. The checker validates every merge, representative,
and path to that representative without assuming distinct certificate nodes
denote distinct domain elements. `ht-cert-check` dispatches both versions; the
same version-2 decoder is available separately with
`LEAN_NUM_THREADS=2 lake build ht-eq-cert-check`. Version 2 accepts global SAT
evidence only after constructing a nonempty quotient model and checking every
guarded grounding modulo equality. It checks both polarities of individual
subsumption and concept-satisfiability queries against quotient models or
closed equality-aware refutations. Complete equality-aware taxonomy batch
evidence remains fail-closed.
`checkEqSat_eq_true_iff_valid` also proves the converse: equality-path-valid,
guarded, quotient-clash-free, witness-complete, saturated endpoints are always
accepted. Thus checker rejection corresponds to a concrete failed endpoint
obligation rather than an uncharacterized implementation gap.
The cardinality checker has the matching exactness result:
`checkEqSatWithCardinality_eq_true_iff` proves acceptance exactly when that
endpoint contract holds and the equality-quotient model satisfies every
minimum or maximum cardinality definition.
The equality-aware blocked-fold boundary exposes the same contracts through
`FiniteEqFoldCertificate.check_eq_true_iff_materialize_valid` and
`checkWithCardinality_eq_true_iff`. These theorems deliberately leave concrete
fold saturation preservation as an explicit obligation.
`FiniteEqFoldCertificate.check_of_base_valid_roleFree` discharges that
obligation completely for role-free clause bodies. Supporting lemmas show that
all folds preserve equality validation, quotient clash freedom, existing
witnesses, and base closed facts. Role-bearing bodies remain the precise
pairwise-blocking proof boundary.
`FiniteEqFoldCertificate.mem_foldedEdges_iff` gives exact provenance for copied
edges, and `closedRole_implication` uses it to preserve every base role
implication through the fold. This covers the sub-role/same-orientation bridge
part of the remaining role-bearing boundary.
Full pairwise signature equality now implies the explicit fold-label contract.
Using it, `closedForwardConcept_implication` and
`closedTargetConcept_implication` preserve the two normalized single-edge
concept propagation orientations across copied blocker edges.
Certified folds now materialize incoming and outgoing blocker edges. The
outgoing-only construction was incomplete for reversed role heads.
`closedInverseRole_implication` proves the corrected fold preserves
`R(x,y) → S(y,x)`, while the earlier propagation theorems now cover either
orientation of copied premise edge.

The production Rust worker obtains its global consistency verdict and evidence
from the total certification search, then publishes only after the native Lean
checker accepts that evidence. It does not use the optimized tableau as a
verdict oracle at this boundary. Its certified constructor uses direct full-label pairwise
blocking, including predecessor labels and bidirectional connecting-role sets,
and materializes those folds as ordinary candidate edges. It also emits
exhaustive global UNSAT refutations when finite search closes over concept,
role, existential, and equality facts. Certified full-pairwise mode lazily
enumerates every finite grounding and doubles the node frontier only when a
branch reaches it. Explicit diagnostic node limits remain fail-closed.
It can also emit individual subsumption and unsatisfiable-concept refutations,
plus finite countermodels for non-subsumption and concept satisfiability. The
checker verifies that each refutation starts from exactly the declared query
labels and that every countermodel contains its declared query labels.
`HypertableauTaxonomyCertificate.lean` proves exact taxonomy materialization
from a complete set of either-polarity decisions.
`HypertableauTaxonomyWire.lean` accepts exactly one concept decision per named
class and a square row-major decision matrix for all ordered pairs. The Rust
worker publishes the named taxonomy directly from this matrix only after both
the global and taxonomy native checkers accept.
`HypertableauMixedTaxonomyWire.lean` preserves that version-1 format and adds a
version-2 matrix in which each cell may independently contain the ordinary
finite evidence or equality-quotient evidence. Both variants refine to the
same semantic decision before total matrix coverage is proved, so an accepted
mixed matrix has the same exactness theorem as an equality-free matrix.
The refutation checker has an explicit fresh-witness rule: it verifies that the
target node occurs in no prior fact, binds that node to the semantic existential
witness, and then checks the recursively materialized edge and filler label.
The Lean checker treats all Rust choices as untrusted and accepts only an exact
finite model or a closed refutation tree. Lean also proves the finite signed-label
bound behind equality/subset blocking: every path longer than the number of
possible signed labels contains an earlier exact-label blocker, and transfer to
that blocker preserves all signed concept facts. The finite-fold checker then
validates role and witness obligations on the materialized graph. Finite
successor slots and the role-sensitive signature depth bound also construct a
finite type of blocked node addresses, supplying the finite-node premise for
the strict branch-progress theorem. Lean further proves that strictly increasing
child identifiers and refusing to expand an earlier-signature duplicate exclude
every overlong all-expanded path. Certified Rust mode 6 checks those concrete
predecessor and terminal expansion invariants before publishing SAT evidence.
For ALC(H), terminal labels equal the relevant expansion-time parent labels.
Iterative deepening removes the producer's historical assignment and implicit
node caps. Once a blocked node
universe is fixed, `HypertableauTermination.lean` proves that ordinary,
equality-aware, and cardinality-aware evidence search has only finitely many
strict branch updates and finitely many duplicate-free progress traces. The
Rust producer enforces that strict-progress premise at every recursive
certificate call. A well-founded exhaustive-search theorem now proves that a
finite strict-growth transition system closes its root or reaches an open leaf.
`HypertableauTerminal.lean` specializes this to HT: once concrete transitions
expose every obstruction and combine exhaustive closed children using
`Refutes`, the root is refuted or a reachable canonical branch models the exact
ontology. `HypertableauSearch.lean` gives the exact finite representation of
labels, edges, and obligations, proves both representation round trips, and
proves strict growth for each absent branchable head and fresh witness. Its
exhaustive step type has exactly one child per disjunct or one fresh-witness
child; refuting those children constructs the matching `Refutes` parent. The
finite completeness theorem is specialized directly to these guarded facts.
The active-node set is now defined exactly from labels, both edge
endpoints, and obligations. Freshness is equivalent to absence from that set,
and spare finite capacity yields a fresh target. A blocked address below the
signature depth can be extended by one successor slot; an unused exact
extension is fresh. `RootedAddressRefines` checks that an occupied canonical
extension already carries the exact role edge and filler label, and
`atWitnessAddresses_obligationAddressInvariant` turns that fact into the fresh
supply required by exhaustive search.
`HypertableauTerminal.lean` also proves that every branch exposes a
clash, an unwitnessed existential, an undischarged grounding, or an exact
canonical model. `HypertableauRoleBlocking.lean` proves the certified full
pairwise signature is finite and repeats on long paths, and the Rust certified
constructor uses the corresponding direct blocking mode. Every concept and
ordered subsumption cell in the complete taxonomy matrix now uses the same
total certification search from its exact root labels. Inverse roles, nominals,
and native ABoxes remain outside this certified HT fragment.

### Equality-aware HT refutations – `ContextCalculus/HypertableauEquality.lean`

`HypertableauEquality.lean` extends abstract branch states with an explicit node
equivalence relation. A realization must map equivalent nodes to one domain
element. Equality-head assertion takes the generated equivalence closure, and
`EqState.merge_realized` proves that every model satisfying the equality head
realizes the merged branch. The generalized branch theorem accepts concept,
role, existential, and equality heads without a semantic side condition.

`EqRefutes.sound` composes equality merges with fresh existential witnesses and
detects complementary labels modulo node equivalence. The finite equality
checker refines the implementation's merge forest using explicit
representatives and paths. Version-2 JSON and the Rust producer connect global
and individual-query SAT/UNSAT evidence to this checker. The bounded Rust
refutation search and its Lean contract distinguish checked closure, an open
branch, and an exhausted frontier. Saturated open leaves now retain their exact
active-node quotient and become conclusive only when the executable equality
model checker accepts them. Checked closure and checked quotient models cover
both terminal meanings.

`HypertableauEqualityBlocking.lean` defines the corresponding full pairwise
signature over equality-closed labels and role edges. It proves finite
signature repetition and the resulting injective-path depth bound. The checked
frontier wire connects this bound to total executable iterative deepening.

`HypertableauEqualityBlockingCertificate.lean` treats the concrete fold as
untrusted input, materializes blocker edges modulo the supplied checked
equality quotient, and proves that acceptance by the ordinary equality model
checker yields a model of the exact ontology. The Rust producer uses the same
closed pairwise signature and fail-closed materialization boundary.

`HypertableauEqualitySearch.lean` carries the same checked rooted-address
frontier used by equality-free search. Its doubling theorem proves that a
frontier cannot recur forever, so equality-aware search eventually returns a
checked quotient model or checked refutation. The Rust frontier producer
reconstructs and validates those exact addresses before deepening.

The distinct-cardinality search uses the same three-way boundary through
minimum expansion and maximum-merge branching. Its checked closure theorem
excludes models satisfying both the exact ontology and its decoded cardinality
definitions. `HypertableauCardinalityFrontierWire.lean` checks tagged rooted
addresses for ordinary witnesses and for each minimum-definition witness
index. `HypertableauCardinalitySearch.lean` proves that these checked frontiers
cannot persist through iterative doubling. Equality-quotient pairwise blocking
folds a saturated open branch into a finite candidate, and
`FiniteEqFoldCertificate.checkWithCardinality_models` proves that an accepted
candidate models both the exact ontology and all decoded cardinality
definitions. Consequently the checker-gated distinct-cardinality fragment has
a total sound and complete decision boundary: a checked model or checked
refutation is conclusive, malformed evidence fails closed, and a checked
frontier eventually disappears.

### ELC residual canonical-model contract — `ContextCalculus/ELResidualCertificate.lean`

This module proves the semantic principle used by plain `CertMode::Check`.
Adding arbitrary residual axioms preserves soundness of the ELC closure. If the
ELC canonical model satisfies those residual axioms, the same closure is also
complete for taxonomy and exact for inconsistency. The executable corollaries
compose this result with `ClosedState` and `SoundState`.

The canonical domain is restricted to live members of an explicit,
signature-closed concept set. This matches Rust's `concept_names` enumeration
and excludes role-only interned IDs. The module also defines Rust's compiled
concept/role/equality atom language with pinned witness variables and proves an
independent finite Boolean checker equivalent to its clause semantics. The
remaining boundary is proving Rust's source residual compiler and optimized
join checker refine this finite contract. Model-repair mode requires a separate
model-transformation certificate.

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
