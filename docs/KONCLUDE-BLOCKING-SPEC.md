# Konclude optimized blocking — faithful port spec

Extracted from `Konclude/Source/Reasoner/Kernel/Algorithm/CCalculationTableauCompletionTaskHandleAlgorithm.cpp`
(read-only). This is the ground truth to PORT (not approximate) into the KM fast
Ht. See [[feedback_port_from_konclude]].

## Terminology / directionality

- `w  = testIndi`    — the node being tested for being blocked.
- `w' = blockingIndi` — the candidate BLOCKER (an earlier node).
- `v  = getAncestorIndividual(w)` = `pred(w)` — w's tree predecessor.
- Edges iterated: `w.getSuccessorRoleHash()` indexed by `v.id` = the role links
  between `w` and its predecessor `v` (used for the inverse direction: "w is an
  inv(r)-successor of v" means `v -r-> w`).
- Flags: `PRFDIRECTBLOCKED`, `PRFINDIRECTBLOCKED` (blocker itself blocked),
  `PRFPROCESSINGBLOCKED`, `PRFBLOCKINGRETESTDUEINDIRECTBLOCKERLOSS`.

## Dispatcher — `isIndividualNodeBlocking` (~18923)

Preconditions: `|L(w)| > |L(w')|` -> false (18931); init-concept of w must be in
L(w') unless continuing (18935). Default config: `mConfOptimizedSubSetBlocking=true`
(others false) -> calls `isLabelConceptOptimizedBlocking`. Then a propagation-binding
check for nominal variables (skip until nominals matter).

## `isLabelConceptOptimizedBlocking` (~18484) — the core

B1 (18492): `isLabelConceptSubSet(L(w), L(w'))` — every (concept,neg) descriptor in
w is in w'. If not subset -> false. (NOTE: subset, like KM mode 1; NOT equality.)

B2 (18500-18560): `ancRoleHash = w.getSuccessorRoleHash()`. If none -> `return true`
(no inverse edges => B1 alone suffices). Else for each link (role r) between w and v:
  for each reapply concept conDes in `w'.getRoleReapplyIterator(r)`:
   - B2a (18530): if `(!neg & ALL/AQALL) | (neg & SOME)` (i.e. ∀r.C from w' or ¬∃r.C):
       for each operand opC (opNeg = linker.neg ^ conNeg):
         if `!L(v).containsConcept(opC, opNeg)` -> `blocked=false` (18536).
   - B2b (18547): if `(!neg & AQAND)` (transitive/automata ∀):
       if `!hasOptimizedBlockingB2AutomateTransitionOperands(concept,r,L(v))` ->
       `blocked=false`.

B3/B5 (18563-18653, only `if blocked`): at-most `≤n r.C` in w' (or ¬≥n): if v's
label lacks the operand polarity, count w''s r-successors (nominal or deeper than
w'); if `>= n` -> `blocked=false`.
B6 (18655-18683): at-least `≥n r.C` in v with n>1 and a v->w r-link: w must contain
the operands else `cBlocked=false`; if cBlocked -> `return true`.
B4 (18686-18744, `if blocked`): at-least `≥n r.C` / ¬≤n in w': either a direct w->v
r-link with v carrying the operands, or w' has `>= n` matching r-successors; else
`blocked=false`.

Return `blocked` (18776).

## `hasOptimizedBlockingB2AutomateTransitionOperands` (~17694)

Recursive over AQAND operands; base AQALL: if `concept.role == r`, every operand
must be in L(v) (non-negated) else false.

## Subset/equal variants
- `isLabelConceptSubSet` (17462): every (concept,neg) of subSet in superSet; sets
  equalSet = (counts equal).
- `isLabelConceptEqualPairwiseBlocking` (18900): equal labels for w==w' AND
  v==v' (same ancestor role) — the textbook pairwise (what KM mode-4 currently is).

## Indirect blocking
On finding a blocker: mark w `PRFDIRECTBLOCKED`; `propagateIndirectSuccessorBlocking`
(19686) adds `PRFINDIRECTBLOCKED` to all deeper successors
(`propagateAddingBlockedProcessingRestrictionToSuccessors` 19785, only succAncDepth
> ancDepth, skip if already flagged). On blocker losing status,
`reactivateIndirectBlockedSuccessors` (19847) flags indirect successors for retest.

## Mapping to KM's Ext (clause world)

KM has NO explicit `∀r.C` concept objects — ∀ is a DL-clause
`C0(x) ∧ r(x,y) → D(y)`. So the Konclude reapply-queue "∀r.C in L(w')" becomes:
for the blocker w', the set of clauses of shape `C0 ∧ role(r) -> D` with `C0 ∈ L(w')`.
Then:
- **B1**: `concepts[w]` keys ⊆ `concepts[w']` keys (CLit = (c,neg); both polarities).
- **B2a**: for each role r on the w<->v edge (in_edges[w]/out_edges[w] touching
  pred v, both forward and inverse-bridge directions), for each ∀-clause
  `C0 ∧ r(x,y) -> D(y)` with C0 ∈ L(w'): require `D ∈ L(v)` (with correct polarity).
  If any missing -> not blocked.
- v = pred(w). "no inverse edges" (Konclude `!ancRoleHash`) ~ w has no role edge to
  v that participates in a ∀ over an inverse/own role; degenerate -> B1 suffices.
- Cardinality B3/B4/B5/B6: defer to a later increment (needs the ≥/≤ recognition;
  KM encodes those as Eq-head + distinctness clauses already).
- Indirect blocking: already added in commit 99a21d1 (mode-4 branch); reuse.

## Port plan (gated, synthetic-tested, ws build)
1. New blocking mode = optimized (B1 subset + B2a ∀-clause-operand on v) +
   indirect. Index ∀-clauses by body (C0, r) -> head D once at Ht::new.  [DONE a853e1e]
2. Synthetic tests: the same mode-4 cases must pass (esp. inverse_model SAT via
   B2a + indirect).  [DONE — mode5_* tests]
3. Auto-route: select mode 5 when the clause set has inverse bridging (Konclude
   default = optimized blocking). `has_inverse_bridge` + KM_HT_AUTOBLOCK gate.  [DONE]
4. Then B2b (transitive/automata), then cardinality B3-B6.  [see finding below]

## FINDING (2026-06-25): B2b is largely PRE-COMPILED in KM

Konclude needs B2b because it keeps `∀R.C` as runtime concepts with role-automata
transitions. **KM's frontend compiles transitivity into concept-propagation clauses
at PARSE time** (`preprocess.rs::transitivity_clauses`): for a transitive-R consumer
`Γ ∧ R(x,y) ∧ ⋀C_i(y) → Δ`, it introduces `P = __trans__R__{C_i}` with
`R(x,y)∧⋀C_i(y)→P(x)`, `R(x,y)∧P(y)→P(x)` (P propagates backward along R), and
`Γ∧P(x)→Δ`. So the transitive consequences become ORDINARY concepts in node labels.
B1 subset blocking already accounts for them (w's __trans__ concepts must be in w').
So Konclude's runtime B2b is substantially SUBSUMED by KM's parse-time compilation +
B1. NOT assumed — to be CONFIRMED on transitive ORE onts at validation time; if a gap
shows, port B2b then.

## Cardinality B3-B6: KM encoding differs

Konclude reads `≤n/≥n r.C` operators from labels and counts successors. KM has NO
such operators in labels: `≤n` is an Eq-head merge clause (apply_head), `≥n` is n
distinct ∃ successors + pairwise distinctness clauses (`⊥⟵Eq(yi,yj)`). So B3-B6 are
NOT a direct port — cardinality-under-blocking soundness rests on KM's merge +
distinctness + B1 subset interacting. Validate on the number/functional targets
(10908 number, 10621 F, 15672 N); port the specific safety check only if a gap shows.
