import ContextCalculus.CBSuccClosureWire

/-!
# Finite production r-Succ closure

This module reconstructs KM's complete r-Succ cross-product from two checked
inputs: the reach-concept signature and the terminal predecessor snapshots.
The latter are the reverse representation of every live successor edge.  The
semi-naive watermarks are an implementation detail; the terminal obligation is
the same finite `outgoing edges × central reach facts` product.
-/

namespace ContextCalculus.CBRSuccClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBPredSendCoverageWire
open ContextCalculus.CBJoin3ClosureWire
open ContextCalculus.CBSuccClosure
open ContextCalculus.CBSuccClosureWire
open ContextCalculus.CBFiniteLiteralOrderWire

structure OutgoingEdge where
  label : FTerm
  targetIndex : Nat
deriving DecidableEq, Repr

/-- Reverse the exact predecessor snapshots into the outgoing successor edges
of one production context. -/
def outgoingEdges (coverage : DecodedPredSendCoverageDocument)
    (sourceIndex : Nat) : List OutgoingEdge :=
  let ordinary := coverage.senders.flatMap fun target =>
    target.edges.filterMap fun edge =>
      if edge.receiverIndex.val = sourceIndex then
        some { label := edge.label, targetIndex := target.senderIndex.val }
      else none
  let root := coverage.rootSender.toList.flatMap fun target =>
    target.edges.filterMap fun edge =>
      if edge.receiverIndex.val = sourceIndex then
        some {
          label := .const edge.individual
          targetIndex := target.senderIndex.val
        }
      else none
  (ordinary ++ root).eraseDups

def isCentralReach (reachConcepts : List Nat) : FPred → Bool
  | .concept concept (.var 0) => decide (concept ∈ reachConcepts)
  | _ => false

/-- The labels of individuals that r-Succ offers.  `concepts` is KM's
`Sig::grounded_label`.  With `everyEdge` off, a label `B(o)` goes over the
grounded successor edge `f(o)` of that individual only; the nominal ground
context holds the labels of an individual on its constant, and the successor
`f(o)` reads them as labels of its predecessor `y`.  With `everyEdge` on, a
label `B(o)` goes over every successor edge, as in the r-Succ rule of
arXiv:1805.01396 (`Su^r` contains `B(o)`): a context that derived `B(o)` under
its own hypotheses hands it to its successors, which read it on the constant
`o` (`forwardPredicate_individual_label`). -/
structure IndividualLabels where
  concepts : List Nat := []
  everyEdge : Bool := false
  /-- KM_RSUCC_DEMAND: a label `B(o)` is owed to a target only when the target
  needs it (`DemandView.deferred`). -/
  demand : Bool := false
deriving DecidableEq, Repr

/-! ## Demand-driven individual labels

KM (`KM_RSUCC_DEMAND`, on by default) holds an offer of a label `B(o)` back
until its target needs it.  A context needs `(B, o)` when one of its clauses,
in body or head, has

* a role literal `r(x, o)` where an ontology clause joins `r(x, y)` to a body
  atom `B(y)` (`(r, true, B) ∈ labelReaders`), or `r(o, x)` where one joins
  `r(y, x)` to `B(y)` (`(r, false, B)`);
* an equation with `o` on either side (every label of `o`); or
* `B ∈ labelAlways`: some ontology clause reads `B` on a constant or on a
  variable that no central role atom binds;

or when one of its successors needs `(B, o)`.  The nominal ground context
always receives its offers.  `CBRSuccDemand` proves that a held-back
hypothesis takes no part in a central Hyper step, an Eq step or a relay. -/

/-- The role atoms of a source clause's body. -/
def bodyRoleAtoms (clause : FCL) : List (Nat × FTerm × FTerm) :=
  clause.body.filterMap fun literal =>
    match literal with
    | .P (.role role source target) => some (role, source, target)
    | _ => none

/-- The central role atoms of `clause` that bind the variable `v`:
`(r, true)` for `r(x, v)`, `(r, false)` for `r(v, x)`. -/
def anchorsOf (clause : FCL) (v : FTerm) : List (Nat × Bool) :=
  (bodyRoleAtoms clause).filterMap fun atom =>
    if atom.2.1 = .var 0 ∧ atom.2.2 = v then some (atom.1, true)
    else if atom.2.1 = v ∧ atom.2.2 = .var 0 then some (atom.1, false)
    else none

/-- A body literal that reads a label away from the centre. -/
def labelRead : FLit → Option (Nat × FTerm)
  | .P (.concept concept term) => if term = .var 0 then none else some (concept, term)
  | _ => none

def isConstTerm : FTerm → Bool
  | .const _ => true
  | _ => false

/-- KM's `Sig::label_readers`: `(r, forward, B)` for each central role atom
that binds the argument of a body atom `B(v)`. -/
def labelReaders (ontology : List FCL) : List (Nat × Bool × Nat) :=
  ontology.flatMap fun clause => clause.body.flatMap fun literal =>
    match labelRead literal with
    | some (concept, term) => (anchorsOf clause term).map fun anchor => (anchor.1, anchor.2, concept)
    | none => []

/-- KM's `Sig::label_always`: concepts read on a constant or on a variable
that no central role atom binds. -/
def labelAlways (ontology : List FCL) : List Nat :=
  ontology.flatMap fun clause => clause.body.filterMap fun literal =>
    match labelRead literal with
    | some (concept, term) =>
        if (anchorsOf clause term).isEmpty || isConstTerm term then some concept else none
    | none => none

/-- A literal through which a context reads the label `B(o)`. -/
def literalRegisters (readers : List (Nat × Bool × Nat)) (concept individual : Nat) :
    FLit → Bool
  | .P (.role role (.var 0) (.const o)) =>
      decide (o = individual) && decide ((role, true, concept) ∈ readers)
  | .P (.role role (.const o) (.var 0)) =>
      decide (o = individual) && decide ((role, false, concept) ∈ readers)
  | .eq left right => decide (left = .const individual) || decide (right = .const individual)
  | _ => false

def registersIn (ontology : List FCL) (retained : List FCL) (concept individual : Nat) : Bool :=
  decide (concept ∈ labelAlways ontology) ||
    retained.any fun clause =>
      clause.body.any (literalRegisters (labelReaders ontology) concept individual) ||
        clause.head.any (literalRegisters (labelReaders ontology) concept individual)

/-- The successor graph and terminal clauses the demand is read from. -/
structure DemandView where
  ontology : List FCL
  nodes : List Nat
  edges : List (Nat × Nat)
  retained : Nat → List FCL
  ground : Nat → Bool

/-- One backward step: a context whose successor needs the label needs it. -/
def needStep (edges : List (Nat × Nat)) (current : List Nat) : List Nat :=
  current ++ edges.filterMap fun edge =>
    if edge.2 ∈ current ∧ edge.1 ∉ current then some edge.1 else none

def needIterate (edges : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, current => current
  | fuel + 1, current => needIterate edges fuel (needStep edges current)

def DemandView.needClosure (view : DemandView) (concept individual : Nat) : List Nat :=
  needIterate view.edges (view.edges.length + 1)
    (view.nodes.filter fun node => registersIn view.ontology (view.retained node) concept individual)

/-- The closure is backward closed over the edges (checked, not assumed). -/
def closedOver (edges : List (Nat × Nat)) (current : List Nat) : Bool :=
  edges.all fun edge => decide (edge.2 ∈ current → edge.1 ∈ current)

/-- Whether KM may hold back the offer `pushed` to `target`.  Only a label of
an individual can wait, never at the nominal ground context, and only when the
need closure is a fixpoint that leaves `target` out. -/
def DemandView.deferred (view : DemandView) (labels : IndividualLabels) (target : Nat) :
    FPred → Bool
  | .concept concept (.const individual) =>
      labels.demand && !view.ground target &&
        closedOver view.edges (view.needClosure concept individual) &&
          decide (target ∉ view.needClosure concept individual)
  | _ => false

/-- Whether the edge labelled `edge` carries the label `B(o)` of an
individual (KM's `rsucc_offered_over`).  Root edges (labelled by a constant)
carry central reach facts only. -/
def isGroundedLabel (labels : IndividualLabels) (edge : FTerm) : FPred → Bool
  | .concept concept (.const individual) =>
      match edge with
      | .app _ (.const parent) =>
          decide (concept ∈ labels.concepts) && (labels.everyEdge || decide (parent = individual))
      | .app _ _ => decide (concept ∈ labels.concepts) && labels.everyEdge
      | _ => false
  | _ => false

/-- Whether the edge labelled `edge` carries the reach fact `predicate`. -/
def offeredOver (reachConcepts : List Nat) (groundedConcepts : IndividualLabels) (edge : FTerm)
    (predicate : FPred) : Bool :=
  isCentralReach reachConcepts predicate || isGroundedLabel groundedConcepts edge predicate

/-- Ordered-unique maximal central reach facts, matching `rsucc_reach_tail`
folded over the append-only terminal pool. -/
def reachPredicates (reachConcepts : List Nat)
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL) : List FPred :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices clause.head).filterMap fun headIndex =>
        match (clause.head[headIndex]? : Option FLit) with
        | some (FLit.P predicate) =>
            if isCentralReach reachConcepts predicate then some predicate else none
        | _ => none).eraseDups

/-- Ordered-unique maximal reach facts that the edge labelled `edge`
carries: the central reach facts (`reachPredicates`) on every edge, and on a
grounded edge `f(o)` also the labels of `o`.  KM folds both kinds over one
append-only pool and filters them per edge. -/
def edgeReachPredicates (reachConcepts : List Nat) (groundedConcepts : IndividualLabels)
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL)
    (edge : FTerm) : List FPred :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices clause.head).filterMap fun headIndex =>
        match (clause.head[headIndex]? : Option FLit) with
        | some (FLit.P predicate) =>
            if offeredOver reachConcepts groundedConcepts edge predicate then some predicate
            else none
        | _ => none).eraseDups

structure RSuccOffer where
  edge : OutgoingEdge
  sourcePredicate : FPred
  pushed : FPred
deriving DecidableEq, Repr

/-- The parent of an edge label, i.e. the term that `forwardTerm` maps to
the predecessor variable `y`: `x` for an ordinary `f(x)` edge, `o` for a
grounded `f(o)` edge, and `x` for a root edge labelled by the individual `o`
(the source context's element is the ground context's predecessor; KM's
`forwards(o, ·)` maps `x ↦ y`, docs/NOMINALS-CB.md section 12). -/
def parentOfEdge : FTerm → FTerm
  | .app _ parent => parent
  | .const _ => .var 0
  | term => term

/-- A root-edge offer of the central label `B(x)` pushes `B(y)`. -/
theorem forwardPredicate_root_label (individual concept : Nat) :
    forwardPredicate (.const individual) (parentOfEdge (.const individual))
        (.concept concept (.var 0)) =
      .concept concept (.var (-1)) := by
  simp [parentOfEdge, forwardPredicate, forwardTerm]

/-- A grounded-edge offer of the label `B(o)` pushes `B(y)`. -/
theorem forwardPredicate_grounded_label (function individual concept : Nat) :
    forwardPredicate (.app function (.const individual))
        (parentOfEdge (.app function (.const individual)))
        (.concept concept (.const individual)) =
      .concept concept (.var (-1)) := by
  simp [parentOfEdge, forwardPredicate, forwardTerm]

/-- Over an ordinary successor edge `f(t)` whose parent `t` is not the
individual `o`, an offer of the label `B(o)` keeps the constant: the
successor receives the hypothesis `B(o)`. -/
theorem forwardPredicate_individual_label (function individual concept : Nat)
    (parent : FTerm) (hparent : parent ≠ .const individual) :
    forwardPredicate (.app function parent) (parentOfEdge (.app function parent))
        (.concept concept (.const individual)) =
      .concept concept (.const individual) := by
  have h : (FTerm.const individual = parent) = False := by
    apply propext; constructor
    · intro e; exact hparent e.symm
    · intro e; exact e.elim
  simp [parentOfEdge, forwardPredicate, forwardTerm, h]

/-- The nominal ground context of `production` holds the unconditional
fact `→ p`. -/
def groundUnitLabel (production : DecodedProductionRun) (p : FPred) : Bool :=
  production.contexts.any fun context =>
    context.nominalGround &&
      context.retained.any fun clause => decide (clause.body = [] ∧ clause.head = [.P p])

/-- With `everyEdge`, a label `B(o)` that the ground context holds as an
unconditional fact goes over the grounded edges `f(o)` only: its readers
get it through the root edges into the ground context as with the offers
off (KM's `rsucc_reach_unit`).  The exclusion only drops offers, and every
offer is a tautological hypothesis, so it does not affect soundness. -/
def skipsGroundUnit (labels : IndividualLabels) (production : DecodedProductionRun)
    (edge : FTerm) : FPred → Bool
  | p@(.concept _ (.const individual)) =>
      labels.everyEdge &&
        (match edge with
          | .app _ (.const parent) => decide (parent ≠ individual)
          | _ => true) &&
        groundUnitLabel production p
  | _ => false

/-- The demand view of a checked production: its contexts, the successor
edges reversed from the predecessor snapshots, and the retained clauses. -/
def productionDemandView (coverage : DecodedPredSendCoverageDocument) : DemandView :=
  let production := coverage.interContext.base.production
  let nodes := List.range production.contexts.length
  { ontology := production.source.ontology
    nodes
    edges := nodes.flatMap fun source =>
      (outgoingEdges coverage source).map fun edge => (source, edge.targetIndex)
    retained := fun index => (production.contexts[index]?.map (·.retained)).getD []
    ground := fun index => (production.contexts[index]?.map (·.nominalGround)).getD false }

def rSuccOffers (coverage : DecodedPredSendCoverageDocument)
    (reachConcepts : List Nat) (groundedConcepts : IndividualLabels) (order : DecodedFiniteLiteralOrderDocument)
    (sourceIndex : Nat) (retained : List FCL) : List RSuccOffer :=
  (outgoingEdges coverage sourceIndex).flatMap fun edge =>
    ((edgeReachPredicates reachConcepts groundedConcepts order retained edge.label).filter
      fun predicate => !skipsGroundUnit groundedConcepts coverage.interContext.base.production
        edge.label predicate &&
        !(productionDemandView coverage).deferred groundedConcepts edge.targetIndex
          (forwardPredicate edge.label (parentOfEdge edge.label) predicate)).map
      fun predicate => {
      edge
      sourcePredicate := predicate
      pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
    }

theorem mem_rSuccOffers_iff {coverage : DecodedPredSendCoverageDocument}
    {reachConcepts : List Nat} {groundedConcepts : IndividualLabels} {order : DecodedFiniteLiteralOrderDocument}
    {sourceIndex : Nat} {retained : List FCL} {offer : RSuccOffer} :
    offer ∈ rSuccOffers coverage reachConcepts groundedConcepts order sourceIndex retained ↔
      ∃ edge ∈ outgoingEdges coverage sourceIndex,
        ∃ predicate ∈ edgeReachPredicates reachConcepts groundedConcepts order retained
            edge.label,
          skipsGroundUnit groundedConcepts coverage.interContext.base.production
              edge.label predicate = false ∧
          (productionDemandView coverage).deferred groundedConcepts edge.targetIndex
              (forwardPredicate edge.label (parentOfEdge edge.label) predicate) = false ∧
          offer = {
            edge := edge
            sourcePredicate := predicate
            pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
          } := by
  simp only [rSuccOffers, List.mem_flatMap, List.mem_map, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨edge, hedge, predicate, ⟨hpred, hskip, hdefer⟩, rfl⟩
    exact ⟨edge, hedge, predicate, hpred, hskip, hdefer, rfl⟩
  · rintro ⟨edge, hedge, predicate, hpred, hskip, hdefer, rfl⟩
    exact ⟨edge, hedge, predicate, ⟨hpred, hskip, hdefer⟩, rfl⟩

/-- Every r-Succ payload is again a tautological hypothesis at its target. -/
theorem rSuccOffer_valid {D : Type} (model : TModel D) (offer : RSuccOffer) :
    valid model (ContextCalculus.CBInterContext.succHypothesis offer.pushed) :=
  ContextCalculus.CBInterContext.succHypothesis_valid model offer.pushed

#print axioms mem_rSuccOffers_iff
#print axioms rSuccOffer_valid
#print axioms forwardPredicate_root_label
#print axioms forwardPredicate_grounded_label
#print axioms forwardPredicate_individual_label

end ContextCalculus.CBRSuccClosure
