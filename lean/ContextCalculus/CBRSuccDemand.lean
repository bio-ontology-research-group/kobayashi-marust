import ContextCalculus.CBRSuccClosure
import ContextCalculus.CBSourceEqClosure

/-!
# Demand-driven r-Succ offers of individual labels

KM holds an offer of a label `B(o)` (an r-Succ payload `B(o) → B(o)` that
keeps the constant, `forwardPredicate_individual_label`) back until its target
needs it (`CBRSuccClosure.DemandView.deferred`).  The closures therefore owe
only the offers that are not deferred.  This module shows why a held-back
hypothesis is not missed.

A held-back hypothesis `B(o) → B(o)` at a target `T` could take part in:

* **Hyper** (KM grounds the central variable only in the nominal ground
  context, which never defers; elsewhere `x ↦ x`).  A body atom `B(v)` of an
  ontology clause instantiates to `B(o)` only for `v ≠ x`.  If `B` is read on
  a constant or on a variable that no central role atom binds, `B` is in
  `labelAlways` and never waits.  Otherwise the clause has a central role atom
  `r(x, v)` or `r(v, x)`, which instantiates to `r(x, o)` or `r(o, x)`; Hyper
  needs a provider for it, a retained clause of `T` with that literal in its
  head, and that literal registers the need
  (`central_hyper_read_registers`).
* **Eq**: KM rewrites a whole argument (`directRewrite`), so rewriting
  `B(o)` needs an equation whose rewritten side is `o`; an equation with `o` on
  either side registers every label of `o` (`eq_rewrite_read_registers`,
  `source_eq_rewrite_read_registers`).  An equation between a Skolem term `f(x)`
  and `o` is such an equation once it is in `T`, whichever way it came (Hyper,
  Eq, or a Pred conclusion of a successor).  Before that, `B(o)` and `B(f(x))`
  are different literals and no rule joins them.
* **A relay**: `T` would offer `B(o)` on to a successor `S`, which might read
  it.  A deferred offer has `T` outside the need closure, which is checked to be
  backward closed over the successor edges, so no successor of `T` is in it
  either (`deferred_successors_outside`), and none registers a reader
  (`deferred_successor_not_registers`).
* **Pred**: a successor `S` sends a conclusion back to `T` only for the body
  atoms on the edge's pushed set.  `B(o)` enters the pushed set of `T → S` only
  as an offer from `T`.  `T` makes that offer only for a `B(o)` it holds in a
  head, as a derived fact or a hypothesis it received.  By the relay case, `S`
  does not need `B(o)` while `T` is held back, so no Pred conclusion of `S`
  carries `B(o)` to `T`.  Resolving such a body atom at `T` would in any case
  need a provider of `B(o)` at `T` other than the held-back hypothesis.

Every step that could use the hypothesis therefore has a premise that
registers a need first.  KM then releases the offer, and saturation is
monotone, so the fixpoint is the one with every offer sent.
-/

namespace ContextCalculus.CBRSuccDemand

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBRSuccClosure
open ContextCalculus.CBFiniteTermOrderWire

/-! ## The need closure -/

theorem mem_needStep_of_mem (edges : List (Nat × Nat)) (current : List Nat)
    (node : Nat) (hnode : node ∈ current) : node ∈ needStep edges current := by
  unfold needStep
  exact List.mem_append_left _ hnode

theorem mem_needIterate_of_mem (edges : List (Nat × Nat)) :
    ∀ (fuel : Nat) (current : List Nat) (node : Nat), node ∈ current →
      node ∈ needIterate edges fuel current := by
  intro fuel
  induction fuel with
  | zero => intro current node hnode; simpa [needIterate] using hnode
  | succ fuel ih =>
      intro current node hnode
      simp only [needIterate]
      exact ih _ node (mem_needStep_of_mem edges current node hnode)

/-- A context that registers the need is in the need closure. -/
theorem mem_needClosure_of_registers (view : DemandView) (concept individual node : Nat)
    (hnode : node ∈ view.nodes)
    (hregisters : registersIn view.ontology (view.retained node) concept individual = true) :
    node ∈ view.needClosure concept individual := by
  unfold DemandView.needClosure
  apply mem_needIterate_of_mem
  simp only [List.mem_filter]
  exact ⟨hnode, hregisters⟩

/-- What a deferred offer guarantees: demand is on, the target is not the
nominal ground context, the target does not register the need, and the
target is outside a need closure that is backward closed over the edges. -/
theorem deferred_spec (view : DemandView) (labels : IndividualLabels)
    (target concept individual : Nat)
    (hdeferred : view.deferred labels target (.concept concept (.const individual)) = true) :
    labels.demand = true ∧ view.ground target = false ∧
      closedOver view.edges (view.needClosure concept individual) = true ∧
      target ∉ view.needClosure concept individual := by
  simp only [DemandView.deferred, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hdeferred
  obtain ⟨⟨⟨hdemand, hground⟩, hclosed⟩, hout⟩ := hdeferred
  exact ⟨hdemand, hground, hclosed, hout⟩

theorem deferred_not_registers (view : DemandView) (labels : IndividualLabels)
    (target concept individual : Nat)
    (hdeferred : view.deferred labels target (.concept concept (.const individual)) = true)
    (htarget : target ∈ view.nodes) :
    registersIn view.ontology (view.retained target) concept individual = false := by
  obtain ⟨_, _, _, hout⟩ := deferred_spec view labels target concept individual hdeferred
  cases hregisters : registersIn view.ontology (view.retained target) concept individual with
  | false => rfl
  | true =>
      exact absurd (mem_needClosure_of_registers view concept individual target htarget
        hregisters) hout

/-- No successor of a held-back target needs the label. -/
theorem deferred_successors_outside (view : DemandView) (labels : IndividualLabels)
    (target concept individual : Nat)
    (hdeferred : view.deferred labels target (.concept concept (.const individual)) = true) :
    ∀ edge ∈ view.edges, edge.1 = target →
      edge.2 ∉ view.needClosure concept individual := by
  obtain ⟨_, _, hclosed, hout⟩ := deferred_spec view labels target concept individual hdeferred
  intro edge hedge hsource hsuccessor
  have hback := List.all_eq_true.mp hclosed edge hedge
  simp only [decide_eq_true_eq] at hback
  exact hout (hsource ▸ hback hsuccessor)

theorem deferred_successor_not_registers (view : DemandView) (labels : IndividualLabels)
    (target concept individual : Nat)
    (hdeferred : view.deferred labels target (.concept concept (.const individual)) = true) :
    ∀ edge ∈ view.edges, edge.1 = target → edge.2 ∈ view.nodes →
      registersIn view.ontology (view.retained edge.2) concept individual = false := by
  intro edge hedge hsource hnode
  cases hregisters : registersIn view.ontology (view.retained edge.2) concept individual with
  | false => rfl
  | true =>
      exact absurd (mem_needClosure_of_registers view concept individual edge.2 hnode
        hregisters) (deferred_successors_outside view labels target concept individual
          hdeferred edge hedge hsource)

/-! ## Readers -/

theorem mem_labelAlways (ontology : List FCL) (source : FCL) (hsource : source ∈ ontology)
    (literal : FLit) (hliteral : literal ∈ source.body) (concept : Nat) (term : FTerm)
    (hread : labelRead literal = some (concept, term))
    (hunbound : ((anchorsOf source term).isEmpty || isConstTerm term) = true) :
    concept ∈ labelAlways ontology := by
  simp only [labelAlways, List.mem_flatMap, List.mem_filterMap]
  exact ⟨source, hsource, literal, hliteral, by simp [hread, hunbound]⟩

theorem mem_labelReaders (ontology : List FCL) (source : FCL) (hsource : source ∈ ontology)
    (literal : FLit) (hliteral : literal ∈ source.body) (concept : Nat) (term : FTerm)
    (hread : labelRead literal = some (concept, term))
    (anchor : Nat × Bool) (hanchor : anchor ∈ anchorsOf source term) :
    (anchor.1, anchor.2, concept) ∈ labelReaders ontology := by
  simp only [labelReaders, List.mem_flatMap]
  refine ⟨source, hsource, literal, hliteral, ?_⟩
  simp only [hread, List.mem_map]
  exact ⟨anchor, hanchor, rfl⟩

theorem registersIn_of_head (ontology retained : List FCL) (concept individual : Nat)
    (provider : FCL) (hprovider : provider ∈ retained) (literal : FLit)
    (hhead : literal ∈ provider.head)
    (hliteral : literalRegisters (labelReaders ontology) concept individual literal = true) :
    registersIn ontology retained concept individual = true := by
  unfold registersIn
  simp only [Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨provider, hprovider, Or.inr ⟨literal, hhead, hliteral⟩⟩

theorem registersIn_of_always (ontology retained : List FCL) (concept individual : Nat)
    (halways : concept ∈ labelAlways ontology) :
    registersIn ontology retained concept individual = true := by
  unfold registersIn
  simp [halways]

/-- An anchor of `v` is a body role atom `r(x, v)` (forward) or `r(v, x)`. -/
theorem anchor_atom (source : FCL) (term : FTerm) (anchor : Nat × Bool)
    (hanchor : anchor ∈ anchorsOf source term) :
    (anchor.2 = true ∧ FLit.P (.role anchor.1 (.var 0) term) ∈ source.body) ∨
      (anchor.2 = false ∧ FLit.P (.role anchor.1 term (.var 0)) ∈ source.body) := by
  simp only [anchorsOf, List.mem_filterMap] at hanchor
  obtain ⟨atom, hatom, hsome⟩ := hanchor
  obtain ⟨role, roleSource, roleTarget⟩ := atom
  simp only [bodyRoleAtoms, List.mem_filterMap] at hatom
  obtain ⟨literal, hliteral, hmatch⟩ := hatom
  have hlit : literal = .P (.role role roleSource roleTarget) := by
    cases literal with
    | P predicate =>
        cases predicate with
        | concept _ _ => simp at hmatch
        | role r s t => simp at hmatch; obtain ⟨rfl, rfl, rfl⟩ := hmatch; rfl
    | eq _ _ => simp at hmatch
    | ineq _ _ => simp at hmatch
  subst hlit
  by_cases hforward : roleSource = .var 0 ∧ roleTarget = term
  · simp only [hforward, and_self, if_true, Option.some.injEq] at hsome
    obtain ⟨rfl, rfl⟩ := hforward
    subst hsome
    exact Or.inl ⟨rfl, hliteral⟩
  · simp only [hforward, if_false] at hsome
    by_cases hbackward : roleSource = term ∧ roleTarget = .var 0
    · simp only [hbackward, and_self, if_true, Option.some.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hbackward
      subst hsome
      exact Or.inr ⟨rfl, hliteral⟩
    · simp [hbackward] at hsome

theorem substL_concept_const (σ : List (Int × FTerm)) (literal : FLit)
    (concept individual : Nat)
    (hsubst : substL σ literal = .P (.concept concept (.const individual))) :
    ∃ term, literal = .P (.concept concept term) ∧ substT σ term = .const individual := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept c t =>
          simp only [substL, FLit.P.injEq, FPred.concept.injEq] at hsubst
          obtain ⟨rfl, ht⟩ := hsubst
          exact ⟨t, rfl, ht⟩
      | role _ _ _ => simp [substL] at hsubst
  | eq _ _ => simp [substL] at hsubst
  | ineq _ _ => simp [substL] at hsubst

/-- **(a), (b): Hyper.**  A central Hyper step (`x ↦ x`) that reads the label
`B(o)` of an individual, i.e. whose instantiated body has `B(o)` and a provider
for every body literal among the target's retained clauses, makes the target
register the need for `(B, o)`. -/
theorem central_hyper_read_registers (ontology retained : List FCL) (source : FCL)
    (hsource : source ∈ ontology) (σ : List (Int × FTerm))
    (hcentral : substT σ (.var 0) = .var 0) (concept individual : Nat)
    (hread : FLit.P (.concept concept (.const individual)) ∈ (substCl σ source).body)
    (hprovided : ∀ literal ∈ (substCl σ source).body,
      ∃ provider ∈ retained, literal ∈ provider.head) :
    registersIn ontology retained concept individual = true := by
  simp only [substCl, List.mem_map] at hread
  obtain ⟨literal, hliteral, hsubst⟩ := hread
  obtain ⟨term, rfl, hterm⟩ := substL_concept_const σ literal concept individual hsubst
  have hnotCentral : term ≠ .var 0 := by
    intro h
    subst h
    rw [hcentral] at hterm
    cases hterm
  have hlabel : labelRead (.P (.concept concept term)) = some (concept, term) := by
    simp [labelRead, hnotCentral]
  cases hunbound : ((anchorsOf source term).isEmpty || isConstTerm term) with
  | true =>
      exact registersIn_of_always ontology retained concept individual
        (mem_labelAlways ontology source hsource _ hliteral concept term hlabel hunbound)
  | false =>
      simp only [Bool.or_eq_false_iff] at hunbound
      obtain ⟨hnonempty, _⟩ := hunbound
      obtain ⟨anchor, hanchor⟩ : ∃ anchor, anchor ∈ anchorsOf source term := by
        cases h : anchorsOf source term with
        | nil => simp [h] at hnonempty
        | cons head _ => exact ⟨head, by simp⟩
      have hreader := mem_labelReaders ontology source hsource _ hliteral concept term hlabel
        anchor hanchor
      rcases anchor_atom source term anchor hanchor with ⟨hdir, hatom⟩ | ⟨hdir, hatom⟩
      · have hinst : FLit.P (.role anchor.1 (.var 0) (.const individual)) ∈
            (substCl σ source).body := by
          simp only [substCl, List.mem_map]
          exact ⟨_, hatom, by simp [substL, hcentral, hterm]⟩
        obtain ⟨provider, hprovider, hhead⟩ := hprovided _ hinst
        refine registersIn_of_head ontology retained concept individual provider hprovider _
          hhead ?_
        rw [hdir] at hreader
        simp [literalRegisters, hreader]
      · have hinst : FLit.P (.role anchor.1 (.const individual) (.var 0)) ∈
            (substCl σ source).body := by
          simp only [substCl, List.mem_map]
          exact ⟨_, hatom, by simp [substL, hcentral, hterm]⟩
        obtain ⟨provider, hprovider, hhead⟩ := hprovided _ hinst
        refine registersIn_of_head ontology retained concept individual provider hprovider _
          hhead ?_
        rw [hdir] at hreader
        simp [literalRegisters, hreader]

/-- **(c): Eq.**  Rewriting the label `B(o)` with an equation of a retained
clause makes the target register every label of `o`: the rewrite replaces a
whole argument, so the equation's left side is `o`. -/
theorem eq_rewrite_read_registers (ontology retained : List FCL)
    (order : DecodedFiniteTermOrderDocument) (equality : FCL) (hequality : equality ∈ retained)
    (left right : FTerm) (hhead : FLit.eq left right ∈ equality.head)
    (concept individual : Nat) (rewritten : FLit)
    (hrewrite : CBLocalEqEnumeration.directRewrite order left right
      (.P (.concept concept (.const individual))) = some rewritten) :
    registersIn ontology retained concept individual = true := by
  have hleft : left = .const individual := by
    by_contra hne
    simp [CBLocalEqEnumeration.directRewrite, Ne.symm hne] at hrewrite
  subst hleft
  exact registersIn_of_head ontology retained concept individual equality hequality _ hhead
    (by simp [literalRegisters])

theorem source_eq_rewrite_read_registers (ontology retained : List FCL)
    {production : CBProductionTraceWire.DecodedProductionRun}
    (order : CBSourceHyperClosure.DecodedSourceFiniteOrder production)
    (equality : FCL) (hequality : equality ∈ retained)
    (left right : FTerm) (hhead : FLit.eq left right ∈ equality.head)
    (concept individual : Nat) (rewritten : FLit)
    (hrewrite : CBSourceEqClosure.directRewrite order left right
      (.P (.concept concept (.const individual))) = some rewritten) :
    registersIn ontology retained concept individual = true := by
  have hleft : left = .const individual := by
    by_contra hne
    simp [CBSourceEqClosure.directRewrite, Ne.symm hne] at hrewrite
  subst hleft
  exact registersIn_of_head ontology retained concept individual equality hequality _ hhead
    (by simp [literalRegisters])

/-- **Held back means unused.**  At a deferred target, no central Hyper step
over its retained clauses reads the label, and no equation of its retained
clauses rewrites it. -/
theorem deferred_label_unread (view : DemandView) (labels : IndividualLabels)
    (target concept individual : Nat)
    (hdeferred : view.deferred labels target (.concept concept (.const individual)) = true)
    (htarget : target ∈ view.nodes) :
    (∀ source ∈ view.ontology, ∀ σ : List (Int × FTerm), substT σ (.var 0) = .var 0 →
      FLit.P (.concept concept (.const individual)) ∈ (substCl σ source).body →
        ¬ ∀ literal ∈ (substCl σ source).body,
          ∃ provider ∈ view.retained target, literal ∈ provider.head) ∧
    (∀ order : DecodedFiniteTermOrderDocument, ∀ equality ∈ view.retained target,
      ∀ left right, FLit.eq left right ∈ equality.head →
        CBLocalEqEnumeration.directRewrite order left right
          (.P (.concept concept (.const individual))) = none) := by
  have hnot := deferred_not_registers view labels target concept individual hdeferred htarget
  constructor
  · intro source hsource σ hcentral hread hprovided
    have := central_hyper_read_registers view.ontology (view.retained target) source hsource σ
      hcentral concept individual hread hprovided
    rw [hnot] at this
    cases this
  · intro order equality hequality left right hhead
    cases hrewrite : CBLocalEqEnumeration.directRewrite order left right
        (.P (.concept concept (.const individual))) with
    | none => rfl
    | some rewritten =>
        have := eq_rewrite_read_registers view.ontology (view.retained target) order equality
          hequality left right hhead concept individual rewritten hrewrite
        rw [hnot] at this
        cases this

#print axioms deferred_spec
#print axioms deferred_not_registers
#print axioms deferred_successors_outside
#print axioms deferred_successor_not_registers
#print axioms central_hyper_read_registers
#print axioms eq_rewrite_read_registers
#print axioms source_eq_rewrite_read_registers
#print axioms deferred_label_unread

end ContextCalculus.CBRSuccDemand
