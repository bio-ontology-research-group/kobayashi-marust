import ContextCalculus.CBProductionTrace
import ContextCalculus.CBSourceWire
import Lean

/-!
# Bounds-checked production CB context traces

One document binds every retained context clause to the exact typed normalized
source ontology and the context's complete core.  Context ids and core
predicates are duplicate-free, all symbols are bounds-checked, the retained
list is exactly the checked trace terminal, and every trace step is verified.

This checker establishes local production-step soundness.  A later terminal
wire must additionally check discarded-clause redundancy, all pending queues,
inter-context messages, closure, and fairness.
-/

namespace ContextCalculus.CBProductionTraceWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBSourceWire
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBRoleChainEncoding

inductive WireProductionJustification where
  | premise (index : Nat) (substitution : List WireSubstitutionEntry)
  | assumption (index : Nat)
  | tautology
  | resolve (positive negative : Nat) (literal : WireLiteral)
  | paramodulate (equality other : Nat) (left right : WireTerm)
      (literal : WireLiteral)
  | factor (source : Nat) (common first second : WireTerm)
  | deleteReflexiveInequality (source : Nat) (term : WireTerm)
  | join3 (consumer provider bridge : Nat) (ground general : WireLiteral)
      (term : WireTerm)
deriving FromJson, ToJson

structure WireProductionEntry where
  clause : WireClause
  justification : WireProductionJustification
deriving FromJson, ToJson

structure WireDiscardedClause where
  clause : WireClause
  strengthening_retained : Nat
deriving FromJson, ToJson

structure WireProductionContext where
  context_id : Nat
  root : Bool
  query_concept : Option Nat
  core : List WirePredicate
  retained : List WireClause
  discarded : List WireDiscardedClause
  trace : List WireProductionEntry
deriving FromJson, ToJson

structure WireProductionRun where
  version : Nat
  source : WireSourceBinding
  contexts : List WireProductionContext
deriving FromJson, ToJson

def WireProductionJustification.decode (bounds : Bounds) :
    WireProductionJustification → Except String Justification
  | .premise index substitution => do
      let variableIds := substitution.map WireSubstitutionEntry.variableId
      if variableIds.Nodup then
        return .premise index
          (← substitution.mapM (WireSubstitutionEntry.decode bounds))
      else throw "production substitution contains a duplicate variable"
  | .assumption index => return .assumption index
  | .tautology => return .tautology
  | .resolve positive negative literal =>
      return .resolve positive negative (← literal.decode bounds)
  | .paramodulate equality other left right literal =>
      return .paramodulate equality other (← left.decode bounds)
        (← right.decode bounds) (← literal.decode bounds)
  | .factor source common first second =>
      return .factor source (← common.decode bounds) (← first.decode bounds)
        (← second.decode bounds)
  | .deleteReflexiveInequality source term =>
      return .deleteReflexiveInequality source (← term.decode bounds)
  | .join3 consumer provider bridge ground general term =>
      return .join3 consumer provider bridge (← ground.decode bounds)
        (← general.decode bounds) (← term.decode bounds)

def WireProductionEntry.decode (bounds : Bounds)
    (wire : WireProductionEntry) : Except String Entry :=
  return (← wire.clause.decode bounds,
    ← wire.justification.decode bounds)

private def assumptionClause (predicate : FPred) : FCL :=
  ⟨[], [.P predicate]⟩

structure DecodedDiscardedClause (retained : List FCL) where
  clause : FCL
  strengtheningIndex : Fin retained.length
  strengthens : Strengthens (retained.get strengtheningIndex) clause

def WireDiscardedClause.decode (bounds : Bounds) (retained : List FCL)
    (wire : WireDiscardedClause) :
    Except String (DecodedDiscardedClause retained) := do
  let clause ← wire.clause.decode bounds
  if hindex : wire.strengthening_retained < retained.length then
    let index : Fin retained.length := ⟨wire.strengthening_retained, hindex⟩
    if hstrengthens : Strengthens (retained.get index) clause then
      return DecodedDiscardedClause.mk clause index hstrengthens
    else throw "retained clause does not strengthen the claimed discarded clause"
  else throw "discarded-clause strengthening index is outside the retained list"

structure DecodedProductionContext (bounds : Bounds) (ontology : List FCL) where
  contextId : Nat
  root : Bool
  queryConcept : Option Nat
  core : List FPred
  core_nodup : core.Nodup
  assumptions : List FCL
  assumptions_eq : assumptions = core.map assumptionClause
  retained : List FCL
  discarded : List (DecodedDiscardedClause retained)
  trace : List Entry
  retained_eq : retained = terminal trace
  trace_valid : check ontology assumptions trace = true

def WireProductionContext.decode (bounds : Bounds) (ontology : List FCL)
    (wire : WireProductionContext) :
    Except String (DecodedProductionContext bounds ontology) := do
  let queryConcept ← match wire.query_concept with
    | none => pure none
    | some query => some <$> checkId "production query concept" bounds.concepts query
  if _hcoreNodup : wire.core.Nodup then
    let core ← wire.core.mapM (WirePredicate.decode bounds)
    if hdecodedCoreNodup : core.Nodup then
      let assumptions := core.map assumptionClause
      let retained ← wire.retained.mapM (WireClause.decode bounds)
      let discarded ← wire.discarded.mapM (WireDiscardedClause.decode bounds retained)
      let trace ← wire.trace.mapM (WireProductionEntry.decode bounds)
      if hretained : retained = terminal trace then
        if htrace : check ontology assumptions trace = true then
          return {
            contextId := wire.context_id
            root := wire.root
            queryConcept
            core
            core_nodup := hdecodedCoreNodup
            assumptions
            assumptions_eq := rfl
            retained
            discarded
            trace
            retained_eq := hretained
            trace_valid := htrace
          }
        else throw "production context trace was rejected"
      else throw "production retained clauses differ from the checked trace terminal"
    else throw "decoded production context core contains duplicates"
  else throw "production context core contains duplicate predicates"

def CoreHolds {D : Type} (model : TModel D) (assignment : Int → D)
    (core : List FPred) : Prop :=
  ∀ predicate ∈ core, model.evalL assignment (.P predicate)

theorem DecodedProductionContext.retained_sound
    (decoded : DecodedProductionContext bounds ontology)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hcore : CoreHolds model assignment decoded.core) :
    ∀ clause ∈ decoded.retained, HoldsAt model assignment clause := by
  rw [decoded.retained_eq]
  apply CBProductionTrace.check_sound model assignment
    (assumptions := decoded.assumptions) (trace := decoded.trace) hontology
  · intro assumption hassumption
    rw [decoded.assumptions_eq] at hassumption
    simp only [List.mem_map] at hassumption
    obtain ⟨predicate, hpredicate, rfl⟩ := hassumption
    intro _
    exact ⟨.P predicate, List.mem_singleton.mpr rfl,
      hcore predicate hpredicate⟩
  · exact decoded.trace_valid

theorem DecodedProductionContext.discarded_sound
    (decoded : DecodedProductionContext bounds ontology)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hcore : CoreHolds model assignment decoded.core) :
    ∀ discarded ∈ decoded.discarded,
      HoldsAt model assignment discarded.clause := by
  intro discarded _
  apply HoldsAt.of_strengthens model assignment discarded.strengthens
  exact decoded.retained_sound model assignment hontology hcore
    (decoded.retained.get discarded.strengtheningIndex)
    (List.get_mem decoded.retained discarded.strengtheningIndex)

structure DecodedProductionRun where
  source : DecodedSourceBinding
  contexts : List (DecodedProductionContext source.bounds source.ontology)
  context_ids_nodup : (contexts.map (·.contextId)).Nodup

def WireProductionRun.decode (wire : WireProductionRun) :
    Except String DecodedProductionRun := do
  if wire.version != 1 then
    throw s!"unsupported CB production-trace version {wire.version}"
  if wire.contexts.isEmpty then
    throw "CB production trace must contain at least one context"
  if _hwireIds : (wire.contexts.map (·.context_id)).Nodup then
    let source ← wire.source.decode
    let contexts ← wire.contexts.mapM
      (WireProductionContext.decode source.bounds source.ontology)
    if hids : (contexts.map (·.contextId)).Nodup then
      return { source, contexts, context_ids_nodup := hids }
    else throw "decoded CB production context ids contain duplicates"
  else throw "CB production context ids contain duplicates"

def WireProductionRun.check (wire : WireProductionRun) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireProductionRun.check_sound (wire : WireProductionRun)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedProductionRun,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.contexts,
        ∀ (D : Type) (model : TModel D) (assignment : Int → D),
          (∀ source ∈ decoded.source.ontology, valid model source) →
          CoreHolds model assignment context.core →
          (∀ clause ∈ context.retained, HoldsAt model assignment clause) ∧
          (∀ discarded ∈ context.discarded,
            HoldsAt model assignment discarded.clause) := by
  cases hdecode : wire.decode with
  | error message => simp [WireProductionRun.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro context hcontext D model assignment hontology hcore
      exact ⟨context.retained_sound model assignment hontology hcore,
        context.discarded_sound model assignment hontology hcore⟩

/-- The same production-step theorem at the typed source semantics.  The model
used for trace evaluation is exactly the verified Skolem extension of a model
of the normalized source, so this statement does not trust the raw clause list
as an independent premise. -/
theorem WireProductionRun.check_source_sound (wire : WireProductionRun)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedProductionRun,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.contexts,
        ∀ (D : Type)
          (interpretation : Eqv.Interp D
            (Fin decoded.source.bounds.concepts)
            (Fin decoded.source.bounds.roles)
            (Fin decoded.source.bounds.individuals))
          (hmodels : CBRoleChainEncoding.models interpretation
            decoded.source.source) (default : D) (assignment : Int → D),
          CoreHolds
            (CBRoleChainEncoding.extendModel decoded.source.source
              interpretation hmodels default) assignment context.core →
          (∀ clause ∈ context.retained,
              HoldsAt
                (CBRoleChainEncoding.extendModel decoded.source.source
                  interpretation hmodels default) assignment clause) ∧
          (∀ discarded ∈ context.discarded,
              HoldsAt
                (CBRoleChainEncoding.extendModel decoded.source.source
                  interpretation hmodels default) assignment
                discarded.clause) := by
  rcases wire.check_sound hcheck with ⟨decoded, hdecode, hsound⟩
  refine ⟨decoded, hdecode, ?_⟩
  intro context hcontext D interpretation hmodels default assignment hcore
  apply hsound context hcontext D
    (CBRoleChainEncoding.extendModel decoded.source.source
      interpretation hmodels default) assignment
  · rw [decoded.source.exact_encoding]
    exact CBRoleChainEncoding.models_extend decoded.source.source
      interpretation hmodels default
  · exact hcore

private def x : WireTerm := .var 0
private def conceptPredicate (id : Nat) : WirePredicate := .concept id x
private def conceptLiteral (id : Nat) : WireLiteral :=
  .predicate (conceptPredicate id)

private def sourceExample : WireSourceBinding where
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  source_clauses := [.gci [0] [1]]
  role_chains := []
  ontology := [⟨[conceptLiteral 0], [conceptLiteral 1]⟩]

private def contextExample : WireProductionContext where
  context_id := 7
  root := true
  query_concept := some 0
  core := [conceptPredicate 0]
  retained := [
    ⟨[conceptLiteral 0], [conceptLiteral 1]⟩,
    ⟨[], [conceptLiteral 0]⟩,
    ⟨[], [conceptLiteral 1]⟩]
  discarded := []
  trace := [
    ⟨⟨[conceptLiteral 0], [conceptLiteral 1]⟩, .premise 0 []⟩,
    ⟨⟨[], [conceptLiteral 0]⟩, .assumption 0⟩,
    ⟨⟨[], [conceptLiteral 1]⟩, .resolve 1 0 (conceptLiteral 0)⟩]

private def acceptedExample : WireProductionRun :=
  { version := 1, source := sourceExample, contexts := [contextExample] }

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example : rejected ({ acceptedExample with contexts :=
    [{ contextExample with retained := contextExample.retained.drop 1 }] }).check = true := by
  native_decide

example : rejected ({ acceptedExample with contexts :=
    [contextExample, contextExample] }).check = true := by native_decide

#print axioms DecodedProductionContext.retained_sound
#print axioms DecodedProductionContext.discarded_sound
#print axioms WireProductionRun.check_sound
#print axioms WireProductionRun.check_source_sound

end ContextCalculus.CBProductionTraceWire
