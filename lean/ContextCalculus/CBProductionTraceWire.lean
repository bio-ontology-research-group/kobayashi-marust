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
open ContextCalculus.CBClauseShape

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
  nominal_ground : Bool
  query_concept : Option Nat
  core : List WirePredicate
  /-- Clauses imported through the globally checked chronological insertion
  DAG (in particular Pred). They are assumptions of this local trace, but are
  not source premises. The enclosing live-derivation theorem must discharge
  their context validity. -/
  imports : Option (List WireClause) := none
  retained : List WireClause
  discarded : List WireDiscardedClause
  trace : List WireProductionEntry
deriving FromJson, ToJson

structure WireProductionRun where
  version : Nat
  source : WireSourceBinding
  individual_count : Nat
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
  nominalGround : Bool
  nominal_ground_root : nominalGround = true → root = true
  queryConcept : Option Nat
  core : List FPred
  core_nodup : core.Nodup
  imports : List FCL
  assumptions : List FCL
  assumptions_eq : assumptions = core.map assumptionClause ++ imports
  retained : List FCL
  retained_predicate_body : ∀ clause ∈ retained, PredicateBody clause
  imports_retained : ∀ imported ∈ imports, imported ∈ retained
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
      let imports ← (wire.imports.getD []).mapM (WireClause.decode bounds)
      let assumptions := core.map assumptionClause ++ imports
      let retained ← wire.retained.mapM (WireClause.decode bounds)
      let discarded ← wire.discarded.mapM (WireDiscardedClause.decode bounds retained)
      let trace ← wire.trace.mapM (WireProductionEntry.decode bounds)
      if hretainedBodies : retained.all predicateBodyB = true then
        if himportsRetained : ∀ imported ∈ imports, imported ∈ retained then
          if hretained : retained = terminal trace then
            if htrace : check ontology assumptions trace = true then
              if hnominalRoot : wire.nominal_ground = true → wire.root = true then
                return {
                  contextId := wire.context_id
                  root := wire.root
                  nominalGround := wire.nominal_ground
                  nominal_ground_root := hnominalRoot
                  queryConcept
                  core
                  core_nodup := hdecodedCoreNodup
                  imports
                  imports_retained := himportsRetained
                  assumptions
                  assumptions_eq := rfl
                  retained
                  retained_predicate_body :=
                    (all_predicateBodyB_eq_true_iff retained).mp hretainedBodies
                  discarded
                  trace
                  retained_eq := hretained
                  trace_valid := htrace
                }
              else throw "nominal ground context is not a root context"
            else throw "production context trace was rejected"
          else throw "production retained clauses differ from the checked trace terminal"
        else throw "production context import is absent from the retained state"
      else throw "production retained clause body contains a non-predicate literal"
    else throw "decoded production context core contains duplicates"
  else throw "production context core contains duplicate predicates"

def CoreHolds {D : Type} (model : TModel D) (assignment : Int → D)
    (core : List FPred) : Prop :=
  ∀ predicate ∈ core, model.evalL assignment (.P predicate)

theorem DecodedProductionContext.retained_sound
    (decoded : DecodedProductionContext bounds ontology)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hcore : CoreHolds model assignment decoded.core)
    (himports : ∀ imported ∈ decoded.imports,
      HoldsAt model assignment imported) :
    ∀ clause ∈ decoded.retained, HoldsAt model assignment clause := by
  rw [decoded.retained_eq]
  apply CBProductionTrace.check_sound model assignment
    (assumptions := decoded.assumptions) (trace := decoded.trace) hontology
  · intro assumption hassumption
    rw [decoded.assumptions_eq] at hassumption
    rcases List.mem_append.mp hassumption with hcoreAssumption | himport
    · simp only [List.mem_map] at hcoreAssumption
      obtain ⟨predicate, hpredicate, rfl⟩ := hcoreAssumption
      intro _
      exact ⟨.P predicate, List.mem_singleton.mpr rfl,
        hcore predicate hpredicate⟩
    · exact himports assumption himport
  · exact decoded.trace_valid

theorem DecodedProductionContext.retained_sound_no_import
    (decoded : DecodedProductionContext bounds ontology)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hcore : CoreHolds model assignment decoded.core)
    (himports : decoded.imports = []) :
    ∀ clause ∈ decoded.retained, HoldsAt model assignment clause := by
  apply decoded.retained_sound model assignment hontology hcore
  simp [himports]

theorem DecodedProductionContext.discarded_sound
    (decoded : DecodedProductionContext bounds ontology)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hcore : CoreHolds model assignment decoded.core)
    (himports : ∀ imported ∈ decoded.imports,
      HoldsAt model assignment imported) :
    ∀ discarded ∈ decoded.discarded,
      HoldsAt model assignment discarded.clause := by
  intro discarded _
  apply HoldsAt.of_strengthens model assignment discarded.strengthens
  exact decoded.retained_sound model assignment hontology hcore himports
    (decoded.retained.get discarded.strengtheningIndex)
    (List.get_mem decoded.retained discarded.strengtheningIndex)

structure DecodedProductionRun where
  source : DecodedSourceBinding
  bounds : Bounds
  source_individuals_le : source.bounds.individuals ≤ bounds.individuals
  bounds_concepts_eq : bounds.concepts = source.bounds.concepts
  bounds_roles_eq : bounds.roles = source.bounds.roles
  bounds_functions_eq : bounds.functions = source.bounds.functions
  contexts : List (DecodedProductionContext bounds source.ontology)
  context_ids_nodup : (contexts.map (·.contextId)).Nodup

def WireProductionRun.decode (wire : WireProductionRun) :
    Except String DecodedProductionRun := do
  if wire.version != 2 then
    throw s!"unsupported CB production-trace version {wire.version}"
  if wire.contexts.isEmpty then
    throw "CB production trace must contain at least one context"
  if _hwireIds : (wire.contexts.map (·.context_id)).Nodup then
    let source ← wire.source.decode
    if hcount : source.bounds.individuals ≤ wire.individual_count then
      let bounds : Bounds :=
        { source.bounds with individuals := wire.individual_count }
      let contexts ← wire.contexts.mapM
        (WireProductionContext.decode bounds source.ontology)
      if hids : (contexts.map (·.contextId)).Nodup then
        return {
          source
          bounds
          source_individuals_le := hcount
          bounds_concepts_eq := rfl
          bounds_roles_eq := rfl
          bounds_functions_eq := rfl
          contexts
          context_ids_nodup := hids
        }
      else throw "decoded CB production context ids contain duplicates"
    else throw "CB production individual table is smaller than the source table"
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
          (∀ imported ∈ context.imports,
            HoldsAt model assignment imported) →
          (∀ clause ∈ context.retained, HoldsAt model assignment clause) ∧
          (∀ discarded ∈ context.discarded,
            HoldsAt model assignment discarded.clause) := by
  cases hdecode : wire.decode with
  | error message => simp [WireProductionRun.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro context hcontext D model assignment hontology hcore himports
      exact ⟨context.retained_sound model assignment hontology hcore himports,
        context.discarded_sound model assignment hontology hcore himports⟩

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
            (decoded.source.productionModel interpretation hmodels default)
              assignment context.core →
          (∀ imported ∈ context.imports,
            HoldsAt
              (decoded.source.productionModel interpretation hmodels default)
                assignment imported) →
          (∀ clause ∈ context.retained,
              HoldsAt
                (decoded.source.productionModel interpretation hmodels default)
                  assignment clause) ∧
          (∀ discarded ∈ context.discarded,
              HoldsAt
                (decoded.source.productionModel interpretation hmodels default)
                  assignment
                discarded.clause) := by
  rcases wire.check_sound hcheck with ⟨decoded, hdecode, hsound⟩
  refine ⟨decoded, hdecode, ?_⟩
  intro context hcontext D interpretation hmodels default assignment hcore himports
  apply hsound context hcontext D
    (decoded.source.productionModel interpretation hmodels default) assignment
  · exact decoded.source.models_production interpretation hmodels default
  · exact hcore
  · exact himports

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
  nominal_ground := false
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
  { version := 2, source := sourceExample, individual_count := 0,
    contexts := [contextExample] }

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example : rejected ({ acceptedExample with contexts :=
    [{ contextExample with retained := contextExample.retained.drop 1 }] }).check = true := by
  native_decide

example : rejected ({ acceptedExample with contexts :=
    [contextExample, contextExample] }).check = true := by native_decide

private def importedClause : WireClause :=
  ⟨[], [conceptLiteral 1]⟩

private def importedContextExample : WireProductionContext where
  context_id := 9
  root := true
  nominal_ground := false
  query_concept := some 0
  core := [conceptPredicate 0]
  imports := some [importedClause]
  retained := [importedClause]
  discarded := []
  trace := [⟨importedClause, .assumption 1⟩]

private def acceptedImportedExample : WireProductionRun :=
  { acceptedExample with contexts := [importedContextExample] }

example : acceptedImportedExample.check = .ok true := by native_decide

example : rejected ({ acceptedImportedExample with contexts :=
    [{ importedContextExample with retained := [] }] }).check = true := by
  native_decide

example : rejected ({ acceptedImportedExample with contexts :=
    [{ importedContextExample with imports := some [⟨[], []⟩] }] }).check = true := by
  native_decide

private def freshLiteral : WireLiteral :=
  .predicate (.concept 0 (.constant 0))

private def freshContextExample : WireProductionContext where
  context_id := 8
  root := true
  nominal_ground := true
  query_concept := none
  core := []
  retained := [⟨[freshLiteral], [freshLiteral]⟩]
  discarded := []
  trace := [⟨⟨[freshLiteral], [freshLiteral]⟩, .tautology⟩]

private def expandedIndividualExample : WireProductionRun :=
  { acceptedExample with
    individual_count := 1
    contexts := [freshContextExample] }

example : expandedIndividualExample.check = .ok true := by native_decide

example : rejected
    ({ expandedIndividualExample with individual_count := 0 }).check = true := by
  native_decide

#print axioms DecodedProductionContext.retained_sound
#print axioms DecodedProductionContext.discarded_sound
#print axioms WireProductionRun.check_sound
#print axioms WireProductionRun.check_source_sound

end ContextCalculus.CBProductionTraceWire
