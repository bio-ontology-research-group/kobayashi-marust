import ContextCalculus.CBLiveInsertionDerivation

/-!
# Sound publication of a live CB taxonomy

Each published positive cell names the exact query context and retained unit
clause that witnesses it. The chronological production certificate proves that
clause context-valid; this file turns that fact into semantic atomic
subsumption for the exact normalized source.
-/

namespace ContextCalculus.CBLiveTaxonomyPublication

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLiveStateWire
open ContextCalculus.CBLiveInsertionDerivation

structure WireLiveSubsumption where
  sub : Nat
  sup : Nat
  context_index : Nat
deriving FromJson, ToJson

structure WireLiveUnsatisfiable where
  sub : Nat
  context_index : Nat
deriving FromJson, ToJson

structure WireLiveTaxonomyPublication where
  version : Nat
  derivation : WireLiveInsertionDerivationDocument
  public_subsumptions : List WireLiveSubsumption
  unsatisfiable : List WireLiveUnsatisfiable
deriving FromJson, ToJson

def queryCore (sub : Nat) : List FPred :=
  [.concept sub (.var 0)]

def subsumptionClause (sup : Nat) : FCL :=
  ⟨[], [.P (.concept sup (.var 0))]⟩

def contradictionClause : FCL := ⟨[], []⟩

structure DecodedLiveSubsumption
    (derivation : DecodedLiveInsertionDerivationDocument) where
  sub : Fin (rProduction derivation.live.global.global.rsucc).source.bounds.concepts
  sup : Fin (rProduction derivation.live.global.global.rsucc).source.bounds.concepts
  contextListIndex : Fin derivation.live.contexts.length
  contextIndex : Fin (rProduction derivation.live.global.global.rsucc).contexts.length
  context_index_eq :
    (derivation.live.contexts.get contextListIndex).contextIndex = contextIndex
  query_eq :
    ((rProduction derivation.live.global.global.rsucc).contexts.get
      contextIndex).queryConcept = some sub.val
  core_eq :
    ((rProduction derivation.live.global.global.rsucc).contexts.get
      contextIndex).core = queryCore sub.val
  clause_mem : subsumptionClause sup.val ∈
    (derivation.live.contexts.get contextListIndex).retained

def WireLiveSubsumption.decode
    (derivation : DecodedLiveInsertionDerivationDocument)
    (wire : WireLiveSubsumption) :
    Except String (DecodedLiveSubsumption derivation) := do
  let production := rProduction derivation.live.global.global.rsucc
  if hsub : wire.sub < production.source.bounds.concepts then
    let sub : Fin production.source.bounds.concepts := ⟨wire.sub, hsub⟩
    if hsup : wire.sup < production.source.bounds.concepts then
      let sup : Fin production.source.bounds.concepts := ⟨wire.sup, hsup⟩
      if hlist : wire.context_index < derivation.live.contexts.length then
        let contextListIndex : Fin derivation.live.contexts.length :=
          ⟨wire.context_index, hlist⟩
        let context := derivation.live.contexts.get contextListIndex
        let contextIndex := context.contextIndex
        if hquery : (production.contexts.get contextIndex).queryConcept = some sub.val then
          if hcore : (production.contexts.get contextIndex).core = queryCore sub.val then
            if hclause : subsumptionClause sup.val ∈ context.retained then
              return {
                sub
                sup
                contextListIndex
                contextIndex
                context_index_eq := rfl
                query_eq := hquery
                core_eq := hcore
                clause_mem := hclause
              }
            else throw "published CB subsumption has no retained unit witness"
          else throw "published CB subsumption context has a different core"
        else throw "published CB subsumption context has a different query"
      else throw "published CB subsumption context index is outside the live run"
    else throw "published CB superconcept is outside the source signature"
  else throw "published CB subconcept is outside the source signature"

structure DecodedLiveUnsatisfiable
    (derivation : DecodedLiveInsertionDerivationDocument) where
  sub : Fin (rProduction derivation.live.global.global.rsucc).source.bounds.concepts
  contextListIndex : Fin derivation.live.contexts.length
  contextIndex : Fin (rProduction derivation.live.global.global.rsucc).contexts.length
  context_index_eq :
    (derivation.live.contexts.get contextListIndex).contextIndex = contextIndex
  query_eq :
    ((rProduction derivation.live.global.global.rsucc).contexts.get
      contextIndex).queryConcept = some sub.val
  core_eq :
    ((rProduction derivation.live.global.global.rsucc).contexts.get
      contextIndex).core = queryCore sub.val
  contradiction_mem : contradictionClause ∈
    (derivation.live.contexts.get contextListIndex).retained

def WireLiveUnsatisfiable.decode
    (derivation : DecodedLiveInsertionDerivationDocument)
    (wire : WireLiveUnsatisfiable) :
    Except String (DecodedLiveUnsatisfiable derivation) := do
  let production := rProduction derivation.live.global.global.rsucc
  if hsub : wire.sub < production.source.bounds.concepts then
    let sub : Fin production.source.bounds.concepts := ⟨wire.sub, hsub⟩
    if hlist : wire.context_index < derivation.live.contexts.length then
      let contextListIndex : Fin derivation.live.contexts.length :=
        ⟨wire.context_index, hlist⟩
      let context := derivation.live.contexts.get contextListIndex
      let contextIndex := context.contextIndex
      if hquery : (production.contexts.get contextIndex).queryConcept = some sub.val then
        if hcore : (production.contexts.get contextIndex).core = queryCore sub.val then
          if hcontradiction : contradictionClause ∈ context.retained then
            return {
              sub
              contextListIndex
              contextIndex
              context_index_eq := rfl
              query_eq := hquery
              core_eq := hcore
              contradiction_mem := hcontradiction
            }
          else throw "published CB unsatisfiable row has no retained contradiction"
        else throw "published CB unsatisfiable context has a different core"
      else throw "published CB unsatisfiable context has a different query"
    else throw "published CB unsatisfiable context index is outside the live run"
  else throw "published CB unsatisfiable concept is outside the source signature"

structure DecodedLiveTaxonomyPublication where
  derivation : DecodedLiveInsertionDerivationDocument
  publicSubsumptions : List (DecodedLiveSubsumption derivation)
  unsatisfiable : List (DecodedLiveUnsatisfiable derivation)

def WireLiveTaxonomyPublication.decode
    (wire : WireLiveTaxonomyPublication) :
    Except String DecodedLiveTaxonomyPublication := do
  if wire.version != 1 then
    throw s!"unsupported live CB taxonomy-publication version {wire.version}"
  let derivation ← wire.derivation.decode
  let publicSubsumptions ← wire.public_subsumptions.mapM
    (WireLiveSubsumption.decode derivation)
  let unsatisfiable ← wire.unsatisfiable.mapM
    (WireLiveUnsatisfiable.decode derivation)
  return { derivation, publicSubsumptions, unsatisfiable }

def WireLiveTaxonomyPublication.check
    (wire : WireLiveTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedLiveSubsumption.entails
    (cell : DecodedLiveSubsumption derivation) :
    (rProduction derivation.live.global.global.rsucc).source.Entails
      cell.sub cell.sup := by
  intro D model hontology element hsub
  let context := derivation.live.contexts.get cell.contextListIndex
  have hcontext : context ∈ derivation.live.contexts :=
    List.get_mem derivation.live.contexts cell.contextListIndex
  have hvalid := derivation.retained_contextValid context hcontext
    (subsumptionClause cell.sup.val) cell.clause_mem model hontology
  have hcore : CoreHolds model (fun _ => element)
      ((rProduction derivation.live.global.global.rsucc).contexts.get
        context.contextIndex).core := by
    rw [cell.context_index_eq, cell.core_eq]
    intro predicate hpredicate
    simp only [queryCore, List.mem_singleton] at hpredicate
    subst predicate
    exact hsub
  have hholds := hvalid (fun _ => element) hcore
  have hholds := hholds (by
    intro literal hliteral
    cases hliteral)
  obtain ⟨literal, hliteral, htrue⟩ := hholds
  simp only [subsumptionClause, List.mem_singleton] at hliteral
  subst literal
  exact htrue

theorem DecodedLiveUnsatisfiable.refutes
    (row : DecodedLiveUnsatisfiable derivation) :
    ∀ (D : Type) (model : TModel D),
      (∀ source ∈
        (rProduction derivation.live.global.global.rsucc).source.ontology,
        valid model source) →
      ∀ element, ¬model.conc row.sub.val element := by
  intro D model hontology element hsub
  let context := derivation.live.contexts.get row.contextListIndex
  have hcontext : context ∈ derivation.live.contexts :=
    List.get_mem derivation.live.contexts row.contextListIndex
  have hvalid := derivation.retained_contextValid context hcontext
    contradictionClause row.contradiction_mem model hontology
  have hcore : CoreHolds model (fun _ => element)
      ((rProduction derivation.live.global.global.rsucc).contexts.get
        context.contextIndex).core := by
    rw [row.context_index_eq, row.core_eq]
    intro predicate hpredicate
    simp only [queryCore, List.mem_singleton] at hpredicate
    subst predicate
    exact hsub
  have hfalse := hvalid (fun _ => element) hcore (by
    intro literal hliteral
    cases hliteral)
  obtain ⟨literal, hliteral, _⟩ := hfalse
  cases hliteral

theorem WireLiveTaxonomyPublication.check_sound
    (wire : WireLiveTaxonomyPublication) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveTaxonomyPublication,
      wire.decode = .ok decoded ∧
      (∀ cell ∈ decoded.publicSubsumptions,
        (rProduction decoded.derivation.live.global.global.rsucc).source.Entails
          cell.sub cell.sup) ∧
      (∀ row ∈ decoded.unsatisfiable,
        ∀ (D : Type) (model : TModel D),
          (∀ source ∈
            (rProduction decoded.derivation.live.global.global.rsucc).source.ontology,
            valid model source) →
          ∀ element, ¬model.conc row.sub.val element) := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLiveTaxonomyPublication.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, fun cell _ => cell.entails,
        fun row _ => row.refutes⟩

#print axioms DecodedLiveSubsumption.entails
#print axioms DecodedLiveUnsatisfiable.refutes
#print axioms WireLiveTaxonomyPublication.check_sound

end ContextCalculus.CBLiveTaxonomyPublication
