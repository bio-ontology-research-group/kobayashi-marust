import ContextCalculus.CBSourceLocalClosure
import ContextCalculus.CBHyperClosure
import ContextCalculus.CBTermDerivationWire

/-!
# Source-bound Hyper closure

This layer reconstructs the finite term and literal universe directly from the
source-bound production snapshot.  It does not accept candidate lists from
Rust.  Lean enumerates all source substitutions and all maximal retained
providers, constructs every Hyper conclusion, and requires a retained
strengthening.
-/

namespace ContextCalculus.CBSourceHyperClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceLocalClosure
open ContextCalculus.CBHyperClosure
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBFiniteModel
open ContextCalculus.CBPredEnumeration
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteLiteralOrderWire

def sourceProductionTerms
    (production : DecodedProductionRun) : List FTerm :=
  ((production.source.ontology.flatMap clauseTerms) ++
    (production.contexts.flatMap fun context =>
      context.retained.flatMap clauseTerms)).eraseDups

def sourceProductionLiterals
    (production : DecodedProductionRun) : List FLit :=
  ((production.source.ontology.flatMap clauseLiterals) ++
    (production.contexts.flatMap fun context =>
      context.retained.flatMap clauseLiterals)).eraseDups

def supportedProductionTerm : FTerm → Bool
  | .var _ | .const _ => true
  | .app _ (.var 0) | .app _ (.const _) => true
  | .app _ _ => false

/-- Structural image of KM's unsigned production term ids: neighbours ordered
by variable index, then individuals, then `f(x)`, then lexicographic `f(o)`. -/
def productionTermLt : FTerm → FTerm → Bool
  | .var left, .var right => left < right
  | .var _, _ => true
  | _, .var _ => false
  | .const left, .const right => left < right
  | .const _, .app _ _ => true
  | .app _ _, .const _ => false
  | .app left (.var 0), .app right (.var 0) => left < right
  | .app _ (.var 0), .app _ (.const _) => true
  | .app _ (.const _), .app _ (.var 0) => false
  | .app left (.const leftIndividual),
      .app right (.const rightIndividual) =>
      left < right || (left = right && leftIndividual < rightIndividual)
  | .app _ _, .app _ _ => false

inductive SourceConceptOrderMode where
  | incomparable
  | sequoia
  | total
  | internalTotal
deriving DecidableEq, FromJson, ToJson

def SourceConceptOrderMode.directReadoutSafe : SourceConceptOrderMode → Bool
  | .incomparable | .sequoia => true
  | .total | .internalTotal => false

structure WireSourceFiniteOrder where
  ordered_terms : List WireTerm
  ordered_literals : List WireLiteral
  root_concept_mode : SourceConceptOrderMode
  non_root_concept_mode : SourceConceptOrderMode
  internal_concepts : List Bool
  pred_triggers : List WireLiteral
deriving FromJson, ToJson

structure DecodedSourceFiniteOrder
    (production : DecodedProductionRun) where
  orderedTerms : List FTerm
  orderedLiterals : List FLit
  rootConceptMode : SourceConceptOrderMode
  nonRootConceptMode : SourceConceptOrderMode
  internalConcepts : List Bool
  predTriggers : List FLit
  terms_nodup : orderedTerms.Nodup
  terms_supported : (orderedTerms.all supportedProductionTerm) = true
  terms_sorted : orderedTerms.Pairwise fun left right =>
    productionTermLt left right = true
  literals_nodup : orderedLiterals.Nodup
  internal_count : internalConcepts.length = production.bounds.concepts
  root_mode_safe : rootConceptMode.directReadoutSafe = true
  non_root_mode_safe : nonRootConceptMode.directReadoutSafe = true
  query_concepts_named : (production.contexts.all fun context =>
    match context.queryConcept with
    | none => true
    | some concept => internalConcepts[concept]?.getD true = false) = true
  pred_triggers_nodup : predTriggers.Nodup
  pred_triggers_predicates : (predTriggers.all fun literal =>
    match literal with | .P _ => true | _ => false) = true
  pred_triggers_present : (predTriggers.all fun literal =>
    literal ∈ sourceProductionLiterals production) = true
  terms_exact : orderedTerms.toFinset =
    (sourceProductionTerms production).toFinset
  literals_exact : orderedLiterals.toFinset =
    (sourceProductionLiterals production).toFinset

def WireSourceFiniteOrder.decode (production : DecodedProductionRun)
    (wire : WireSourceFiniteOrder) :
    Except String (DecodedSourceFiniteOrder production) := do
  let orderedTerms ← wire.ordered_terms.mapM
    (WireTerm.decode production.bounds)
  let orderedLiterals ← wire.ordered_literals.mapM
    (WireLiteral.decode production.bounds)
  let predTriggers ← wire.pred_triggers.mapM
    (WireLiteral.decode production.bounds)
  if htermsNodup : orderedTerms.Nodup then
    if htermsSupported : orderedTerms.all supportedProductionTerm = true then
      if htermsSorted : (orderedTerms.Pairwise fun left right =>
          productionTermLt left right = true) then
        if hliteralsNodup : orderedLiterals.Nodup then
          if hinternalCount : wire.internal_concepts.length =
              production.bounds.concepts then
            if hrootSafe : wire.root_concept_mode.directReadoutSafe = true then
             if hnonRootSafe : wire.non_root_concept_mode.directReadoutSafe = true then
              if hqueriesNamed : (production.contexts.all fun context =>
                  match context.queryConcept with
                  | none => true
                  | some concept =>
                      wire.internal_concepts[concept]?.getD true = false) = true then
               if htriggersNodup : predTriggers.Nodup then
              if htriggersPredicates : (predTriggers.all fun literal =>
                  match literal with | .P _ => true | _ => false) = true then
                if htriggersPresent : (predTriggers.all fun literal =>
                    literal ∈ sourceProductionLiterals production) = true then
                  if htermsExact : orderedTerms.toFinset =
                      (sourceProductionTerms production).toFinset then
                    if hliteralsExact : orderedLiterals.toFinset =
                        (sourceProductionLiterals production).toFinset then
                      return {
                        orderedTerms
                        orderedLiterals
                        rootConceptMode := wire.root_concept_mode
                        nonRootConceptMode := wire.non_root_concept_mode
                        internalConcepts := wire.internal_concepts
                        predTriggers
                        terms_nodup := htermsNodup
                        terms_supported := htermsSupported
                        terms_sorted := htermsSorted
                        literals_nodup := hliteralsNodup
                        internal_count := hinternalCount
                        root_mode_safe := hrootSafe
                        non_root_mode_safe := hnonRootSafe
                        query_concepts_named := hqueriesNamed
                        pred_triggers_nodup := htriggersNodup
                        pred_triggers_predicates := htriggersPredicates
                        pred_triggers_present := htriggersPresent
                        terms_exact := htermsExact
                        literals_exact := hliteralsExact
                      }
                    else throw "source-bound CB literal order omits or invents a literal"
                  else throw "source-bound CB term order omits or invents a term"
                else throw "source-bound CB predecessor trigger is absent"
              else throw "source-bound CB predecessor trigger is not a predicate"
               else throw "source-bound CB predecessor triggers contain a duplicate"
              else throw "source-bound CB query concept is marked internal"
             else throw "source-bound CB non-root order needs a residue certificate"
            else throw "source-bound CB root order needs a residue certificate"
          else throw "source-bound CB internal-concept mask has the wrong length"
        else throw "source-bound CB literal order contains a duplicate"
      else throw "source-bound CB terms do not follow production term order"
    else throw "source-bound CB term universe has an unsupported shape"
  else throw "source-bound CB term order contains a duplicate"

def DecodedSourceFiniteOrder.termRank
    (order : DecodedSourceFiniteOrder production) (term : FTerm) : Nat :=
  order.orderedTerms.idxOf term

def DecodedSourceFiniteOrder.termLt
    (order : DecodedSourceFiniteOrder production) (left right : FTerm) : Bool :=
  order.termRank left < order.termRank right

def DecodedSourceFiniteOrder.termLe
    (order : DecodedSourceFiniteOrder production) (left right : FTerm) : Bool :=
  order.termRank left ≤ order.termRank right

def DecodedSourceFiniteOrder.isInternal
    (order : DecodedSourceFiniteOrder production) (concept : Nat) : Bool :=
  order.internalConcepts[concept]?.getD true

def DecodedSourceFiniteOrder.isPredTrigger
    (order : DecodedSourceFiniteOrder production) (predicate : FPred) : Bool :=
  .P predicate ∈ order.predTriggers

def DecodedSourceFiniteOrder.predMaxTerm
    (order : DecodedSourceFiniteOrder production) : FPred → FTerm
  | .concept _ term => term
  | .role _ source target =>
      if order.termLe source target then target else source

def DecodedSourceFiniteOrder.sameTermConceptLe
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (left right : Nat) : Bool :=
  let mode := if root then order.rootConceptMode else order.nonRootConceptMode
  match mode with
  | .incomparable => left = right
  | .total => left ≤ right
  | .sequoia =>
      match order.isInternal left, order.isInternal right with
      | true, true => left ≤ right
      | false, false => left = right
      | false, true => true
      | true, false => false
  | .internalTotal =>
      match order.isInternal left, order.isInternal right with
      | true, true | false, false => left ≤ right
      | false, true => true
      | true, false => false

def DecodedSourceFiniteOrder.predLe
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (left right : FPred) : Bool :=
  if order.isPredTrigger right then left = right
  else if order.isPredTrigger left then true
  else match left, right with
  | .concept leftIri leftTerm, .concept rightIri rightTerm =>
      if leftTerm = rightTerm then
        order.sameTermConceptLe root leftIri rightIri
      else order.termLt leftTerm rightTerm
  | left, right =>
      let leftMax := order.predMaxTerm left
      let rightMax := order.predMaxTerm right
      if leftMax ≠ rightMax then order.termLt leftMax rightMax
      else match left, right with
      | .role leftIri leftSource leftTarget,
          .role rightIri rightSource rightTarget =>
          order.termLt leftSource rightSource ||
            (leftSource = rightSource &&
              (order.termLt leftTarget rightTarget ||
                (leftTarget = rightTarget && leftIri ≤ rightIri)))
      | .concept leftIri _, .concept rightIri _ => leftIri ≤ rightIri
      | .role .., .concept .. => false
      | .concept .., .role .. => true

def DecodedSourceFiniteOrder.literalLe
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (left right : FLit) : Bool :=
  match left, right with
  | .eq leftSource leftTarget, .eq rightSource rightTarget
  | .eq leftSource leftTarget, .ineq rightSource rightTarget
  | .ineq leftSource leftTarget, .ineq rightSource rightTarget =>
      order.termLt leftSource rightSource ||
        (leftSource = rightSource && order.termLe leftTarget rightTarget)
  | .ineq leftSource leftTarget, .eq rightSource rightTarget =>
      order.termLt leftSource rightSource ||
        (leftSource = rightSource && order.termLt leftTarget rightTarget)
  | .eq source _, .P (.concept _ term)
  | .ineq source _, .P (.concept _ term) => order.termLe source term
  | .eq source _, .P (.role _ leftTerm rightTerm)
  | .ineq source _, .P (.role _ leftTerm rightTerm) =>
      order.termLe source leftTerm || order.termLe source rightTerm
  | .P (.concept _ term), .eq source _
  | .P (.concept _ term), .ineq source _ => !(order.termLe source term)
  | .P (.role _ leftTerm rightTerm), .eq source _
  | .P (.role _ leftTerm rightTerm), .ineq source _ =>
      !(order.termLe source leftTerm || order.termLe source rightTerm)
  | .P leftPredicate, .P rightPredicate =>
      order.predLe root leftPredicate rightPredicate

def DecodedSourceFiniteOrder.maximalHeadIndices
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (head : List FLit) : List Nat :=
  (List.range head.length).filter fun index =>
    match head[index]? with
    | none => false
    | some literal => head.all fun other =>
        decide (other = literal) || !order.literalLe root literal other

theorem mem_maximalHeadIndices_iff
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (head : List FLit) (index : Nat) :
    index ∈ order.maximalHeadIndices root head ↔
      index < head.length ∧
      ∃ literal, head[index]? = some literal ∧
        ∀ other ∈ head, other = literal ∨
          order.literalLe root literal other = false := by
  simp only [DecodedSourceFiniteOrder.maximalHeadIndices,
    List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hindex, hmaximal⟩
    cases hliteral : head[index]? with
    | none => simp [hliteral] at hmaximal
    | some literal =>
        refine ⟨hindex, literal, rfl, ?_⟩
        simpa [hliteral, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true] using hmaximal
  · rintro ⟨hindex, literal, hliteral, hmaximal⟩
    refine ⟨hindex, ?_⟩
    simpa [hliteral, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true] using hmaximal

theorem incomparable_pair_both_maximal
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (left right : FLit)
    (hleftRight : order.literalLe root left right = false)
    (hrightLeft : order.literalLe root right left = false) :
    0 ∈ order.maximalHeadIndices root [left, right] ∧
      1 ∈ order.maximalHeadIndices root [left, right] := by
  constructor <;> rw [mem_maximalHeadIndices_iff]
  · exact ⟨by simp, left, by simp, by
      intro other hother
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hother
      rcases hother with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hleftRight⟩
  · exact ⟨by simp, right, by simp, by
      intro other hother
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hother
      rcases hother with rfl | rfl
      · exact Or.inr hrightLeft
      · exact Or.inl rfl⟩

structure LinearExtensionOn
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (support : List FLit) (rank : FLit → Nat) : Prop where
  injective : ∀ left ∈ support, ∀ right ∈ support,
    rank left = rank right → left = right
  preserves : ∀ left ∈ support, ∀ right ∈ support,
    order.literalLe root left right = true → rank left ≤ rank right

/-- A maximum chosen by any injective total ranking extending production's
partial literal order is production-maximal. This is the transfer needed to
use a total ordered canonical-model construction while relying on KM's
all-partial-maxima rule coverage. -/
theorem total_rank_maximal_is_production_maximal
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (head : List FLit) (rank : FLit → Nat)
    (hextension : LinearExtensionOn order root head rank)
    (index : Nat) (literal : FLit)
    (hindex : head[index]? = some literal)
    (hmax : ∀ other ∈ head, rank other ≤ rank literal) :
    index ∈ order.maximalHeadIndices root head := by
  rw [mem_maximalHeadIndices_iff]
  have hbound : index < head.length :=
    (List.getElem?_eq_some_iff.mp hindex).1
  have hliteral : literal ∈ head := by
    obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp hindex
    rw [← hget]
    exact List.getElem_mem hbound
  refine ⟨hbound, literal, hindex, ?_⟩
  intro other hother
  by_cases hequal : other = literal
  · exact Or.inl hequal
  · apply Or.inr
    apply Bool.eq_false_iff.mpr
    intro hle
    have hrankLe : rank literal ≤ rank other :=
      hextension.preserves literal hliteral other hother hle
    have hrankEq : rank literal = rank other :=
      Nat.le_antisymm hrankLe (hmax other hother)
    exact hequal (hextension.injective other hother literal hliteral
      hrankEq.symm)

def maximalProvidersFor
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (literal : FLit) : List ProviderLocation :=
  (List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some provider =>
        ((order.maximalHeadIndices root provider.head).filter fun headIndex =>
          decide (provider.head[headIndex]? = some literal)).map fun headIndex =>
            (clauseIndex, headIndex)

theorem mem_maximalProvidersFor_iff
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (literal : FLit)
    (location : ProviderLocation) :
    location ∈ maximalProvidersFor order root retained literal ↔
      location.1 < retained.length ∧
      ∃ provider, retained[location.1]? = some provider ∧
        location.2 ∈ order.maximalHeadIndices root provider.head ∧
        provider.head[location.2]? = some literal := by
  rcases location with ⟨clauseIndex, headIndex⟩
  simp only [maximalProvidersFor, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨candidateIndex, hbound, hmember⟩
    cases hprovider : retained[candidateIndex]? with
    | none => simp [hprovider] at hmember
    | some provider =>
        simp only [hprovider, List.mem_map, List.mem_filter,
          decide_eq_true_eq] at hmember
        rcases hmember with ⟨selectedHead, ⟨hmaximal, hliteral⟩, heq⟩
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨hbound, provider, hprovider, hmaximal, hliteral⟩
  · rintro ⟨hbound, provider, hprovider, hmaximal, hliteral⟩
    refine ⟨clauseIndex, hbound, ?_⟩
    simp only [hprovider, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨headIndex, ⟨hmaximal, hliteral⟩, rfl⟩

def providerSelections
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (body : List FLit) :
    List (List ProviderLocation) :=
  cartesianSelections (body.map (maximalProvidersFor order root retained))

theorem mem_providerSelections_iff
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (body : List FLit)
    (selection : List ProviderLocation) :
    selection ∈ providerSelections order root retained body ↔
      Selects selection
        (body.map (maximalProvidersFor order root retained)) :=
  mem_cartesianSelections_iff selection _

theorem providerAt_of_mem_maximalProvidersFor
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (literal : FLit)
    (location : ProviderLocation)
    (hlocation : location ∈ maximalProvidersFor order root retained literal) :
    ∃ provider,
      providerAt retained literal location = some (literal, provider) := by
  obtain ⟨_, provider, hprovider, _, hhead⟩ :=
    (mem_maximalProvidersFor_iff order root retained literal location).mp
      hlocation
  refine ⟨provider, ?_⟩
  rcases location with ⟨clauseIndex, headIndex⟩
  simp [providerAt, hprovider, hhead]

theorem selectedProviders_exists_of_mem_providerSelections
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) :
    ∀ {body selection},
      selection ∈ providerSelections order root retained body →
      ∃ providers,
        selectedProviders retained body selection = some providers := by
  intro body
  induction body with
  | nil =>
      intro selection hselection
      have hselects :=
        (mem_providerSelections_iff order root retained [] selection).mp
          hselection
      cases selection with
      | nil => exact ⟨[], rfl⟩
      | cons location locations => simp [Selects] at hselects
  | cons literal body ih =>
      intro selection hselection
      have hselects :=
        (mem_providerSelections_iff order root retained
          (literal :: body) selection).mp hselection
      cases selection with
      | nil => simp [Selects] at hselects
      | cons location locations =>
          simp only [List.map_cons, Selects] at hselects
          obtain ⟨hlocation, hlocations⟩ := hselects
          obtain ⟨provider, hprovider⟩ :=
            providerAt_of_mem_maximalProvidersFor order root retained literal
              location hlocation
          have htailMember : locations ∈
              providerSelections order root retained body :=
            (mem_providerSelections_iff order root retained body locations).mpr
              hlocations
          obtain ⟨providers, hproviders⟩ := ih htailMember
          exact ⟨(literal, provider) :: providers, by
            simp [selectedProviders, hprovider, hproviders]⟩

theorem hyperResolution_exists_of_mem_providerSelections
    (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) (source : FCL)
    (selection : List ProviderLocation)
    (hselection : selection ∈
      providerSelections order root retained source.body) :
    ∃ providers raw,
      selectedProviders retained source.body selection = some providers ∧
      resolveProviders source providers = some raw := by
  obtain ⟨providers, hproviders⟩ :=
    selectedProviders_exists_of_mem_providerSelections order root retained
      hselection
  have hdecoded := selectedProviders_sound retained hproviders
  obtain ⟨raw, hraw⟩ := resolveProviders_exists_of_provider_heads source
    providers (fun selected hselected => (hdecoded.2 selected hselected).2)
  exact ⟨providers, raw, hproviders, hraw⟩

def hyperCandidates (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained source : List FCL) : List FCL :=
  source.flatMap fun sourceClause =>
    (substitutions order.orderedTerms sourceClause).flatMap fun substitution =>
      let instantiated := substCl substitution sourceClause
      (providerSelections order root retained instantiated.body).filterMap fun selection =>
        hyperCandidate? retained sourceClause substitution selection

theorem hyperCandidates_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (retained source : List FCL)
    (hsource : ∀ clause ∈ source, valid model clause)
    (hretained : ∀ clause ∈ retained, HoldsAt model assignment clause) :
    ∀ conclusion ∈ hyperCandidates order root retained source,
      HoldsAt model assignment conclusion := by
  intro conclusion hconclusion
  simp only [hyperCandidates, List.mem_flatMap, List.mem_filterMap] at hconclusion
  obtain ⟨sourceClause, hsourceClause, substitution, _hsubstitution,
    selection, _hselection, hcandidate⟩ := hconclusion
  exact hyperCandidate_sound model assignment retained sourceClause substitution
    selection conclusion hcandidate (hsource sourceClause hsourceClause) hretained

def sourceHyperClosedB (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology) : Bool :=
  (hyperCandidates order context.root context.retained production.source.ontology).all
    (hasStrengthening context.retained)

theorem sourceHyperClosedB_sound
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hclosed : sourceHyperClosedB order context = true) :
    ∀ candidate ∈ hyperCandidates order context.root context.retained
        production.source.ontology,
      ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro candidate hcandidate
  have h := List.all_eq_true.mp hclosed candidate hcandidate
  exact (hasStrengthening_eq_true_iff context.retained candidate).mp h

structure WireSourceHyperClosureDocument where
  version : Nat
  local_closure : WireSourceLocalClosureDocument
  order : WireSourceFiniteOrder
deriving FromJson, ToJson

structure DecodedSourceHyperClosureDocument where
  localClosure : DecodedSourceLocalClosureDocument
  order : DecodedSourceFiniteOrder localClosure.live.production
  hyper_closed : ∀ context ∈ localClosure.live.production.contexts,
    sourceHyperClosedB order context = true

def WireSourceHyperClosureDocument.decode
    (wire : WireSourceHyperClosureDocument) :
    Except String DecodedSourceHyperClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB Hyper-closure version {wire.version}"
  let localClosure ← wire.local_closure.decode
  let order ← wire.order.decode localClosure.live.production
  if hclosed : ∀ context ∈ localClosure.live.production.contexts,
      sourceHyperClosedB order context = true then
    return { localClosure, order, hyper_closed := hclosed }
  else throw "source-bound CB terminal state is not Hyper-closed"

def WireSourceHyperClosureDocument.check
    (wire : WireSourceHyperClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceHyperClosureDocument.complete_coverage
    (decoded : DecodedSourceHyperClosureDocument) :
    ∀ context ∈ decoded.localClosure.live.production.contexts,
      ∀ candidate ∈ hyperCandidates decoded.order context.root context.retained
          decoded.localClosure.live.production.source.ontology,
        ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro context hcontext
  exact sourceHyperClosedB_sound decoded.order context
    (decoded.hyper_closed context hcontext)

theorem WireSourceHyperClosureDocument.check_sound
    (wire : WireSourceHyperClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceHyperClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.localClosure.live.production.contexts,
        ∀ candidate ∈ hyperCandidates decoded.order context.root context.retained
            decoded.localClosure.live.production.source.ontology,
          ∃ clause ∈ context.retained, Strengthens clause candidate := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceHyperClosureDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.complete_coverage⟩

#print axioms hyperCandidates_sound
#print axioms mem_maximalHeadIndices_iff
#print axioms incomparable_pair_both_maximal
#print axioms total_rank_maximal_is_production_maximal
#print axioms mem_maximalProvidersFor_iff
#print axioms mem_providerSelections_iff
#print axioms providerAt_of_mem_maximalProvidersFor
#print axioms selectedProviders_exists_of_mem_providerSelections
#print axioms hyperResolution_exists_of_mem_providerSelections
#print axioms sourceHyperClosedB_sound
#print axioms WireSourceHyperClosureDocument.check_sound

end ContextCalculus.CBSourceHyperClosure
