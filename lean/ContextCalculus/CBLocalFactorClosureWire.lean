import ContextCalculus.CBLocalResolutionClosureWire

/-!
# Exact local Factor and head-simplification closure

This layer mirrors the production Factor candidate scan over every ordered pair
of distinct head equalities with the same left side and different right sides.
It also mirrors the semantically relevant parts of `filter_head`: reflexive
equalities and equality/inequality complements discard a tautological result,
while reflexive inequalities are removed. Every remaining Factor result must
have a retained syntactic strengthening.

The checker additionally requires every terminal retained head to have already
passed those simplifications. This closes Factor and reflexive-inequality
normalization modulo retained-clause redundancy. It does not cover general Eq
paramodulation or the other remaining production rule families.
-/

namespace ContextCalculus.CBLocalFactorClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLocalResolutionClosureWire

def isReflexiveEquality : FLit → Bool
  | .eq left right => decide (left = right)
  | _ => false

def isReflexiveInequality : FLit → Bool
  | .ineq left right => decide (left = right)
  | _ => false

def filterReflexiveHead (head : List FLit) : Option (List FLit) :=
  if head.any isReflexiveEquality then none
  else some (head.filter fun literal => !isReflexiveInequality literal)

def hasEqualityComplement (head : List FLit) : Bool :=
  head.any fun literal => match literal with
    | .eq left right => .ineq left right ∈ head
    | _ => false

def normalizeGeneratedHead (head : List FLit) : Option (List FLit) := do
  let filtered ← filterReflexiveHead head
  if hasEqualityComplement filtered then none else some filtered

def terminalHeadNormal (head : List FLit) : Bool :=
  normalizeGeneratedHead head = some head

theorem HoldsAt.filterReflexiveHead_sound {D : Type}
    (model : TModel D) (assignment : Int → D) (source : FCL)
    (filtered : List FLit) (hfilter : filterReflexiveHead source.head = some filtered)
    (hsource : HoldsAt model assignment source) :
    HoldsAt model assignment { source with head := filtered } := by
  unfold filterReflexiveHead at hfilter
  split at hfilter
  · contradiction
  next _ =>
    simp only [Option.some.injEq] at hfilter
    subst filtered
    intro hbody
    obtain ⟨literal, hliteral, htrue⟩ := hsource hbody
    refine ⟨literal, List.mem_filter.mpr ⟨hliteral, ?_⟩, htrue⟩
    cases literal with
    | P predicate => rfl
    | eq left right => rfl
    | ineq left right =>
        by_cases heq : left = right
        · subst right
          exact False.elim (htrue rfl)
        · simp [isReflexiveInequality, heq]

theorem HoldsAt.normalizeGeneratedHead_sound {D : Type}
    (model : TModel D) (assignment : Int → D) (source : FCL)
    (filtered : List FLit)
    (hnormalize : normalizeGeneratedHead source.head = some filtered)
    (hsource : HoldsAt model assignment source) :
    HoldsAt model assignment { source with head := filtered } := by
  cases hfilter : filterReflexiveHead source.head with
  | none => simp [normalizeGeneratedHead, hfilter] at hnormalize
  | some intermediate =>
      by_cases hcomplement : hasEqualityComplement intermediate = true
      · simp [normalizeGeneratedHead, hfilter, hcomplement] at hnormalize
      · have heq : intermediate = filtered := by
          simpa [normalizeGeneratedHead, hfilter, hcomplement] using hnormalize
        subst filtered
        exact HoldsAt.filterReflexiveHead_sound model assignment source
          intermediate hfilter hsource

structure FactorSignature where
  sourceIndex : Nat
  firstHeadIndex : Nat
  secondHeadIndex : Nat
deriving DecidableEq, Repr

def factorCandidate? (sourceIndex firstHeadIndex secondHeadIndex : Nat)
    (source : FCL) : Option (FactorSignature × FCL) := do
  if firstHeadIndex = secondHeadIndex then none else pure ()
  let .eq common first ← source.head[firstHeadIndex]? | none
  let .eq secondCommon second ← source.head[secondHeadIndex]? | none
  if secondCommon = common ∧ second ≠ first then
    let raw := factorConclusion source common first second
    let head ← normalizeGeneratedHead raw.head
    some ({ sourceIndex, firstHeadIndex, secondHeadIndex }, { raw with head })
  else none

def factorCandidates (retained : List FCL) : List (FactorSignature × FCL) :=
  (List.range retained.length).flatMap fun sourceIndex =>
    match retained[sourceIndex]? with
    | none => []
    | some source =>
        (List.range source.head.length).flatMap fun firstHeadIndex =>
          (List.range source.head.length).filterMap fun secondHeadIndex =>
            factorCandidate? sourceIndex firstHeadIndex secondHeadIndex source

theorem mem_factorCandidates_iff (retained : List FCL)
    (candidate : FactorSignature × FCL) :
    candidate ∈ factorCandidates retained ↔
      ∃ sourceIndex, sourceIndex < retained.length ∧
      ∃ source, retained[sourceIndex]? = some source ∧
      ∃ firstHeadIndex, firstHeadIndex < source.head.length ∧
      ∃ secondHeadIndex, secondHeadIndex < source.head.length ∧
        factorCandidate? sourceIndex firstHeadIndex secondHeadIndex source =
          some candidate := by
  simp only [factorCandidates, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨sourceIndex, hsourceIndex, hmember⟩
    cases hsource : retained[sourceIndex]? with
    | none => simp [hsource] at hmember
    | some source =>
        refine ⟨sourceIndex, hsourceIndex, source, hsource, ?_⟩
        simpa [hsource, List.mem_filterMap] using hmember
  · rintro ⟨sourceIndex, hsourceIndex, source, hsource, hmember⟩
    refine ⟨sourceIndex, hsourceIndex, ?_⟩
    simpa [hsource, List.mem_filterMap] using hmember

theorem factorCandidate_sound {D : Type}
    (model : TModel D) (assignment : Int → D)
    (source : FCL) (sourceIndex firstHeadIndex secondHeadIndex : Nat)
    (signature : FactorSignature) (conclusion : FCL)
    (hcandidate : factorCandidate? sourceIndex firstHeadIndex secondHeadIndex source =
      some (signature, conclusion))
    (hsource : HoldsAt model assignment source) :
    HoldsAt model assignment conclusion := by
  by_cases hsame : firstHeadIndex = secondHeadIndex
  · simp [factorCandidate?, hsame] at hcandidate
  · cases hfirst : source.head[firstHeadIndex]? with
    | none => simp [factorCandidate?, hsame, hfirst] at hcandidate
    | some firstLiteral =>
      cases firstLiteral with
      | P predicate => simp [factorCandidate?, hsame, hfirst] at hcandidate
      | ineq left right => simp [factorCandidate?, hsame, hfirst] at hcandidate
      | eq common first =>
        cases hsecond : source.head[secondHeadIndex]? with
        | none => simp [factorCandidate?, hsame, hfirst, hsecond] at hcandidate
        | some secondLiteral =>
          cases secondLiteral with
          | P predicate =>
              simp [factorCandidate?, hsame, hfirst, hsecond] at hcandidate
          | ineq left right =>
              simp [factorCandidate?, hsame, hfirst, hsecond] at hcandidate
          | eq secondCommon second =>
            by_cases hconditions : secondCommon = common ∧ second ≠ first
            · rcases hconditions with ⟨rfl, hdistinct⟩
              let raw := factorConclusion source secondCommon first second
              cases hnormal : normalizeGeneratedHead raw.head with
              | none =>
                  simp [factorCandidate?, hsame, hfirst, hsecond,
                    hdistinct, raw, hnormal] at hcandidate
              | some filtered =>
                  have hpair :
                      ({ sourceIndex, firstHeadIndex, secondHeadIndex },
                        { raw with head := filtered }) =
                        (signature, conclusion) := by
                    simpa [factorCandidate?, hsame, hfirst, hsecond,
                      hdistinct, raw, hnormal] using hcandidate
                  have hfirstMember : FLit.eq secondCommon first ∈ source.head := by
                    obtain ⟨hbound, hget⟩ :=
                      List.getElem?_eq_some_iff.mp hfirst
                    rw [← hget]
                    exact List.getElem_mem hbound
                  have hsecondMember : FLit.eq secondCommon second ∈ source.head := by
                    obtain ⟨hbound, hget⟩ :=
                      List.getElem?_eq_some_iff.mp hsecond
                    rw [← hget]
                    exact List.getElem_mem hbound
                  have hraw : HoldsAt model assignment raw :=
                    factorConclusion_sound model assignment source secondCommon first
                      second (Ne.symm hdistinct) hfirstMember hsecondMember hsource
                  have hfiltered : HoldsAt model assignment
                      { raw with head := filtered } :=
                    HoldsAt.normalizeGeneratedHead_sound model assignment raw
                      filtered hnormal hraw
                  have hconclusion : { raw with head := filtered } = conclusion :=
                    congrArg Prod.snd hpair
                  rw [← hconclusion]
                  exact hfiltered
            · simp [factorCandidate?, hsame, hfirst, hsecond,
                hconditions] at hcandidate

structure WireFactorCoverage where
  source_index : Nat
  first_head_index : Nat
  second_head_index : Nat
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedFactorCoverage
    (context : DecodedProductionContext bounds ontology) where
  sourceIndex : Fin context.retained.length
  firstHeadIndex : Fin (context.retained.get sourceIndex).head.length
  secondHeadIndex : Fin (context.retained.get sourceIndex).head.length
  signature : FactorSignature
  conclusion : FCL
  candidate_eq : factorCandidate? sourceIndex.val firstHeadIndex.val
    secondHeadIndex.val (context.retained.get sourceIndex) =
      some (signature, conclusion)
  strengtheningIndex : Fin context.retained.length
  strengthens : Strengthens (context.retained.get strengtheningIndex) conclusion

def WireFactorCoverage.decode
    (context : DecodedProductionContext bounds ontology)
    (wire : WireFactorCoverage) : Except String (DecodedFactorCoverage context) := do
  if hsource : wire.source_index < context.retained.length then
    let sourceIndex : Fin context.retained.length := ⟨wire.source_index, hsource⟩
    let source := context.retained.get sourceIndex
    if hfirst : wire.first_head_index < source.head.length then
      let firstHeadIndex : Fin source.head.length :=
        ⟨wire.first_head_index, hfirst⟩
      if hsecond : wire.second_head_index < source.head.length then
        let secondHeadIndex : Fin source.head.length :=
          ⟨wire.second_head_index, hsecond⟩
        match hcandidate : factorCandidate? wire.source_index
            wire.first_head_index wire.second_head_index source with
        | none => throw "claimed Factor tuple is not a production candidate"
        | some (signature, conclusion) =>
            if hstrengthening : wire.strengthening_retained < context.retained.length then
              let strengtheningIndex : Fin context.retained.length :=
                ⟨wire.strengthening_retained, hstrengthening⟩
              if hstrengthens : Strengthens
                  (context.retained.get strengtheningIndex) conclusion then
                return {
                  sourceIndex
                  firstHeadIndex
                  secondHeadIndex
                  signature
                  conclusion
                  candidate_eq := hcandidate
                  strengtheningIndex
                  strengthens := hstrengthens
                }
              else throw "retained clause does not strengthen Factor candidate"
            else throw "Factor strengthening index is outside retained clauses"
      else throw "Factor second head index is outside its source clause"
    else throw "Factor first head index is outside its source clause"
  else throw "Factor source index is outside retained clauses"

structure WireContextFactorClosure where
  context_index : Nat
  context_id : Nat
  generated : List WireFactorCoverage
deriving FromJson, ToJson

structure DecodedContextFactorClosure
    (localDoc : DecodedLocalResolutionClosureDocument) where
  contextIndex : Fin localDoc.terminal.sendCoverage.interContext.base.production.contexts.length
  contextId : Nat
  context_id_eq :
    (localDoc.terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex).contextId = contextId
  heads_normal : ∀ clause ∈
      (localDoc.terminal.sendCoverage.interContext.base.production.contexts.get
        contextIndex).retained,
      terminalHeadNormal clause.head = true
  generated : List (DecodedFactorCoverage
    (localDoc.terminal.sendCoverage.interContext.base.production.contexts.get contextIndex))
  candidates_exact : generated.map (fun coverage =>
      (coverage.signature, coverage.conclusion)) =
    factorCandidates
      (localDoc.terminal.sendCoverage.interContext.base.production.contexts.get
        contextIndex).retained

def WireContextFactorClosure.decode
    (localDoc : DecodedLocalResolutionClosureDocument)
    (wire : WireContextFactorClosure) :
    Except String (DecodedContextFactorClosure localDoc) := do
  let production := localDoc.terminal.sendCoverage.interContext.base.production
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length :=
      ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      if hnormal : ∀ clause ∈ context.retained,
          terminalHeadNormal clause.head = true then
        let generated ← wire.generated.mapM (WireFactorCoverage.decode context)
        let actual := generated.map fun coverage =>
          (coverage.signature, coverage.conclusion)
        let expected := factorCandidates context.retained
        if hexact : actual = expected then
          return {
            contextIndex
            contextId := wire.context_id
            context_id_eq := hid
            heads_normal := hnormal
            generated
            candidates_exact := hexact
          }
        else throw "Factor coverage omits, duplicates, or invents a candidate"
      else throw "terminal retained head still needs reflexive/complement simplification"
    else throw "Factor context id differs from production context"
  else throw "Factor context index is outside the production run"

structure WireLocalFactorClosureDocument where
  version : Nat
  local_resolution : WireLocalResolutionClosureDocument
  contexts : List WireContextFactorClosure
deriving FromJson, ToJson

structure DecodedLocalFactorClosureDocument where
  localResolution : DecodedLocalResolutionClosureDocument
  contexts : List (DecodedContextFactorClosure localResolution)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range localResolution.terminal.sendCoverage.interContext.base.production.contexts.length

def WireLocalFactorClosureDocument.decode (wire : WireLocalFactorClosureDocument) :
    Except String DecodedLocalFactorClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported local Factor-closure version {wire.version}"
  let localResolution ← wire.local_resolution.decode
  let contexts ← wire.contexts.mapM (WireContextFactorClosure.decode localResolution)
  let actual := contexts.map fun context => context.contextIndex.val
  let expected := List.range
    localResolution.terminal.sendCoverage.interContext.base.production.contexts.length
  if hexact : actual = expected then
    return { localResolution, contexts, context_indices_exact := hexact }
  else throw "Factor closure does not cover every context exactly once"

def WireLocalFactorClosureDocument.check
    (wire : WireLocalFactorClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireLocalFactorClosureDocument.check_sound
    (wire : WireLocalFactorClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLocalFactorClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (fun context => context.contextIndex.val) =
        List.range decoded.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length ∧
      ∀ context ∈ decoded.contexts,
        (∀ clause ∈
            (decoded.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained,
            terminalHeadNormal clause.head = true) ∧
        context.generated.map (fun coverage =>
          (coverage.signature, coverage.conclusion)) =
          factorCandidates
            (decoded.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained ∧
        ∀ coverage ∈ context.generated,
          Strengthens
            ((decoded.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained.get coverage.strengtheningIndex)
            coverage.conclusion := by
  cases hdecode : wire.decode with
  | error message => simp [WireLocalFactorClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      refine ⟨context.heads_normal, context.candidates_exact, ?_⟩
      intro coverage _
      exact coverage.strengthens

private def x : WireTerm := .var 0
private def y : WireTerm := .var (-1)
private def z : WireTerm := .var (-2)
private def a : WireTerm := .var (-3)
private def b : WireTerm := .var (-4)
private def marker : WireLiteral := .equality a b
private def eqxy : WireLiteral := .equality x y
private def eqxz : WireLiteral := .equality x z
private def ineqyz : WireLiteral := .inequality y z
private def ineqzy : WireLiteral := .inequality z y

private def factorPremise : WireClause :=
  ⟨[marker], [marker, eqxy, eqxz]⟩
private def factorResultYZ : WireClause :=
  ⟨[marker], [marker, eqxz, ineqyz]⟩
private def factorResultZY : WireClause :=
  ⟨[marker], [marker, eqxy, ineqzy]⟩

private def factorTerminal :=
  let terminal := CBTerminalStateWire.acceptedExample
  let send := terminal.send_coverage
  let inter := send.inter_context
  let production := inter.production
  let contexts := production.contexts.map fun context =>
    { context with
      retained := context.retained ++ [factorPremise, factorResultYZ, factorResultZY]
      trace := context.trace ++
        [⟨factorPremise, .tautology⟩,
         ⟨factorResultYZ, .factor 1 x y z⟩,
         ⟨factorResultZY, .factor 1 x z y⟩] }
  { terminal with send_coverage := { send with inter_context :=
      { inter with production := { production with contexts } } } }

private def localGenerated : List WireResolutionCoverage :=
  (List.range 3).flatMap fun positive =>
    (List.range 3).map fun negative => {
      positive_index := positive + 1
      negative_index := negative + 1
      literal := marker
      strengthening_retained := positive + 1
    }

private def localDocument : WireLocalResolutionClosureDocument where
  version := 1
  terminal := factorTerminal
  contexts := [{ context_index := 0, context_id := 7, generated := localGenerated }]

private def factorGenerated : List WireFactorCoverage := [{
  source_index := 1
  first_head_index := 1
  second_head_index := 2
  strengthening_retained := 2
}, {
  source_index := 1
  first_head_index := 2
  second_head_index := 1
  strengthening_retained := 3
}]

def acceptedExample : WireLocalFactorClosureDocument where
  version := 1
  local_resolution := localDocument
  contexts := [{
    context_index := 0
    context_id := 7
    generated := factorGenerated
  }]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example : rejected ({ acceptedExample with contexts := [{
    context_index := 0
    context_id := 7
    generated := factorGenerated.drop 1
  }] }).check = true := by native_decide

example : filterReflexiveHead [.ineq (.var 0) (.var 0), .eq (.var 0) (.var 1)] =
    some [.eq (.var 0) (.var 1)] := by native_decide

example : normalizeGeneratedHead
    [.eq (.var 0) (.var 1), .ineq (.var 0) (.var 1)] = none := by native_decide

example : terminalHeadNormal [.ineq (.var 0) (.var 0)] = false := by
  native_decide

example : terminalHeadNormal
    [.eq (.var 0) (.var 1), .ineq (.var 0) (.var 1)] = false := by
  native_decide

#print axioms WireLocalFactorClosureDocument.check_sound
#print axioms HoldsAt.normalizeGeneratedHead_sound
#print axioms factorCandidate_sound
#print axioms mem_factorCandidates_iff

end ContextCalculus.CBLocalFactorClosureWire
