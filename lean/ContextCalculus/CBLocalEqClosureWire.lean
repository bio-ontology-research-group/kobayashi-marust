import ContextCalculus.CBLocalEqEnumeration

/-!
# Exact local Eq closure wire

For every terminal context, this checker independently reconstructs the union
of KM's two Eq candidate paths under the checked finite term and literal
orders. Every non-tautological candidate must have a retained syntactic
strengthening. Serialized data supplies indexes only; Lean recomputes maxima,
the direct rewrite, filtering, and the complete candidate list.
-/

namespace ContextCalculus.CBLocalEqClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBLocalEqEnumeration
open ContextCalculus.CBLocalFactorClosureWire

structure WireEqCoverage where
  equality_index : Nat
  equality_head_index : Nat
  target_index : Nat
  target_head_index : Nat
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedEqCoverage
    (literalOrder : DecodedFiniteLiteralOrderDocument)
    (context : DecodedProductionContext bounds ontology) where
  equalityIndex : Fin context.retained.length
  equalityHeadIndex : Fin (context.retained.get equalityIndex).head.length
  targetIndex : Fin context.retained.length
  targetHeadIndex : Fin (context.retained.get targetIndex).head.length
  equality_maximal : equalityHeadIndex.val ∈
    literalOrder.maximalHeadIndices (context.retained.get equalityIndex).head
  target_maximal : targetHeadIndex.val ∈
    literalOrder.maximalHeadIndices (context.retained.get targetIndex).head
  left : FTerm
  right : FTerm
  equality_eq : (context.retained.get equalityIndex).head.get equalityHeadIndex =
    .eq left right
  target : FLit
  target_eq : (context.retained.get targetIndex).head.get targetHeadIndex = target
  target_ne_equality : target ≠ .eq left right
  rewritten : FLit
  rewrite_eq : directRewrite literalOrder.termOrder left right target = some rewritten
  production_case : productionCase left right target = true
  raw : FCL
  raw_eq : raw = directParamodulant
    (context.retained.get targetIndex) (context.retained.get equalityIndex)
    target (.eq left right) rewritten
  conclusion : FCL
  normalize_eq : normalizeGeneratedHead raw.head = some conclusion.head
  conclusion_body_eq : conclusion.body = raw.body
  candidate : EqCandidate
  candidate_eq : candidate = {
    signature := {
      equalityIndex := equalityIndex.val
      equalityHeadIndex := equalityHeadIndex.val
      targetIndex := targetIndex.val
      targetHeadIndex := targetHeadIndex.val }
    left, right, equality := .eq left right, target, rewritten, conclusion }
  strengtheningIndex : Fin context.retained.length
  strengthens : Strengthens (context.retained.get strengtheningIndex) conclusion

def DecodedEqCoverage.signature
    (coverage : DecodedEqCoverage literalOrder context) : EqSignature :=
  coverage.candidate.signature

def WireEqCoverage.decode (literalOrder : DecodedFiniteLiteralOrderDocument)
    (context : DecodedProductionContext bounds ontology) (wire : WireEqCoverage) :
    Except String (DecodedEqCoverage literalOrder context) := do
  if hequality : wire.equality_index < context.retained.length then
    let equalityIndex : Fin context.retained.length :=
      ⟨wire.equality_index, hequality⟩
    let equalityClause := context.retained.get equalityIndex
    if hequalityHead : wire.equality_head_index < equalityClause.head.length then
      let equalityHeadIndex : Fin equalityClause.head.length :=
        ⟨wire.equality_head_index, hequalityHead⟩
      if hequalityMax : equalityHeadIndex.val ∈
          literalOrder.maximalHeadIndices equalityClause.head then
        match hequalityLiteral : equalityClause.head.get equalityHeadIndex with
        | .eq left right =>
          if htarget : wire.target_index < context.retained.length then
            let targetIndex : Fin context.retained.length :=
              ⟨wire.target_index, htarget⟩
            let targetClause := context.retained.get targetIndex
            if htargetHead : wire.target_head_index < targetClause.head.length then
              let targetHeadIndex : Fin targetClause.head.length :=
                ⟨wire.target_head_index, htargetHead⟩
              if htargetMax : targetHeadIndex.val ∈
                  literalOrder.maximalHeadIndices targetClause.head then
                let targetLiteral := targetClause.head.get targetHeadIndex
                if hdistinct : targetLiteral ≠ .eq left right then
                  match hrewrite : directRewrite literalOrder.termOrder left right
                      targetLiteral with
                  | none => throw "Eq target is not rewritable by the selected equality"
                  | some rewritten =>
                    if hcase : productionCase left right targetLiteral = true then
                      let raw := directParamodulant targetClause equalityClause
                        targetLiteral (.eq left right) rewritten
                      match hnormalize : normalizeGeneratedHead raw.head with
                      | none => throw "Eq candidate is tautological and must not be serialized"
                      | some head =>
                        let conclusion : FCL := ⟨raw.body, head⟩
                        let candidate : EqCandidate := {
                          signature := {
                            equalityIndex := equalityIndex.val
                            equalityHeadIndex := equalityHeadIndex.val
                            targetIndex := targetIndex.val
                            targetHeadIndex := targetHeadIndex.val }
                          left, right, equality := .eq left right
                          target := targetLiteral, rewritten, conclusion }
                        if hstrengthening : wire.strengthening_retained <
                            context.retained.length then
                          let strengtheningIndex : Fin context.retained.length :=
                            ⟨wire.strengthening_retained, hstrengthening⟩
                          if hstrengthens : Strengthens
                              (context.retained.get strengtheningIndex) conclusion then
                            return {
                              equalityIndex, equalityHeadIndex
                              targetIndex, targetHeadIndex
                              equality_maximal := hequalityMax
                              target_maximal := htargetMax
                              left, right, equality_eq := hequalityLiteral
                              target := targetLiteral, target_eq := rfl
                              target_ne_equality := hdistinct
                              rewritten, rewrite_eq := hrewrite
                              production_case := hcase
                              raw, raw_eq := rfl
                              conclusion, normalize_eq := hnormalize
                              conclusion_body_eq := rfl
                              candidate, candidate_eq := rfl
                              strengtheningIndex, strengthens := hstrengthens }
                          else throw "retained clause does not strengthen Eq candidate"
                        else throw "Eq strengthening index is outside retained clauses"
                    else throw "Eq candidate violates a production suppression condition"
                else throw "Eq target is the selected equality literal"
              else throw "Eq target literal is not maximal"
            else throw "Eq target head index is outside its clause"
          else throw "Eq target clause index is outside retained clauses"
        | _ => throw "Eq provider literal is not an equality"
      else throw "Eq provider equality is not maximal"
    else throw "Eq provider head index is outside its clause"
  else throw "Eq provider clause index is outside retained clauses"

theorem DecodedEqCoverage.conclusion_sound {D : Type}
    (coverage : DecodedEqCoverage literalOrder context)
    (model : TModel D) (assignment : Int → D)
    (htarget : HoldsAt model assignment
      (context.retained.get coverage.targetIndex))
    (hequality : HoldsAt model assignment
      (context.retained.get coverage.equalityIndex)) :
    HoldsAt model assignment coverage.conclusion := by
  have hraw : HoldsAt model assignment coverage.raw := by
    rw [coverage.raw_eq]
    exact directParamodulant_sound model assignment literalOrder.termOrder
      (context.retained.get coverage.targetIndex)
      (context.retained.get coverage.equalityIndex)
      coverage.left coverage.right coverage.target (.eq coverage.left coverage.right)
      coverage.rewritten rfl coverage.rewrite_eq htarget hequality
  have hnormalized : HoldsAt model assignment
      { coverage.raw with head := coverage.conclusion.head } :=
    HoldsAt.normalizeGeneratedHead_sound model assignment coverage.raw
      coverage.conclusion.head coverage.normalize_eq hraw
  have heq : { coverage.raw with head := coverage.conclusion.head } =
      coverage.conclusion := by
    have hbody := coverage.conclusion_body_eq
    cases hrawStruct : coverage.raw with
    | mk rawBody rawHead =>
      cases hconclusionStruct : coverage.conclusion with
      | mk conclusionBody conclusionHead =>
        simp only [hrawStruct, hconclusionStruct] at hbody ⊢
        rw [hbody]
  rwa [← heq]

structure WireContextEqClosure where
  context_index : Nat
  context_id : Nat
  generated : List WireEqCoverage
deriving FromJson, ToJson

def productionContexts (literalOrder : DecodedFiniteLiteralOrderDocument) :=
  literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts

structure DecodedContextEqClosure
    (literalOrder : DecodedFiniteLiteralOrderDocument) where
  contextIndex : Fin (productionContexts literalOrder).length
  contextId : Nat
  context_id_eq :
    ((productionContexts literalOrder).get contextIndex).contextId = contextId
  generated : List (DecodedEqCoverage literalOrder
    ((productionContexts literalOrder).get contextIndex))
  candidates_exact : generated.map (fun coverage => coverage.candidate) =
    eqCandidates literalOrder
      ((productionContexts literalOrder).get contextIndex).retained

theorem DecodedContextEqClosure.generated_sound {D : Type}
    (contextClosure : DecodedContextEqClosure literalOrder)
    (model : TModel D) (assignment : Int → D)
    (hretained : ∀ clause ∈
      ((productionContexts literalOrder).get contextClosure.contextIndex).retained,
      HoldsAt model assignment clause) :
    ∀ coverage ∈ contextClosure.generated,
      HoldsAt model assignment coverage.conclusion := by
  intro coverage _
  apply coverage.conclusion_sound model assignment
  · apply hretained
    exact List.get_mem _ _
  · apply hretained
    exact List.get_mem _ _

def WireContextEqClosure.decode (literalOrder : DecodedFiniteLiteralOrderDocument)
    (wire : WireContextEqClosure) : Except String (DecodedContextEqClosure literalOrder) := do
  let contexts := productionContexts literalOrder
  if hcontext : wire.context_index < contexts.length then
    let contextIndex : Fin contexts.length := ⟨wire.context_index, hcontext⟩
    let context := contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      let generated ← wire.generated.mapM (WireEqCoverage.decode literalOrder context)
      let actual := generated.map fun coverage => coverage.candidate
      let expected := eqCandidates literalOrder context.retained
      if hexact : actual = expected then
        return {
          contextIndex := contextIndex
          contextId := wire.context_id
          context_id_eq := hid
          generated := generated
          candidates_exact := hexact }
      else throw "Eq coverage omits, duplicates, or invents a candidate"
    else throw "Eq context id differs from production context"
  else throw "Eq context index is outside the production run"

structure WireLocalEqClosureDocument where
  version : Nat
  literal_order : WireFiniteLiteralOrderDocument
  contexts : List WireContextEqClosure
deriving FromJson, ToJson

structure DecodedLocalEqClosureDocument where
  literalOrder : DecodedFiniteLiteralOrderDocument
  contexts : List (DecodedContextEqClosure literalOrder)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range (productionContexts literalOrder).length

def WireLocalEqClosureDocument.decode (wire : WireLocalEqClosureDocument) :
    Except String DecodedLocalEqClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported local Eq-closure version {wire.version}"
  let literalOrder ← wire.literal_order.decode
  let contexts ← wire.contexts.mapM (WireContextEqClosure.decode literalOrder)
  let actual := contexts.map fun context => context.contextIndex.val
  let expected := List.range (productionContexts literalOrder).length
  if hexact : actual = expected then
    return { literalOrder, contexts, context_indices_exact := hexact }
  else throw "Eq closure does not cover every context exactly once"

def WireLocalEqClosureDocument.check (wire : WireLocalEqClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireLocalEqClosureDocument.check_sound
    (wire : WireLocalEqClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLocalEqClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (fun context => context.contextIndex.val) =
        List.range (productionContexts decoded.literalOrder).length ∧
      ∀ context ∈ decoded.contexts,
        context.generated.map (fun coverage => coverage.candidate) =
          eqCandidates decoded.literalOrder
            ((productionContexts decoded.literalOrder).get
              context.contextIndex).retained ∧
        ∀ coverage ∈ context.generated,
          Strengthens
            (((productionContexts decoded.literalOrder).get
              context.contextIndex).retained.get coverage.strengtheningIndex)
            coverage.conclusion := by
  cases hdecode : wire.decode with
  | error message => simp [WireLocalEqClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      refine ⟨context.candidates_exact, ?_⟩
      intro coverage _
      exact coverage.strengthens

#print axioms DecodedEqCoverage.conclusion_sound
#print axioms DecodedContextEqClosure.generated_sound
#print axioms WireLocalEqClosureDocument.check_sound

end ContextCalculus.CBLocalEqClosureWire
