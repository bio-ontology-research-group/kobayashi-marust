import ContextCalculus.CBSourceSuccClosure
import ContextCalculus.CBLocalEqEnumeration

/-!
# Source-bound equality closure

This checker reconstructs the complete direct-position ordered-paramodulation
candidate set from each terminal context. It uses the same source-bound term
order and root/non-root partial literal order as production Hyper, then requires
a retained strengthening for every non-tautological normalized conclusion.
-/

namespace ContextCalculus.CBSourceEqClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceSuccClosure
open ContextCalculus.CBLocalEqEnumeration
open ContextCalculus.CBLocalFactorClosureWire

def orderedPair (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) : FTerm × FTerm :=
  if order.termLe right left then (left, right) else (right, left)

def orderedEq (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) : FLit :=
  let pair := orderedPair order left right
  .eq pair.1 pair.2

def orderedIneq (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) : FLit :=
  let pair := orderedPair order left right
  .ineq pair.1 pair.2

/-- KM's first eligible direct-position rewrite, using the source-bound term
order to orient rewritten equalities and inequalities. -/
def directRewrite (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) : FLit → Option FLit
  | .P (.concept concept argument) =>
      if argument = left then some (.P (.concept concept right)) else none
  | .P (.role role source target) =>
      if source = left then some (.P (.role role right target))
      else if target = left then some (.P (.role role source right)) else none
  | .eq source target =>
      if source = left then some (orderedEq order right target) else none
  | .ineq source target =>
      if source = left then some (orderedIneq order right target) else none

theorem eval_orderedEq_iff {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) :
    model.evalL assignment (orderedEq order left right) ↔
      model.evalT assignment left = model.evalT assignment right := by
  simp only [orderedEq, orderedPair]
  split
  · rfl
  · simp only [TModel.evalL, eq_comm]

theorem eval_orderedIneq_iff {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) :
    model.evalL assignment (orderedIneq order left right) ↔
      model.evalT assignment left ≠ model.evalT assignment right := by
  simp only [orderedIneq, orderedPair]
  split
  · rfl
  · simp only [TModel.evalL, ne_comm]

theorem eval_directRewrite_iff {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (left right : FTerm) (literal rewritten : FLit)
    (hequal : model.evalT assignment left = model.evalT assignment right)
    (hrewrite : directRewrite order left right literal = some rewritten) :
    model.evalL assignment rewritten ↔ model.evalL assignment literal := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept argument =>
          by_cases harg : argument = left
          · rw [harg] at hrewrite ⊢
            simp only [directRewrite, ↓reduceIte, Option.some.injEq] at hrewrite
            subst rewritten
            simp only [TModel.evalL, hequal]
          · simp [directRewrite, harg] at hrewrite
      | role role source target =>
          by_cases hsource : source = left
          · rw [hsource] at hrewrite ⊢
            simp only [directRewrite, ↓reduceIte, Option.some.injEq] at hrewrite
            subst rewritten
            simp only [TModel.evalL, hequal]
          · by_cases htarget : target = left
            · rw [htarget] at hrewrite ⊢
              simp [directRewrite, hsource] at hrewrite
              subst rewritten
              simp only [TModel.evalL, hequal]
            · simp [directRewrite, hsource, htarget] at hrewrite
  | eq source target =>
      by_cases hsource : source = left
      · rw [hsource] at hrewrite ⊢
        simp only [directRewrite, ↓reduceIte, Option.some.injEq] at hrewrite
        subst rewritten
        rw [eval_orderedEq_iff]
        simp only [TModel.evalL, hequal]
      · simp [directRewrite, hsource] at hrewrite
  | ineq source target =>
      by_cases hsource : source = left
      · rw [hsource] at hrewrite ⊢
        simp only [directRewrite, ↓reduceIte, Option.some.injEq] at hrewrite
        subst rewritten
        rw [eval_orderedIneq_iff]
        simp only [TModel.evalL, hequal]
      · simp [directRewrite, hsource] at hrewrite

theorem directParamodulant_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedSourceFiniteOrder production)
    (targetClause equalityClause : FCL) (left right : FTerm)
    (target equality rewritten : FLit)
    (hequalityLiteral : equality = .eq left right)
    (hrewrite : directRewrite order left right target = some rewritten)
    (htargetValid : HoldsAt model assignment targetClause)
    (hequalityValid : HoldsAt model assignment equalityClause) :
    HoldsAt model assignment
      (CBLocalEqEnumeration.directParamodulant targetClause equalityClause
        target equality rewritten) := by
  intro hbody
  have htargetBody : ∀ literal ∈ targetClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [CBLocalEqEnumeration.directParamodulant, hliteral])
  have hequalityBody : ∀ literal ∈ equalityClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [CBLocalEqEnumeration.directParamodulant, hliteral])
  obtain ⟨eqHead, heqHead, heqTrue⟩ := hequalityValid hequalityBody
  by_cases heqChosen : eqHead = equality
  · subst eqHead
    subst equality
    simp only [TModel.evalL] at heqTrue
    obtain ⟨targetHead, htargetHead, htargetTrue⟩ := htargetValid htargetBody
    by_cases htargetChosen : targetHead = target
    · subst targetHead
      refine ⟨rewritten, by
        simp [CBLocalEqEnumeration.directParamodulant], ?_⟩
      exact (eval_directRewrite_iff model assignment order left right target
        rewritten heqTrue hrewrite).mpr htargetTrue
    · exact ⟨targetHead, by
        simp [CBLocalEqEnumeration.directParamodulant, mem_without,
          htargetHead, htargetChosen], htargetTrue⟩
  · exact ⟨eqHead, by
      simp [CBLocalEqEnumeration.directParamodulant, mem_without,
        heqHead, heqChosen], heqTrue⟩

def candidateAt? (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL)
    (equalityIndex equalityHeadIndex targetIndex targetHeadIndex : Nat) :
    Option EqCandidate := do
  let equalityClause ← retained[equalityIndex]?
  let targetClause ← retained[targetIndex]?
  if equalityHeadIndex ∈ order.maximalHeadIndices root equalityClause.head then
    pure () else none
  if targetHeadIndex ∈ order.maximalHeadIndices root targetClause.head then
    pure () else none
  let equality ← equalityClause.head[equalityHeadIndex]?
  let .eq left right := equality | none
  let target ← targetClause.head[targetHeadIndex]?
  if target = equality then none else pure ()
  let rewritten ← directRewrite order left right target
  if productionCase left right target then pure () else none
  let raw := CBLocalEqEnumeration.directParamodulant targetClause equalityClause
    target equality rewritten
  let head ← normalizeGeneratedHead raw.head
  some {
    signature := { equalityIndex, equalityHeadIndex, targetIndex, targetHeadIndex }
    left, right, equality, target, rewritten
    conclusion := { raw with head }
  }

def signatures (retained : List FCL) : List EqSignature :=
  (List.range retained.length).flatMap fun equalityIndex =>
    match retained[equalityIndex]? with
    | none => []
    | some equalityClause =>
      (List.range equalityClause.head.length).flatMap fun equalityHeadIndex =>
        (List.range retained.length).flatMap fun targetIndex =>
          match retained[targetIndex]? with
          | none => []
          | some targetClause =>
            (List.range targetClause.head.length).map fun targetHeadIndex =>
              { equalityIndex, equalityHeadIndex, targetIndex, targetHeadIndex }

def candidates (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) : List EqCandidate :=
  (signatures retained).filterMap fun signature =>
    candidateAt? order root retained signature.equalityIndex
      signature.equalityHeadIndex signature.targetIndex signature.targetHeadIndex

theorem mem_candidates_has_checked_origin
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (retained : List FCL) (candidate : EqCandidate)
    (hmember : candidate ∈ candidates order root retained) :
    ∃ signature ∈ signatures retained,
      candidateAt? order root retained signature.equalityIndex
        signature.equalityHeadIndex signature.targetIndex
        signature.targetHeadIndex = some candidate := by
  simp only [candidates, List.mem_filterMap] at hmember
  obtain ⟨signature, hsignature, hcandidate⟩ := hmember
  cases hresult : candidateAt? order root retained signature.equalityIndex
      signature.equalityHeadIndex signature.targetIndex signature.targetHeadIndex with
  | none => simp [hresult] at hcandidate
  | some conclusion =>
      simp only [hresult, Option.some.injEq] at hcandidate
      subst conclusion
      exact ⟨signature, hsignature, hresult⟩

def sourceEqClosedB (order : DecodedSourceFiniteOrder production)
    (context : DecodedSourceLiveContext production ordinary rootArena) : Bool :=
  (candidates order context.rootDomain context.retained).all fun candidate =>
    context.retained.any fun retained => decide (Strengthens retained candidate.conclusion)

theorem sourceEqClosedB_sound
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedSourceLiveContext production ordinary rootArena)
    (hclosed : sourceEqClosedB order context = true) :
    ∀ candidate ∈ candidates order context.rootDomain context.retained,
      ∃ retained ∈ context.retained,
        Strengthens retained candidate.conclusion := by
  intro candidate hcandidate
  have hany := List.all_eq_true.mp hclosed candidate hcandidate
  simpa only [List.any_eq_true, decide_eq_true_eq] using hany

structure WireSourceEqClosureDocument where
  version : Nat
  succ_closure : WireSourceSuccClosureDocument
deriving FromJson, ToJson

structure DecodedSourceEqClosureDocument where
  succClosure : DecodedSourceSuccClosureDocument
  eq_closed : ∀ context ∈
      succClosure.join3Closure.hyperClosure.localClosure.live.contexts,
    sourceEqClosedB succClosure.join3Closure.hyperClosure.order context = true

def WireSourceEqClosureDocument.decode (wire : WireSourceEqClosureDocument) :
    Except String DecodedSourceEqClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB Eq-closure version {wire.version}"
  let succClosure ← wire.succ_closure.decode
  let live := succClosure.join3Closure.hyperClosure.localClosure.live
  if hclosed : ∀ context ∈ live.contexts,
      sourceEqClosedB succClosure.join3Closure.hyperClosure.order context = true then
    return { succClosure, eq_closed := hclosed }
  else throw "source-bound CB terminal state is not Eq-closed"

def WireSourceEqClosureDocument.check (wire : WireSourceEqClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireSourceEqClosureDocument.check_sound
    (wire : WireSourceEqClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceEqClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈
          decoded.succClosure.join3Closure.hyperClosure.localClosure.live.contexts,
        ∀ candidate ∈ candidates
            decoded.succClosure.join3Closure.hyperClosure.order
            context.rootDomain context.retained,
          ∃ retained ∈ context.retained,
            Strengthens retained candidate.conclusion := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceEqClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro context hcontext
      exact sourceEqClosedB_sound
        decoded.succClosure.join3Closure.hyperClosure.order context
        (decoded.eq_closed context hcontext)

#print axioms eval_directRewrite_iff
#print axioms directParamodulant_sound
#print axioms mem_candidates_has_checked_origin
#print axioms WireSourceEqClosureDocument.check_sound

end ContextCalculus.CBSourceEqClosure
