import ContextCalculus.CBFiniteLiteralOrderWire

/-!
# Exact local Eq candidate enumeration

This module specifies the terminal-state union of KM's `eq_from_pred` and
`eq_from_equation` scans.  Unlike the generic checker paramodulation operation,
KM rewrites one designated direct literal argument, not every recursive
occurrence of a decoded nested term.  The operation below mirrors that choice
and reorients equality literals with the checked finite term order.
-/

namespace ContextCalculus.CBLocalEqEnumeration

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteLiteralOrderWire

def orderedPair (order : DecodedFiniteTermOrderDocument) (left right : FTerm) :
    FTerm × FTerm :=
  if order.rank right ≤ order.rank left then (left, right) else (right, left)

def orderedEq (order : DecodedFiniteTermOrderDocument) (left right : FTerm) : FLit :=
  let pair := orderedPair order left right
  .eq pair.1 pair.2

def orderedIneq (order : DecodedFiniteTermOrderDocument) (left right : FTerm) : FLit :=
  let pair := orderedPair order left right
  .ineq pair.1 pair.2

/-- KM's `Lit::contains_at_rewrite_position`. -/
def containsAtRewritePosition (literal : FLit) (term : FTerm) : Bool :=
  match literal with
  | .P (.concept _ argument) => decide (argument = term)
  | .P (.role _ source target) => decide (source = term ∨ target = term)
  | .eq left _ | .ineq left _ => decide (left = term)

/-- KM's `Lit::rewrite`: rewrite the first eligible direct position. -/
def directRewrite (order : DecodedFiniteTermOrderDocument)
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

def productionCase (left right : FTerm) : FLit → Bool
  | .eq source other => decide ¬(source = left ∧ right = other)
  | .ineq source other => decide (source = left ∧ right ≠ other)
  | .P _ => true

/-- The exact result of KM's production Eq rewrite.  An outer `none` means
the production branch is suppressed.  `some none` is the special
equality--disequality cancellation branch: rewriting `s != t` with `s = t`
removes the selected disequality instead of retaining the reflexive literal
`t != t`. -/
def productionRewrite (order : DecodedFiniteTermOrderDocument)
    (left right : FTerm) : FLit → Option (Option FLit)
  | .P predicate => (directRewrite order left right (.P predicate)).map some
  | .eq source other =>
      if source = left then
        if right = other then none else some (some (orderedEq order right other))
      else none
  | .ineq source other =>
      if source = left then
        if right = other then some none
        else some (some (orderedIneq order right other))
      else none

theorem eval_orderedEq_iff {D : Type} (model : TModel D) (assignment : Int → D)
    (order : DecodedFiniteTermOrderDocument) (left right : FTerm) :
    model.evalL assignment (orderedEq order left right) ↔
      model.evalT assignment left = model.evalT assignment right := by
  simp only [orderedEq, orderedPair]
  split
  · rfl
  · simp only [TModel.evalL, eq_comm]

theorem eval_orderedIneq_iff {D : Type} (model : TModel D) (assignment : Int → D)
    (order : DecodedFiniteTermOrderDocument) (left right : FTerm) :
    model.evalL assignment (orderedIneq order left right) ↔
      model.evalT assignment left ≠ model.evalT assignment right := by
  simp only [orderedIneq, orderedPair]
  split
  · rfl
  · simp only [TModel.evalL, ne_comm]

theorem eval_directRewrite_iff {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedFiniteTermOrderDocument)
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

def directParamodulant (targetClause equalityClause : FCL)
    (target equality rewritten : FLit) : FCL :=
  ⟨targetClause.body ++ equalityClause.body,
    rewritten :: (without target targetClause.head ++
      without equality equalityClause.head)⟩

theorem directParamodulant_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedFiniteTermOrderDocument)
    (targetClause equalityClause : FCL) (left right : FTerm)
    (target equality rewritten : FLit)
    (hequalityLiteral : equality = .eq left right)
    (hrewrite : directRewrite order left right target = some rewritten)
    (htargetValid : CBProductionTrace.HoldsAt model assignment targetClause)
    (hequalityValid : CBProductionTrace.HoldsAt model assignment equalityClause) :
    CBProductionTrace.HoldsAt model assignment
      (directParamodulant targetClause equalityClause target equality rewritten) := by
  intro hbody
  have htargetBody : ∀ literal ∈ targetClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [directParamodulant, hliteral])
  have hequalityBody : ∀ literal ∈ equalityClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [directParamodulant, hliteral])
  obtain ⟨eqHead, heqHead, heqTrue⟩ := hequalityValid hequalityBody
  by_cases heqChosen : eqHead = equality
  · subst eqHead
    subst equality
    simp only [TModel.evalL] at heqTrue
    obtain ⟨targetHead, htargetHead, htargetTrue⟩ := htargetValid htargetBody
    by_cases htargetChosen : targetHead = target
    · subst targetHead
      refine ⟨rewritten, by simp [directParamodulant], ?_⟩
      exact (eval_directRewrite_iff model assignment order left right target
        rewritten heqTrue hrewrite).mpr htargetTrue
    · exact ⟨targetHead, by
        simp [directParamodulant, mem_without, htargetHead, htargetChosen],
        htargetTrue⟩
  · exact ⟨eqHead, by
      simp [directParamodulant, mem_without, heqHead, heqChosen], heqTrue⟩

def productionParamodulant (targetClause equalityClause : FCL)
    (target equality : FLit) (rewritten : Option FLit) : FCL :=
  ⟨targetClause.body ++ equalityClause.body,
    rewritten.toList ++ (without target targetClause.head ++
      without equality equalityClause.head)⟩

/-- Regression for KM's equality--disequality cancellation branch. -/
theorem productionRewrite_ineq_cancels
    (order : DecodedFiniteTermOrderDocument) (left right : FTerm) :
    productionRewrite order left right (.ineq left right) = some none := by
  simp [productionRewrite]

theorem unit_eq_ineq_productionParamodulant_is_bottom
    (left right : FTerm) :
    productionParamodulant ⟨[], [.ineq left right]⟩
      ⟨[], [.eq left right]⟩ (.ineq left right) (.eq left right) none =
      ⟨[], []⟩ := by
  simp [productionParamodulant, without]

theorem productionParamodulant_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedFiniteTermOrderDocument)
    (targetClause equalityClause : FCL) (left right : FTerm)
    (target equality : FLit) (rewritten : Option FLit)
    (hequalityLiteral : equality = .eq left right)
    (hrewrite : productionRewrite order left right target = some rewritten)
    (htargetValid : CBProductionTrace.HoldsAt model assignment targetClause)
    (hequalityValid : CBProductionTrace.HoldsAt model assignment equalityClause) :
    CBProductionTrace.HoldsAt model assignment
      (productionParamodulant targetClause equalityClause target equality rewritten) := by
  intro hbody
  have htargetBody : ∀ literal ∈ targetClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [productionParamodulant, hliteral])
  have hequalityBody : ∀ literal ∈ equalityClause.body,
      model.evalL assignment literal := fun literal hliteral =>
    hbody literal (by simp [productionParamodulant, hliteral])
  obtain ⟨eqHead, heqHead, heqTrue⟩ := hequalityValid hequalityBody
  by_cases heqChosen : eqHead = equality
  · subst eqHead
    subst equality
    simp only [TModel.evalL] at heqTrue
    obtain ⟨targetHead, htargetHead, htargetTrue⟩ := htargetValid htargetBody
    by_cases htargetChosen : targetHead = target
    · subst targetHead
      cases target with
      | P predicate =>
          simp only [productionRewrite] at hrewrite
          cases hdirect : directRewrite order left right (.P predicate) with
          | none => simp [hdirect] at hrewrite
          | some literal =>
              simp [hdirect] at hrewrite
              subst rewritten
              refine ⟨literal, by simp [productionParamodulant], ?_⟩
              exact (eval_directRewrite_iff model assignment order left right
                (.P predicate) literal heqTrue hdirect).mpr htargetTrue
      | eq source other =>
          by_cases hsource : source = left
          · subst source
            by_cases hother : right = other
            · simp [productionRewrite, hother] at hrewrite
            · simp [productionRewrite, hother] at hrewrite
              subst rewritten
              refine ⟨orderedEq order right other,
                by simp [productionParamodulant], ?_⟩
              rw [eval_orderedEq_iff]
              simpa only [TModel.evalL, heqTrue] using htargetTrue
          · simp [productionRewrite, hsource] at hrewrite
      | ineq source other =>
          by_cases hsource : source = left
          · subst source
            by_cases hother : right = other
            · subst other
              simp [productionRewrite] at hrewrite
              subst rewritten
              exact (htargetTrue heqTrue).elim
            · simp [productionRewrite, hother] at hrewrite
              subst rewritten
              refine ⟨orderedIneq order right other,
                by simp [productionParamodulant], ?_⟩
              rw [eval_orderedIneq_iff]
              simpa only [TModel.evalL, heqTrue] using htargetTrue
          · simp [productionRewrite, hsource] at hrewrite
    · exact ⟨targetHead, by
        simp [productionParamodulant, mem_without, htargetHead, htargetChosen],
        htargetTrue⟩
  · exact ⟨eqHead, by
      simp [productionParamodulant, mem_without, heqHead, heqChosen], heqTrue⟩

structure EqSignature where
  equalityIndex : Nat
  equalityHeadIndex : Nat
  targetIndex : Nat
  targetHeadIndex : Nat
deriving DecidableEq, Repr

structure EqCandidate where
  signature : EqSignature
  left : FTerm
  right : FTerm
  equality : FLit
  target : FLit
  rewritten : Option FLit
  conclusion : FCL
deriving DecidableEq, Repr

def eqCandidate? (literalOrder : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) (equalityIndex equalityHeadIndex targetIndex
      targetHeadIndex : Nat) : Option EqCandidate := do
  let equalityClause ← retained[equalityIndex]?
  let targetClause ← retained[targetIndex]?
  if equalityHeadIndex ∈ literalOrder.maximalHeadIndices equalityClause.head then
    pure () else none
  if targetHeadIndex ∈ literalOrder.maximalHeadIndices targetClause.head then
    pure () else none
  let equality ← equalityClause.head[equalityHeadIndex]?
  let .eq left right := equality | none
  let target ← targetClause.head[targetHeadIndex]?
  if target = equality then none else pure ()
  let rewritten ← productionRewrite literalOrder.termOrder left right target
  let raw := productionParamodulant targetClause equalityClause target equality rewritten
  let head ← CBLocalFactorClosureWire.normalizeGeneratedHead raw.head
  some {
    signature := { equalityIndex, equalityHeadIndex, targetIndex, targetHeadIndex }
    left, right, equality, target, rewritten
    conclusion := { raw with head }
  }

def eqCandidates (literalOrder : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) : List EqCandidate :=
  (List.range retained.length).flatMap fun equalityIndex =>
    match retained[equalityIndex]? with
    | none => []
    | some equalityClause =>
      (List.range equalityClause.head.length).flatMap fun equalityHeadIndex =>
        (List.range retained.length).flatMap fun targetIndex =>
          match retained[targetIndex]? with
          | none => []
          | some targetClause =>
            (List.range targetClause.head.length).filterMap fun targetHeadIndex =>
              eqCandidate? literalOrder retained equalityIndex equalityHeadIndex
                targetIndex targetHeadIndex

theorem mem_eqCandidates_iff (literalOrder : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) (candidate : EqCandidate) :
    candidate ∈ eqCandidates literalOrder retained ↔
      ∃ equalityIndex, equalityIndex < retained.length ∧
      ∃ equalityClause, retained[equalityIndex]? = some equalityClause ∧
      ∃ equalityHeadIndex, equalityHeadIndex < equalityClause.head.length ∧
      ∃ targetIndex, targetIndex < retained.length ∧
      ∃ targetClause, retained[targetIndex]? = some targetClause ∧
      ∃ targetHeadIndex, targetHeadIndex < targetClause.head.length ∧
        eqCandidate? literalOrder retained equalityIndex equalityHeadIndex
          targetIndex targetHeadIndex = some candidate := by
  simp only [eqCandidates, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨equalityIndex, hequalityIndex, hrest⟩
    cases hequalityClause : retained[equalityIndex]? with
    | none => simp [hequalityClause] at hrest
    | some equalityClause =>
      obtain ⟨equalityHeadIndex, hequalityHeadIndex, hrest⟩ := by
        simpa [hequalityClause] using hrest
      obtain ⟨targetIndex, htargetIndex, hrest⟩ := hrest
      cases htargetClause : retained[targetIndex]? with
      | none => simp [htargetClause] at hrest
      | some targetClause =>
        refine ⟨equalityIndex, hequalityIndex, equalityClause,
          hequalityClause, equalityHeadIndex, hequalityHeadIndex,
          targetIndex, htargetIndex, targetClause, htargetClause, ?_⟩
        simpa [htargetClause, List.mem_filterMap] using hrest
  · rintro ⟨equalityIndex, hequalityIndex, equalityClause,
      hequalityClause, equalityHeadIndex, hequalityHeadIndex,
      targetIndex, htargetIndex, targetClause, htargetClause, htargetHead⟩
    refine ⟨equalityIndex, hequalityIndex, ?_⟩
    simp only [hequalityClause]
    refine List.mem_flatMap.mpr ⟨equalityHeadIndex,
      by simpa using hequalityHeadIndex, ?_⟩
    refine List.mem_flatMap.mpr ⟨targetIndex, by simpa using htargetIndex, ?_⟩
    simpa [htargetClause, List.mem_filterMap] using htargetHead

#print axioms eval_directRewrite_iff
#print axioms directParamodulant_sound
#print axioms productionParamodulant_sound
#print axioms productionRewrite_ineq_cancels
#print axioms unit_eq_ineq_productionParamodulant_is_bottom
#print axioms mem_eqCandidates_iff

end ContextCalculus.CBLocalEqEnumeration
