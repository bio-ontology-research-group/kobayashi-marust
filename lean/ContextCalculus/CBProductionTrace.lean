import ContextCalculus.CheckerTerm

/-!
# Sound traces for production CB contexts

A production context has a finite list of core predicates, not merely the
single concept core supported by the query certificate checker.  This module
checks a trace from the normalized ontology and an arbitrary list of local
assumption clauses.  Acceptance proves every retained trace clause at the
context element whenever the source ontology and all core assumptions hold.

This closes the local sound-step part of the production refinement.  Terminal
closure, redundancy deletion, inter-context transfer, and fairness are separate
obligations layered on this trace.
-/

namespace ContextCalculus.CBProductionTrace

open ContextCalculus ContextCalculus.CheckerTerm

inductive Justification where
  | premise (index : Nat) (substitution : List (Int × FTerm))
  | assumption (index : Nat)
  | tautology
  | resolve (positive negative : Nat) (literal : FLit)
  | paramodulate (equality other : Nat) (left right : FTerm) (literal : FLit)
  | factor (source : Nat) (common first second : FTerm)
  | deleteReflexiveInequality (source : Nat) (term : FTerm)
deriving Repr

abbrev Entry := FCL × Justification

def factorConclusion (source : FCL) (common first second : FTerm) : FCL :=
  ⟨source.body,
    FLit.ineq first second :: without (FLit.eq common first) source.head⟩

def deleteReflexiveInequalityConclusion (source : FCL) (term : FTerm) : FCL :=
  ⟨source.body, without (FLit.ineq term term) source.head⟩

def stepOk (ontology assumptions done : List FCL) (clause : FCL) :
    Justification → Bool
  | .premise index substitution =>
      match ontology[index]? with
      | some premise => decide (clEquivT clause (substCl substitution premise))
      | none => false
  | .assumption index =>
      match assumptions[index]? with
      | some assumption => decide (clEquivT clause assumption)
      | none => false
  | .tautology => decide (∃ literal ∈ clause.body, literal ∈ clause.head)
  | .resolve positive negative literal =>
      match done[positive]?, done[negative]? with
      | some left, some right =>
          decide (literal ∈ left.head) && decide (literal ∈ right.body) &&
            decide (clEquivT clause (resolvent left right literal))
      | _, _ => false
  | .paramodulate equality other left right literal =>
      match done[equality]?, done[other]? with
      | some eqClause, some otherClause =>
          decide (FLit.eq left right ∈ eqClause.head) &&
            decide (literal ∈ otherClause.head) &&
            decide (clEquivT clause
              (paraResolvent eqClause otherClause left right literal))
      | _, _ => false
  | .factor source common first second =>
      match done[source]? with
      | some premise =>
          decide (first ≠ second) &&
            decide (FLit.eq common first ∈ premise.head) &&
            decide (FLit.eq common second ∈ premise.head) &&
            decide (clEquivT clause
              (factorConclusion premise common first second))
      | none => false
  | .deleteReflexiveInequality source term =>
      match done[source]? with
      | some premise =>
          decide (FLit.ineq term term ∈ premise.head) &&
            decide (clEquivT clause
              (deleteReflexiveInequalityConclusion premise term))
      | none => false

def checkFold (ontology assumptions : List FCL) :
    List FCL → List Entry → Option (List FCL)
  | done, [] => some done
  | done, (clause, justification) :: rest =>
      if stepOk ontology assumptions done clause justification then
        checkFold ontology assumptions (done ++ [clause]) rest
      else none

def terminal (trace : List Entry) : List FCL := trace.map Prod.fst

def check (ontology assumptions : List FCL) (trace : List Entry) : Bool :=
  match checkFold ontology assumptions [] trace with
  | some final => decide (final = terminal trace)
  | none => false

theorem checkFold_eq_terminal (ontology assumptions : List FCL) :
    ∀ {done : List FCL} {trace : List Entry} {final : List FCL},
      checkFold ontology assumptions done trace = some final →
        final = done ++ terminal trace := by
  intro done trace
  induction trace generalizing done with
  | nil =>
      intro final hcheck
      simp only [checkFold, Option.some.injEq] at hcheck
      subst final
      simp [terminal]
  | cons entry rest ih =>
      intro final hcheck
      rcases entry with ⟨clause, justification⟩
      simp only [checkFold] at hcheck
      by_cases hstep : stepOk ontology assumptions done clause justification
      · rw [if_pos hstep] at hcheck
        rw [ih hcheck]
        simp [terminal, List.append_assoc]
      · rw [if_neg hstep] at hcheck
        contradiction

variable {D : Type}

def HoldsAt (model : TModel D) (assignment : Int → D) (clause : FCL) : Prop :=
  sat (model.evalL assignment) clause

/-- `stronger` semantically subsumes `weaker`: it requires no more body atoms
and offers no additional head alternatives.  This is the deletion relation
used by a retained-clause antichain. -/
def Strengthens (stronger weaker : FCL) : Prop :=
  stronger.body ⊆ weaker.body ∧ stronger.head ⊆ weaker.head

instance (stronger weaker : FCL) : Decidable (Strengthens stronger weaker) := by
  unfold Strengthens
  infer_instance

theorem HoldsAt.of_strengthens (model : TModel D) (assignment : Int → D)
    {stronger weaker : FCL} (hstrengthens : Strengthens stronger weaker)
    (hstronger : HoldsAt model assignment stronger) :
    HoldsAt model assignment weaker := by
  intro hbody
  have hstrongBody : ∀ literal ∈ stronger.body,
      model.evalL assignment literal := by
    intro literal hliteral
    exact hbody literal (hstrengthens.1 hliteral)
  obtain ⟨literal, hliteral, htrue⟩ := hstronger hstrongBody
  exact ⟨literal, hstrengthens.2 hliteral, htrue⟩

theorem factorConclusion_sound (model : TModel D) (assignment : Int → D)
    (source : FCL) (common first second : FTerm)
    (hdistinct : first ≠ second)
    (_hfirst : FLit.eq common first ∈ source.head)
    (hsecond : FLit.eq common second ∈ source.head)
    (hsource : HoldsAt model assignment source) :
    HoldsAt model assignment (factorConclusion source common first second) := by
  intro hbody
  obtain ⟨literal, hliteral, htrue⟩ := hsource hbody
  by_cases hremoved : literal = FLit.eq common first
  · subst literal
    simp only [TModel.evalL] at htrue
    by_cases hsecondTrue : model.evalT assignment common =
        model.evalT assignment second
    · have hreverse : second ≠ first := Ne.symm hdistinct
      exact ⟨FLit.eq common second, by
          simp [factorConclusion, mem_without, hsecond, hreverse], hsecondTrue⟩
    · have hinequality : model.evalT assignment first ≠
          model.evalT assignment second := by
          intro heq
          apply hsecondTrue
          exact htrue.trans heq
      exact ⟨FLit.ineq first second, by simp [factorConclusion], hinequality⟩
  · exact ⟨literal, by
      simp only [factorConclusion, List.mem_cons]
      exact Or.inr (mem_without.mpr ⟨hliteral, hremoved⟩), htrue⟩

theorem deleteReflexiveInequalityConclusion_sound
    (model : TModel D) (assignment : Int → D) (source : FCL) (term : FTerm)
    (hsource : HoldsAt model assignment source) :
    HoldsAt model assignment
      (deleteReflexiveInequalityConclusion source term) := by
  intro hbody
  obtain ⟨literal, hliteral, htrue⟩ := hsource hbody
  have hnot : literal ≠ FLit.ineq term term := by
    intro heq
    subst literal
    exact htrue rfl
  exact ⟨literal, mem_without.mpr ⟨hliteral, hnot⟩, htrue⟩

theorem stepOk_sound (model : TModel D) (assignment : Int → D)
    {ontology assumptions done : List FCL} {clause : FCL}
    {justification : Justification}
    (hontology : ∀ source ∈ ontology, valid model source)
    (hassumptions : ∀ assumption ∈ assumptions,
      HoldsAt model assignment assumption)
    (hdone : ∀ derived ∈ done, HoldsAt model assignment derived)
    (hstep : stepOk ontology assumptions done clause justification = true) :
    HoldsAt model assignment clause := by
  cases justification with
  | premise index substitution =>
      simp only [stepOk] at hstep
      cases hsource : ontology[index]? with
      | none => simp [hsource] at hstep
      | some source =>
          rw [hsource] at hstep
          simp only [decide_eq_true_eq] at hstep
          exact sat_of_clEquivT hstep
            (inst_valid model
              (hontology source (List.mem_of_getElem? hsource)) substitution assignment)
  | assumption index =>
      simp only [stepOk] at hstep
      cases hassumption : assumptions[index]? with
      | none => simp [hassumption] at hstep
      | some assumption =>
          rw [hassumption] at hstep
          simp only [decide_eq_true_eq] at hstep
          exact sat_of_clEquivT hstep
            (hassumptions assumption (List.mem_of_getElem? hassumption))
  | tautology =>
      simp only [stepOk, decide_eq_true_eq] at hstep
      obtain ⟨literal, hbody, hhead⟩ := hstep
      intro bodyTrue
      exact ⟨literal, hhead, bodyTrue literal hbody⟩
  | resolve positive negative literal =>
      simp only [stepOk] at hstep
      cases hleft : done[positive]? with
      | none => simp [hleft] at hstep
      | some left =>
          cases hright : done[negative]? with
          | none => simp [hleft, hright] at hstep
          | some right =>
              rw [hleft, hright] at hstep
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
              rcases hstep with ⟨⟨hpositive, hnegative⟩, hequivalent⟩
              exact sat_of_clEquivT hequivalent
                (resolution_sound (model.evalL assignment) left right literal
                  (hdone left (List.mem_of_getElem? hleft))
                  (hdone right (List.mem_of_getElem? hright))
                  hpositive hnegative)
  | paramodulate equality other left right literal =>
      simp only [stepOk] at hstep
      cases heqClause : done[equality]? with
      | none => simp [heqClause] at hstep
      | some eqClause =>
          cases hotherClause : done[other]? with
          | none => simp [heqClause, hotherClause] at hstep
          | some otherClause =>
              rw [heqClause, hotherClause] at hstep
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
              rcases hstep with ⟨⟨hequality, hliteral⟩, hequivalent⟩
              exact sat_of_clEquivT hequivalent
                (paraResolvent_sound model assignment eqClause otherClause
                  left right literal
                  (hdone eqClause (List.mem_of_getElem? heqClause))
                  (hdone otherClause (List.mem_of_getElem? hotherClause))
                  hequality hliteral)
  | factor source common first second =>
      simp only [stepOk] at hstep
      cases hsource : done[source]? with
      | none => simp [hsource] at hstep
      | some sourceClause =>
          rw [hsource] at hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          rcases hstep with ⟨⟨⟨hdistinct, hfirst⟩, hsecond⟩, hequivalent⟩
          exact sat_of_clEquivT hequivalent
            (factorConclusion_sound model assignment sourceClause common first second
              hdistinct hfirst hsecond
              (hdone sourceClause (List.mem_of_getElem? hsource)))
  | deleteReflexiveInequality source term =>
      simp only [stepOk] at hstep
      cases hsource : done[source]? with
      | none => simp [hsource] at hstep
      | some sourceClause =>
          rw [hsource] at hstep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          exact sat_of_clEquivT hstep.2
            (deleteReflexiveInequalityConclusion_sound model assignment
              sourceClause term (hdone sourceClause
                (List.mem_of_getElem? hsource)))

theorem checkFold_sound (model : TModel D) (assignment : Int → D)
    {ontology assumptions done trace final}
    (hontology : ∀ source ∈ ontology, valid model source)
    (hassumptions : ∀ assumption ∈ assumptions,
      HoldsAt model assignment assumption)
    (hdone : ∀ derived ∈ done, HoldsAt model assignment derived)
    (hcheck : checkFold ontology assumptions done trace = some final) :
    ∀ derived ∈ final, HoldsAt model assignment derived := by
  induction trace generalizing done with
  | nil =>
      simp only [checkFold, Option.some.injEq] at hcheck
      subst final
      exact hdone
  | cons entry rest ih =>
      rcases entry with ⟨clause, justification⟩
      simp only [checkFold] at hcheck
      by_cases hstep : stepOk ontology assumptions done clause justification
      · rw [if_pos hstep] at hcheck
        apply ih (done := done ++ [clause])
        · intro derived hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hdone derived hmem
          · simp only [List.mem_singleton] at hmem
            subst derived
            exact stepOk_sound model assignment hontology hassumptions hdone hstep
        · exact hcheck
      · rw [if_neg hstep] at hcheck
        contradiction

theorem check_sound (model : TModel D) (assignment : Int → D)
    {ontology assumptions trace}
    (hontology : ∀ source ∈ ontology, valid model source)
    (hassumptions : ∀ assumption ∈ assumptions,
      HoldsAt model assignment assumption)
    (hcheck : check ontology assumptions trace = true) :
    ∀ derived ∈ terminal trace, HoldsAt model assignment derived := by
  unfold check at hcheck
  cases hfold : checkFold ontology assumptions [] trace with
  | none => simp [hfold] at hcheck
  | some final =>
      rw [hfold] at hcheck
      simp only [decide_eq_true_eq] at hcheck
      subst final
      exact checkFold_sound model assignment hontology hassumptions
        (by intro derived hmem; cases hmem) hfold

private def factorSource : FCL :=
  ⟨[], [.eq (.var 0) (.var 1), .eq (.var 0) (.var 2)]⟩

private def factorTrace : List Entry :=
  [ (factorSource, .assumption 0)
  , (factorConclusion factorSource (.var 0) (.var 1) (.var 2),
      .factor 0 (.var 0) (.var 1) (.var 2)) ]

example : check [] [factorSource] factorTrace = true := by native_decide

private def badFactorTrace : List Entry :=
  [ (factorSource, .assumption 0)
  , (factorConclusion factorSource (.var 0) (.var 1) (.var 1),
      .factor 0 (.var 0) (.var 1) (.var 1)) ]

example : check [] [factorSource] badFactorTrace = false := by native_decide

private def reflexiveInequalitySource : FCL :=
  ⟨[], [.ineq (.var 0) (.var 0), .P (.concept 0 (.var 0))]⟩

private def reflexiveInequalityTrace : List Entry :=
  [ (reflexiveInequalitySource, .assumption 0)
  , (deleteReflexiveInequalityConclusion reflexiveInequalitySource (.var 0),
      .deleteReflexiveInequality 0 (.var 0)) ]

example : check [] [reflexiveInequalitySource]
    reflexiveInequalityTrace = true := by native_decide

#print axioms check_sound
#print axioms HoldsAt.of_strengthens
#print axioms factorConclusion_sound
#print axioms deleteReflexiveInequalityConclusion_sound

end ContextCalculus.CBProductionTrace
