import ContextCalculus.CBHyperClosureWire

/-!
# Exact residual Join case 3 closure

Join cases 1 and 2 are ordinary in-context resolution and are already covered
by the stronger local-resolution closure checker.  This module isolates case 3:
a ground body atom over named individuals is discharged by a body-empty
provider over `x` and a body-empty equality bridge `o ≈ x`.
-/

namespace ContextCalculus.CBJoin3Closure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBLocalFactorClosureWire

/-- Every production way of replacing one named-individual position by `x`.
For `R(o,o)`, KM also tries the simultaneous `R(x,x)` variant. -/
def variants : FLit → List (FLit × FTerm)
  | .P (.concept concept term@(.const _)) =>
      [(.P (.concept concept (.var 0)), term)]
  | .P (.role role source@(.const _) target@(.const _)) =>
      let base := [(.P (.role role (.var 0) target), source),
        (.P (.role role source (.var 0)), target)]
      if source = target then
        base ++ [(.P (.role role (.var 0) (.var 0)), source)]
      else base
  | _ => []

/-- Validate and normalize one residual Join-3 tuple.  Maximality is supplied
by the exhaustive enumeration layer, while all semantic side conditions are
rechecked here. -/
def join3Candidate? (consumer provider bridge : FCL)
    (ground general : FLit) (term : FTerm) : Option FCL := do
  if provider.body = [] ∧ bridge.body = [] ∧
      ground ∈ consumer.body ∧ general ∈ provider.head ∧
      .eq term (.var 0) ∈ bridge.head ∧
      (general, term) ∈ variants ground ∧
      ground = substL [(0, term)] general then
    let raw := join3Conclusion consumer provider bridge ground general term
    let head ← normalizeGeneratedHead raw.head
    return { raw with head }
  else none

theorem join3Candidate_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (consumer provider bridge : FCL)
    (ground general : FLit) (term : FTerm) (conclusion : FCL)
    (hcandidate : join3Candidate? consumer provider bridge ground general term =
      some conclusion)
    (hconsumer : HoldsAt model assignment consumer)
    (hprovider : HoldsAt model assignment provider)
    (hbridge : HoldsAt model assignment bridge) :
    HoldsAt model assignment conclusion := by
  by_cases hconditions : provider.body = [] ∧ bridge.body = [] ∧
      ground ∈ consumer.body ∧ general ∈ provider.head ∧
      .eq term (.var 0) ∈ bridge.head ∧
      (general, term) ∈ variants ground ∧
      ground = substL [(0, term)] general
  · let raw := join3Conclusion consumer provider bridge ground general term
    cases hnormal : normalizeGeneratedHead raw.head with
    | none =>
        simp only [join3Candidate?, if_pos hconditions] at hcandidate
        simp [raw, hnormal] at hcandidate
    | some head =>
        have hconclusion : { raw with head := head } = conclusion := by
          simp only [join3Candidate?, if_pos hconditions] at hcandidate
          simpa [raw, hnormal] using hcandidate
        rw [← hconclusion]
        apply HoldsAt.normalizeGeneratedHead_sound model assignment raw head
          hnormal
        exact join3Conclusion_sound model assignment consumer provider bridge
          ground general term hconsumer hprovider hbridge hconditions.1
          hconditions.2.1 hconditions.2.2.1 hconditions.2.2.2.1
          hconditions.2.2.2.2.2.2
  · simp [join3Candidate?, hconditions] at hcandidate

example : variants (.P (.role 0 (.const 1) (.const 1))) =
    [(.P (.role 0 (.var 0) (.const 1)), .const 1),
     (.P (.role 0 (.const 1) (.var 0)), .const 1),
     (.P (.role 0 (.var 0) (.var 0)), .const 1)] := by native_decide

#print axioms join3Candidate_sound

end ContextCalculus.CBJoin3Closure
