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

structure Join3Signature where
  consumerIndex : Nat
  bodyIndex : Nat
  variantIndex : Nat
  providerIndex : Nat
  providerHeadIndex : Nat
  bridgeIndex : Nat
  bridgeHeadIndex : Nat
deriving DecidableEq, Repr

/-- Reconstruct one candidate exclusively from bounded retained-list indexes.
Both provider literals are checked maximal from the certified literal order;
the provider and bridge must be distinct retained clauses, matching KM's
work-off/index discipline. -/
def candidateAt? (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) (signature : Join3Signature) : Option FCL := do
  let consumer ← retained[signature.consumerIndex]?
  let ground ← consumer.body[signature.bodyIndex]?
  let (general, term) ← (variants ground)[signature.variantIndex]?
  let provider ← retained[signature.providerIndex]?
  if signature.providerHeadIndex ∈ order.maximalHeadIndices provider.head then
    pure ()
  else none
  let providerLiteral ← provider.head[signature.providerHeadIndex]?
  if providerLiteral = general then pure () else none
  let bridge ← retained[signature.bridgeIndex]?
  if signature.providerIndex ≠ signature.bridgeIndex then pure () else none
  if signature.bridgeHeadIndex ∈ order.maximalHeadIndices bridge.head then
    pure ()
  else none
  let bridgeLiteral ← bridge.head[signature.bridgeHeadIndex]?
  if bridgeLiteral = .eq term (.var 0) then pure () else none
  join3Candidate? consumer provider bridge ground general term

theorem candidateAt_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) (signature : Join3Signature) (conclusion : FCL)
    (hcandidate : candidateAt? order retained signature = some conclusion)
    (hretained : ∀ clause ∈ retained, HoldsAt model assignment clause) :
    HoldsAt model assignment conclusion := by
  cases hconsumer : retained[signature.consumerIndex]? with
  | none => simp [candidateAt?, hconsumer] at hcandidate
  | some consumer =>
    cases hground : consumer.body[signature.bodyIndex]? with
    | none => simp [candidateAt?, hconsumer, hground] at hcandidate
    | some ground =>
      cases hvariant : (variants ground)[signature.variantIndex]? with
      | none => simp [candidateAt?, hconsumer, hground, hvariant] at hcandidate
      | some variant =>
        rcases variant with ⟨general, term⟩
        cases hprovider : retained[signature.providerIndex]? with
        | none =>
            simp [candidateAt?, hconsumer, hground, hvariant, hprovider]
              at hcandidate
        | some provider =>
          by_cases hproviderMax : signature.providerHeadIndex ∈
              order.maximalHeadIndices provider.head
          · cases hproviderLiteral : provider.head[signature.providerHeadIndex]? with
            | none =>
                simp [candidateAt?, hconsumer, hground, hvariant, hprovider,
                  hproviderMax, hproviderLiteral] at hcandidate
            | some providerLiteral =>
              by_cases hproviderEq : providerLiteral = general
              · cases hbridge : retained[signature.bridgeIndex]? with
                | none =>
                    simp [candidateAt?, hconsumer, hground, hvariant,
                      hprovider, hproviderMax, hproviderLiteral, hproviderEq,
                      hbridge] at hcandidate
                | some bridge =>
                  by_cases hdistinct : signature.providerIndex ≠
                      signature.bridgeIndex
                  · by_cases hbridgeMax : signature.bridgeHeadIndex ∈
                        order.maximalHeadIndices bridge.head
                    · cases hbridgeLiteral : bridge.head[signature.bridgeHeadIndex]? with
                      | none =>
                          simp [candidateAt?, hconsumer, hground, hvariant,
                            hprovider, hproviderMax, hproviderLiteral,
                            hproviderEq, hbridge, hdistinct, hbridgeMax,
                            hbridgeLiteral] at hcandidate
                      | some bridgeLiteral =>
                        by_cases hbridgeEq : bridgeLiteral = .eq term (.var 0)
                        · have hjoin : join3Candidate? consumer provider bridge
                              ground general term = some conclusion := by
                            simpa [candidateAt?, hconsumer, hground, hvariant,
                              hprovider, hproviderMax, hproviderLiteral,
                              hproviderEq, hbridge, hdistinct, hbridgeMax,
                              hbridgeLiteral, hbridgeEq] using hcandidate
                          apply join3Candidate_sound model assignment consumer
                            provider bridge ground general term conclusion hjoin
                          · exact hretained consumer
                              ((List.getElem?_eq_some_iff.mp hconsumer).2 ▸
                                List.getElem_mem
                                  (List.getElem?_eq_some_iff.mp hconsumer).1)
                          · exact hretained provider
                              ((List.getElem?_eq_some_iff.mp hprovider).2 ▸
                                List.getElem_mem
                                  (List.getElem?_eq_some_iff.mp hprovider).1)
                          · exact hretained bridge
                              ((List.getElem?_eq_some_iff.mp hbridge).2 ▸
                                List.getElem_mem
                                  (List.getElem?_eq_some_iff.mp hbridge).1)
                        · simp [candidateAt?, hconsumer, hground, hvariant,
                            hprovider, hproviderMax, hproviderLiteral,
                            hproviderEq, hbridge, hdistinct, hbridgeMax,
                            hbridgeLiteral, hbridgeEq] at hcandidate
                    · simp [candidateAt?, hconsumer, hground, hvariant,
                        hprovider, hproviderMax, hproviderLiteral, hproviderEq,
                        hbridge, hdistinct, hbridgeMax] at hcandidate
                  · simp [candidateAt?, hconsumer, hground, hvariant,
                      hprovider, hproviderMax, hproviderLiteral, hproviderEq,
                      hbridge, hdistinct] at hcandidate
              · simp [candidateAt?, hconsumer, hground, hvariant, hprovider,
                  hproviderMax, hproviderLiteral, hproviderEq] at hcandidate
          · simp [candidateAt?, hconsumer, hground, hvariant, hprovider,
              hproviderMax] at hcandidate

/-- Enumerate every bounded residual Join-3 signature independently of runtime
indexes and arrival order. -/
def signatures (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) : List Join3Signature :=
  (List.range retained.length).flatMap fun consumerIndex =>
    match retained[consumerIndex]? with
    | none => []
    | some consumer =>
      (List.range consumer.body.length).flatMap fun bodyIndex =>
        match consumer.body[bodyIndex]? with
        | none => []
        | some ground =>
          (List.range (variants ground).length).flatMap fun variantIndex =>
            (List.range retained.length).flatMap fun providerIndex =>
              match retained[providerIndex]? with
              | none => []
              | some provider =>
                (order.maximalHeadIndices provider.head).flatMap fun providerHeadIndex =>
                  (List.range retained.length).flatMap fun bridgeIndex =>
                    match retained[bridgeIndex]? with
                    | none => []
                    | some bridge =>
                      (order.maximalHeadIndices bridge.head).map fun bridgeHeadIndex =>
                        {
                          consumerIndex, bodyIndex, variantIndex, providerIndex,
                          providerHeadIndex, bridgeIndex, bridgeHeadIndex }

/-- Checked conclusions for all signatures. Duplicate semantic conclusions
remain separate because each production firing must be covered. -/
def candidates (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) : List (Join3Signature × FCL) :=
  (signatures order retained).filterMap fun signature =>
    (candidateAt? order retained signature).map fun conclusion =>
      (signature, conclusion)

theorem mem_candidates_has_checked_origin
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL)
    (candidate : Join3Signature × FCL) (hmember : candidate ∈ candidates order retained) :
    candidateAt? order retained candidate.1 = some candidate.2 := by
  simp only [candidates, List.mem_filterMap] at hmember
  obtain ⟨signature, _hsignature, hcandidate⟩ := hmember
  cases hresult : candidateAt? order retained signature with
  | none => simp [hresult] at hcandidate
  | some conclusion =>
      simp only [hresult, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hcandidate
      rcases hcandidate with ⟨rfl, rfl⟩
      exact hresult

theorem candidates_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL)
    (hretained : ∀ clause ∈ retained, HoldsAt model assignment clause) :
    ∀ candidate ∈ candidates order retained,
      HoldsAt model assignment candidate.2 := by
  intro candidate hcandidate
  exact candidateAt_sound model assignment order retained candidate.1 candidate.2
    (mem_candidates_has_checked_origin order retained candidate hcandidate)
    hretained

example : variants (.P (.role 0 (.const 1) (.const 1))) =
    [(.P (.role 0 (.var 0) (.const 1)), .const 1),
     (.P (.role 0 (.const 1) (.var 0)), .const 1),
     (.P (.role 0 (.var 0) (.var 0)), .const 1)] := by native_decide

#print axioms join3Candidate_sound
#print axioms mem_candidates_has_checked_origin
#print axioms candidateAt_sound
#print axioms candidates_sound

end ContextCalculus.CBJoin3Closure
