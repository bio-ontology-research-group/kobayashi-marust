import ContextCalculus.CBSourceLiveInsertionDerivation
import ContextCalculus.CBLocalFactorClosureWire

/-!
# Source-bound local Resolution and Factor closure

This checker avoids serializing candidate lists. It receives the already
source-bound live derivation, independently enumerates every terminal local
Resolution and Factor candidate in Lean, and requires a retained syntactic
strengthening for each one. It also checks the terminal head-normal form used
by production Factor and reflexive-inequality deletion.
-/

namespace ContextCalculus.CBSourceLocalClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBLocalFactorClosureWire

def localResolutionCandidates (retained : List FCL) : List FCL :=
  retained.flatMap fun positive =>
    retained.flatMap fun negative =>
      positive.head.filterMap fun literal =>
        if literal ∈ negative.body then
          some (resolvent positive negative literal)
        else none

def hasStrengthening (retained : List FCL) (candidate : FCL) : Bool :=
  retained.any fun clause => decide (Strengthens clause candidate)

def localResolutionClosedB (context : DecodedProductionContext bounds ontology) : Bool :=
  (localResolutionCandidates context.retained).all
    (hasStrengthening context.retained)

def localFactorClosedB (context : DecodedProductionContext bounds ontology) : Bool :=
  (context.retained.all fun clause => terminalHeadNormal clause.head) &&
    ((factorCandidates context.retained).all fun candidate =>
      hasStrengthening context.retained candidate.2)

theorem hasStrengthening_eq_true_iff (retained : List FCL) (candidate : FCL) :
    hasStrengthening retained candidate = true ↔
      ∃ clause ∈ retained, Strengthens clause candidate := by
  simp [hasStrengthening]

theorem localResolutionClosedB_sound
    (context : DecodedProductionContext bounds ontology)
    (hclosed : localResolutionClosedB context = true) :
    ∀ candidate ∈ localResolutionCandidates context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro candidate hcandidate
  have h := List.all_eq_true.mp hclosed candidate hcandidate
  exact (hasStrengthening_eq_true_iff context.retained candidate).mp h

theorem localFactorClosedB_sound
    (context : DecodedProductionContext bounds ontology)
    (hclosed : localFactorClosedB context = true) :
    (∀ clause ∈ context.retained, terminalHeadNormal clause.head = true) ∧
    (∀ candidate ∈ factorCandidates context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate.2) := by
  simp only [localFactorClosedB, Bool.and_eq_true] at hclosed
  constructor
  · intro clause hclause
    exact List.all_eq_true.mp hclosed.1 clause hclause
  · intro candidate hcandidate
    have h := List.all_eq_true.mp hclosed.2 candidate hcandidate
    exact (hasStrengthening_eq_true_iff context.retained candidate.2).mp h

structure WireSourceLocalClosureDocument where
  version : Nat
  live : WireSourceLiveInsertionDerivationDocument
deriving FromJson, ToJson

structure DecodedSourceLocalClosureDocument where
  live : DecodedSourceLiveInsertionDerivationDocument
  resolution_closed : ∀ context ∈ live.production.contexts,
    localResolutionClosedB context = true
  factor_closed : ∀ context ∈ live.production.contexts,
    localFactorClosedB context = true

def WireSourceLocalClosureDocument.decode
    (wire : WireSourceLocalClosureDocument) :
    Except String DecodedSourceLocalClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB local-closure version {wire.version}"
  let live ← wire.live.decode
  if hresolution : ∀ context ∈ live.production.contexts,
      localResolutionClosedB context = true then
    if hfactor : ∀ context ∈ live.production.contexts,
        localFactorClosedB context = true then
      return { live, resolution_closed := hresolution, factor_closed := hfactor }
    else throw "source-bound CB terminal state is not Factor-closed"
  else throw "source-bound CB terminal state is not local-Resolution-closed"

def WireSourceLocalClosureDocument.check
    (wire : WireSourceLocalClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceLocalClosureDocument.local_resolution_closed
    (decoded : DecodedSourceLocalClosureDocument) :
    ∀ context ∈ decoded.live.production.contexts,
      ∀ candidate ∈ localResolutionCandidates context.retained,
        ∃ clause ∈ context.retained, Strengthens clause candidate := by
  intro context hcontext
  exact localResolutionClosedB_sound context
    (decoded.resolution_closed context hcontext)

theorem DecodedSourceLocalClosureDocument.local_factor_closed
    (decoded : DecodedSourceLocalClosureDocument) :
    ∀ context ∈ decoded.live.production.contexts,
      (∀ clause ∈ context.retained, terminalHeadNormal clause.head = true) ∧
      (∀ candidate ∈ factorCandidates context.retained,
        ∃ clause ∈ context.retained, Strengthens clause candidate.2) := by
  intro context hcontext
  exact localFactorClosedB_sound context (decoded.factor_closed context hcontext)

theorem WireSourceLocalClosureDocument.check_sound
    (wire : WireSourceLocalClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceLocalClosureDocument,
      wire.decode = .ok decoded ∧
      (∀ context ∈ decoded.live.production.contexts,
        ∀ candidate ∈ localResolutionCandidates context.retained,
          ∃ clause ∈ context.retained, Strengthens clause candidate) ∧
      (∀ context ∈ decoded.live.production.contexts,
        (∀ clause ∈ context.retained, terminalHeadNormal clause.head = true) ∧
        (∀ candidate ∈ factorCandidates context.retained,
          ∃ clause ∈ context.retained, Strengthens clause candidate.2)) := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceLocalClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.local_resolution_closed,
        decoded.local_factor_closed⟩

#print axioms localResolutionClosedB_sound
#print axioms localFactorClosedB_sound
#print axioms WireSourceLocalClosureDocument.check_sound

end ContextCalculus.CBSourceLocalClosure
