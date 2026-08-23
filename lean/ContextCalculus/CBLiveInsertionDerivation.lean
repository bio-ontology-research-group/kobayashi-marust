import ContextCalculus.CBLiveStateWire

/-!
# Chronological soundness of live CB insertions

The live engine records every successful context-clause insertion in one global
chronological stream. A local derivation may use only explicitly selected,
earlier events from the same context. It may then append an arbitrary checked
`CBProductionTrace` fragment, allowing source instantiation and intermediate
resolution clauses that were not themselves retained by KM. This module proves
the induction principle consumed by the production evidence wire.

Inter-context arrivals require the separate checked Pred/r-Pred transfer
constructor and are deliberately not admitted as local derivations here.
-/

namespace ContextCalculus.CBLiveInsertionDerivation

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLiveStateWire

abbrev LiveEvent (production : DecodedProductionRun)
    (ordinary root : List FCL) :=
  DecodedLiveInsertionEvent production ordinary root

def EventSound (event : LiveEvent production ordinary root) : Prop :=
  ∀ {D : Type} (model : TModel D) (assignment : Int → D),
    (∀ source ∈ production.source.ontology, valid model source) →
    CoreHolds model assignment
      (production.contexts.get event.contextIndex).core →
    HoldsAt model assignment event.clause

structure PriorLocalRef
    (done : List (LiveEvent production ordinary root))
    (event : LiveEvent production ordinary root) where
  index : Fin done.length
  context_eq : (done.get index).contextIndex = event.contextIndex

def priorClauses
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (references : List (PriorLocalRef done event)) : List FCL :=
  references.map fun reference => (done.get reference.index).clause

inductive EventEvidence
    (done : List (LiveEvent production ordinary root)) :
    LiveEvent production ordinary root → Type
  | seed (event) (hseed : event.origin ≠ .derived) : EventEvidence done event
  | localTrace (event)
      (references : List (PriorLocalRef done event))
      (trace : List Entry) (final : List FCL)
      (checked : checkFold production.source.ontology
        (production.contexts.get event.contextIndex).assumptions
        (priorClauses references) trace = some final)
      (conclusion : event.clause ∈ final) : EventEvidence done event

inductive CertifiedHistory :
    List (LiveEvent production ordinary root) → Type
  | nil : CertifiedHistory []
  | snoc {done event} : CertifiedHistory done → EventEvidence done event →
      CertifiedHistory (done ++ [event])

private theorem prior_local_sound
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (hall : ∀ prior ∈ done, EventSound prior)
    (references : List (PriorLocalRef done event))
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ production.source.ontology, valid model source)
    (hcore : CoreHolds model assignment
      (production.contexts.get event.contextIndex).core) :
    ∀ clause ∈ priorClauses references, HoldsAt model assignment clause := by
  intro clause hclause
  simp only [priorClauses, List.mem_map] at hclause
  obtain ⟨reference, _, rfl⟩ := hclause
  have hprior : EventSound (done.get reference.index) :=
    hall (done.get reference.index) (List.get_mem done reference.index)
  have hpriorCore : CoreHolds model assignment
      (production.contexts.get (done.get reference.index).contextIndex).core := by
    rw [congrArg (fun contextIndex =>
      (production.contexts.get contextIndex).core) reference.context_eq]
    exact hcore
  exact hprior model assignment hontology hpriorCore

theorem EventEvidence.sound
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (evidence : EventEvidence done event)
    (hall : ∀ prior ∈ done, EventSound prior) : EventSound event := by
  cases evidence with
  | seed hseed =>
      intro D model assignment hontology hcore
      exact event.seed_sound model assignment hontology hcore hseed
  | localTrace references trace final checked conclusion =>
      intro D model assignment hontology hcore
      have hfinal := checkFold_sound model assignment hontology
        (fun assumption hassumption => by
          rw [(production.contexts.get event.contextIndex).assumptions_eq]
            at hassumption
          simp only [List.mem_map] at hassumption
          obtain ⟨predicate, hpredicate, rfl⟩ := hassumption
          intro _
          exact ⟨.P predicate, List.mem_singleton.mpr rfl,
            hcore predicate hpredicate⟩)
        (prior_local_sound hall references model assignment hontology hcore)
        checked
      exact hfinal event.clause conclusion

theorem CertifiedHistory.sound
    {history : List (LiveEvent production ordinary root)}
    (certificate : CertifiedHistory history) :
    ∀ event ∈ history, EventSound event := by
  induction certificate
  case nil => simp
  case snoc =>
      rename_i priorCertificate evidence ih
      intro candidate hcandidate
      simp only [List.mem_append, List.mem_singleton] at hcandidate
      rcases hcandidate with hprior | rfl
      · exact ih candidate hprior
      · exact evidence.sound ih

#print axioms EventEvidence.sound
#print axioms CertifiedHistory.sound

end ContextCalculus.CBLiveInsertionDerivation
