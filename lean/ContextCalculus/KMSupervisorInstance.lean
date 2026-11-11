import ContextCalculus.KMConcreteAutomaticSupervisor

/-!
# The KM supervisor instance and its completeness on the EL fragment

This is the v1.6.0 capstone (`docs/V1.6.0-COMPLETENESS-PLAN.md`).  The
supervisor is instantiated with an arbitrary fail-closed Rust executor and an
arbitrary router decision; every route's execution is followed by the EL
reference procedure.  Soundness holds for every source.  Completeness holds
for every source of the EL fragment, whatever the router decided and whatever
the Rust workers did, because the reference procedure publishes an accepted
answer on that fragment.

The theorem is about the idealised procedure: the reference closure has no
resource bound.  Running it as a process can time out, which the fail-closed
design turns into no answer, never into a wrong one.
-/

namespace ContextCalculus.KMSupervisorInstance

open ContextCalculus
open ContextCalculus.Certification
open ContextCalculus.CertifiedRouting
open ContextCalculus.KMAutomaticRouting
open ContextCalculus.KMAutomaticSupervisor
open ContextCalculus.KMConcreteWorkerAdapters
open ContextCalculus.KMConcreteAutomaticSupervisor

/-- The EL fragment of the common source, as the recogniser accepts it, with a
duplicate-free request list (a request with duplicates has no correct
answer). -/
def ELFragment (source : RoutingSource) : Prop :=
  (ELCommonSourceRecognizer.recognizeEL source.named source.ontology).isSome =
      true ∧
    source.named.Nodup

/-- The ALC fragment of the common source, as the recogniser accepts it, with a
duplicate-free request list. -/
def ALCFragment (source : RoutingSource) : Prop :=
  (ALCCommonSourceRecognizer.recognizeALC source.named source.ontology).isSome =
      true ∧
    source.named.Nodup

/-- Every route runs its Rust execution first, then the EL reference procedure,
and finally the ALC reference procedure when earlier stages do not publish. -/
def kmExecute (rust : Route → KMRequestedExecution) (route : Route) :
    KMRequestedExecution :=
  ((rust route).orElse elReferenceExecution).orElse alcReferenceExecution

/-- The KM supervisor for a fail-closed Rust executor and a router decision.
Both are parameters: nothing about the Rust workers' behaviour on a source, and
nothing about the profile predicates behind the decision, is assumed. -/
def kmSupervisor (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) : ConcreteSupervisor where
  decide := decide
  execute := kmExecute rust

theorem kmSupervisor_sound (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) :
    Sound RequestedCorrect (kmSupervisor rust decide).run :=
  (kmSupervisor rust decide).sound

/-- On the EL fragment the selected route itself covers the source, through
its reference stage. -/
theorem kmSupervisor_coversAt_of_EL (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) (source : RoutingSource)
    (hsource : ELFragment source) :
    (kmSupervisor rust decide).CoversAt source :=
  ⟨select (decide source), select_mem_executionRoutes (decide source),
    KMRequestedExecution.orElse_completeAt_left _ _ source
      (KMRequestedExecution.orElse_completeAt_right _ _ source
        (elReferenceExecution_completeAt source hsource.1 hsource.2))⟩

theorem kmSupervisor_complete_on_EL (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect ELFragment (kmSupervisor rust decide).run :=
  (kmSupervisor rust decide).complete_on ELFragment
    (kmSupervisor_coversAt_of_EL rust decide)

/-- The v1.6.0 capstone: for every fail-closed executor and every router
decision, every published answer is exact, and every EL source receives one. -/
theorem kmSupervisor_sound_and_complete_on_EL
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    (∀ source answer,
      (kmSupervisor rust decide).run.run source = .publish answer →
        RequestedCorrect source answer) ∧
    (∀ source, ELFragment source →
      ∃ answer, (kmSupervisor rust decide).run.run source = .publish answer ∧
        RequestedCorrect source answer) :=
  ⟨kmSupervisor_sound rust decide, kmSupervisor_complete_on_EL rust decide⟩

/-- On the ALC fragment the selected route covers the source through its ALC
reference stage. -/
theorem kmSupervisor_coversAt_of_ALC (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) (source : RoutingSource)
    (hsource : ALCFragment source) :
    (kmSupervisor rust decide).CoversAt source :=
  ⟨select (decide source), select_mem_executionRoutes (decide source),
    KMRequestedExecution.orElse_completeAt_right _ _ source
      (alcReferenceExecution_completeAt source hsource.1 hsource.2)⟩

theorem kmSupervisor_complete_on_ALC (rust : Route → KMRequestedExecution)
    (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect ALCFragment (kmSupervisor rust decide).run :=
  (kmSupervisor rust decide).complete_on ALCFragment
    (kmSupervisor_coversAt_of_ALC rust decide)

theorem kmSupervisor_sound_and_complete_on_ALC
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    (∀ source answer,
      (kmSupervisor rust decide).run.run source = .publish answer →
        RequestedCorrect source answer) ∧
    (∀ source, ALCFragment source →
      ∃ answer, (kmSupervisor rust decide).run.run source = .publish answer ∧
        RequestedCorrect source answer) :=
  ⟨kmSupervisor_sound rust decide, kmSupervisor_complete_on_ALC rust decide⟩

theorem kmSupervisor_complete_on_EL_or_ALC
    (rust : Route → KMRequestedExecution) (decide : RoutingSource → Decision) :
    CompleteOn RequestedCorrect (fun source => ELFragment source ∨ ALCFragment source)
      (kmSupervisor rust decide).run :=
  (kmSupervisor rust decide).complete_on
    (fun source => ELFragment source ∨ ALCFragment source)
    (fun source hsource =>
      match hsource with
      | .inl hel => kmSupervisor_coversAt_of_EL rust decide source hel
      | .inr halc => kmSupervisor_coversAt_of_ALC rust decide source halc)

#print axioms kmSupervisor_sound
#print axioms kmSupervisor_coversAt_of_EL
#print axioms kmSupervisor_complete_on_EL
#print axioms kmSupervisor_sound_and_complete_on_EL
#print axioms kmSupervisor_coversAt_of_ALC
#print axioms kmSupervisor_complete_on_ALC
#print axioms kmSupervisor_sound_and_complete_on_ALC
#print axioms kmSupervisor_complete_on_EL_or_ALC

end ContextCalculus.KMSupervisorInstance
