import ContextCalculus.KMAutomaticRouting

/-!
# Certified execution of the KM automatic supervisor

`KMAutomaticRouting` checks the ordered selector and its source-appropriate
fallback choice.  This module certifies the control flow that KM executes after
that choice: try the selected worker, and, when the selected atomic specialist
may defer, retain the exact fallback in the same publication sequence.

Worker adapters remain indexed by the common routed source.  Consequently the
theorem below cannot combine an ELC, HT, or CB publication checked for a
different source.  Concrete frontend adapters must discharge the two explicit
completeness fields rather than obtaining completeness from a route tag.
-/

namespace ContextCalculus.KMAutomaticSupervisor

open ContextCalculus.Certification
open ContextCalculus.CertifiedRouting
open ContextCalculus.KMAutomaticRouting

universe u v

/-- Exact route sequence used after automatic selection.  An atomic specialist
is followed by its source-appropriate fallback; every other selected route is
already a portfolio or a total calculus and appears alone. -/
def executionRoutes (decision : Decision) : List Route :=
  let selected := select decision
  match automaticFallback selected decision.fragment with
  | some fallback => [selected, fallback]
  | none => [selected]

/-- A source-bound automatic supervisor.  The worker map supplies separately
certified ELC, HT, and CB adapters sharing `Source` and `correct`.

The completeness fields expose the only two legal coverage arguments:

* a selected route with no supervisor fallback is complete for this source;
* a retained fallback is complete for this source.

Neither field follows from the route name or successful process termination.
-/
structure CertifiedSupervisor (Source : Type u) (Answer : Type v)
    (correct : Source → Answer → Prop) where
  decide : Source → Decision
  worker : Route → CertifiedProcedure Source Answer correct
  selectedComplete : ∀ source,
    automaticFallback (select (decide source)) (decide source).fragment = none →
      CompleteAt correct (worker (select (decide source))).procedure source
  fallbackComplete : ∀ source fallback,
    automaticFallback (select (decide source)) (decide source).fragment =
        some fallback →
      CompleteAt correct (worker fallback).procedure source

def CertifiedSupervisor.procedures
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct)
    (source : Source) : List (CertifiedProcedure Source Answer correct) :=
  (executionRoutes (supervisor.decide source)).map supervisor.worker

def CertifiedSupervisor.run
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct) :
    Procedure Source Answer where
  run source :=
    (CertifiedProcedure.firstPublish (supervisor.procedures source)).run source

theorem CertifiedSupervisor.covers
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source) :
    CertifiedProcedure.Covers (supervisor.procedures source) source := by
  cases hfallback : automaticFallback
      (select (supervisor.decide source)) (supervisor.decide source).fragment with
  | none =>
      refine ⟨supervisor.worker (select (supervisor.decide source)), ?_,
        supervisor.selectedComplete source hfallback⟩
      simp [CertifiedSupervisor.procedures, executionRoutes, hfallback]
  | some fallback =>
      refine ⟨supervisor.worker fallback, ?_,
        supervisor.fallbackComplete source fallback hfallback⟩
      simp [CertifiedSupervisor.procedures, executionRoutes, hfallback]

theorem CertifiedSupervisor.sound
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct) :
    Sound correct supervisor.run := by
  intro source answer hrun
  exact CertifiedProcedure.firstPublish_sound
    (supervisor.procedures source) source answer hrun

theorem CertifiedSupervisor.complete
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct) :
    ∀ source, CompleteAt correct supervisor.run source := by
  intro source
  apply firstPublish_completeAt correct
    ((supervisor.procedures source).map CertifiedProcedure.procedure) source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, _hworker, rfl⟩
    exact worker.sound source
  · rcases supervisor.covers source with ⟨worker, hmember, hcomplete⟩
    exact ⟨worker.procedure,
      List.mem_map.mpr ⟨worker, hmember, rfl⟩, hcomplete⟩

/-- The automatic supervisor theorem over its actual ordered execution plan.
Every published answer is correct for the exact routed source, and every source
has a checked publication through either the selected route or its fallback. -/
theorem CertifiedSupervisor.sound_and_complete
    {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}
    (supervisor : CertifiedSupervisor Source Answer correct) :
    ( ∀ source answer, supervisor.run.run source = .publish answer →
        correct source answer) ∧
      (∀ source, ∃ answer, supervisor.run.run source = .publish answer ∧
        correct source answer) := by
  exact ⟨supervisor.sound, supervisor.complete⟩

#print axioms CertifiedSupervisor.covers
#print axioms CertifiedSupervisor.sound
#print axioms CertifiedSupervisor.complete
#print axioms CertifiedSupervisor.sound_and_complete

end ContextCalculus.KMAutomaticSupervisor
