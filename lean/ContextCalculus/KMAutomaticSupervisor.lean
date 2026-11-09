import ContextCalculus.KMAutomaticRouting

/-!
# Certified execution of the KM automatic supervisor

`KMAutomaticRouting` checks the ordered selector and its source-appropriate
fallback choice.  This module certifies the control flow that KM executes after
that choice: try the selected worker, and, when the selected atomic specialist
may defer, retain the exact fallback in the same publication sequence.

Worker adapters remain indexed by the common routed source.  Consequently the
theorem below cannot combine an ELC, HT, or CB publication checked for a
different source.

Completeness is not a field of the supervisor (v1.6.0).  It is the predicate
`CoversAt`: some route of the execution plan is complete at the source.  The
completeness theorems take coverage as a hypothesis, and concrete instances
discharge it from the totality theorems of their reference procedures on the
fragments those procedures cover (`KMSupervisorInstance`).
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

theorem select_mem_executionRoutes (decision : Decision) :
    select decision ∈ executionRoutes decision := by
  cases hfallback : automaticFallback (select decision) decision.fragment <;>
    simp [executionRoutes, hfallback]

theorem fallback_mem_executionRoutes (decision : Decision) (fallback : Route)
    (hfallback : automaticFallback (select decision) decision.fragment =
      some fallback) :
    fallback ∈ executionRoutes decision := by
  simp [executionRoutes, hfallback]

/-- A source-bound automatic supervisor.  The worker map supplies separately
certified ELC, HT, and CB adapters sharing `Source` and `correct`. -/
structure CertifiedSupervisor (Source : Type u) (Answer : Type v)
    (correct : Source → Answer → Prop) where
  decide : Source → Decision
  worker : Route → CertifiedProcedure Source Answer correct

variable {Source : Type u} {Answer : Type v} {correct : Source → Answer → Prop}

def CertifiedSupervisor.procedures
    (supervisor : CertifiedSupervisor Source Answer correct)
    (source : Source) : List (CertifiedProcedure Source Answer correct) :=
  (executionRoutes (supervisor.decide source)).map supervisor.worker

def CertifiedSupervisor.run
    (supervisor : CertifiedSupervisor Source Answer correct) :
    Procedure Source Answer where
  run source :=
    (CertifiedProcedure.firstPublish (supervisor.procedures source)).run source

/-- Coverage at a source: one route of the execution plan is complete there.
This is the only completeness argument the supervisor accepts; it follows
neither from a route name nor from process termination. -/
def CertifiedSupervisor.CoversAt
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source) :
    Prop :=
  ∃ route ∈ executionRoutes (supervisor.decide source),
    CompleteAt correct (supervisor.worker route).procedure source

/-- The selected route is always in the plan. -/
theorem CertifiedSupervisor.coversAt_of_selected
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source)
    (hcomplete : CompleteAt correct
      (supervisor.worker (select (supervisor.decide source))).procedure source) :
    supervisor.CoversAt source :=
  ⟨select (supervisor.decide source),
    select_mem_executionRoutes (supervisor.decide source), hcomplete⟩

/-- A retained fallback is in the plan. -/
theorem CertifiedSupervisor.coversAt_of_fallback
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source)
    (fallback : Route)
    (hfallback : automaticFallback (select (supervisor.decide source))
      (supervisor.decide source).fragment = some fallback)
    (hcomplete : CompleteAt correct (supervisor.worker fallback).procedure source) :
    supervisor.CoversAt source :=
  ⟨fallback, fallback_mem_executionRoutes (supervisor.decide source) fallback
    hfallback, hcomplete⟩

theorem CertifiedSupervisor.covers
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source)
    (hcovers : supervisor.CoversAt source) :
    CertifiedProcedure.Covers (supervisor.procedures source) source := by
  rcases hcovers with ⟨route, hroute, hcomplete⟩
  exact ⟨supervisor.worker route,
    List.mem_map.mpr ⟨route, hroute, rfl⟩, hcomplete⟩

theorem CertifiedSupervisor.sound
    (supervisor : CertifiedSupervisor Source Answer correct) :
    Sound correct supervisor.run := by
  intro source answer hrun
  exact CertifiedProcedure.firstPublish_sound
    (supervisor.procedures source) source answer hrun

theorem CertifiedSupervisor.completeAt
    (supervisor : CertifiedSupervisor Source Answer correct) (source : Source)
    (hcovers : supervisor.CoversAt source) :
    CompleteAt correct supervisor.run source := by
  apply firstPublish_completeAt correct
    ((supervisor.procedures source).map CertifiedProcedure.procedure) source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, _hworker, rfl⟩
    exact worker.sound source
  · rcases supervisor.covers source hcovers with ⟨worker, hmember, hcomplete⟩
    exact ⟨worker.procedure,
      List.mem_map.mpr ⟨worker, hmember, rfl⟩, hcomplete⟩

/-- Completeness on a fragment follows from coverage on that fragment. -/
theorem CertifiedSupervisor.complete_on
    (supervisor : CertifiedSupervisor Source Answer correct)
    (fragment : Source → Prop)
    (hcovers : ∀ source, fragment source → supervisor.CoversAt source) :
    CompleteOn correct fragment supervisor.run :=
  fun source hsource => supervisor.completeAt source (hcovers source hsource)

theorem CertifiedSupervisor.complete
    (supervisor : CertifiedSupervisor Source Answer correct)
    (hcovers : ∀ source, supervisor.CoversAt source) :
    ∀ source, CompleteAt correct supervisor.run source :=
  fun source => supervisor.completeAt source (hcovers source)

/-- The automatic supervisor theorem over its actual ordered execution plan.
Every published answer is correct for the exact routed source, and every
covered source has a checked publication through either the selected route or
its fallback. -/
theorem CertifiedSupervisor.sound_and_complete
    (supervisor : CertifiedSupervisor Source Answer correct)
    (hcovers : ∀ source, supervisor.CoversAt source) :
    ( ∀ source answer, supervisor.run.run source = .publish answer →
        correct source answer) ∧
      (∀ source, ∃ answer, supervisor.run.run source = .publish answer ∧
        correct source answer) :=
  ⟨supervisor.sound, supervisor.complete hcovers⟩

#print axioms CertifiedSupervisor.covers
#print axioms CertifiedSupervisor.sound
#print axioms CertifiedSupervisor.completeAt
#print axioms CertifiedSupervisor.complete_on
#print axioms CertifiedSupervisor.complete
#print axioms CertifiedSupervisor.sound_and_complete

end ContextCalculus.KMAutomaticSupervisor
