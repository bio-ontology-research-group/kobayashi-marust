import ContextCalculus.KMConcreteWorkerAdapters
import ContextCalculus.KMAutomaticSupervisor

/-!
# Concrete certified KM automatic supervisor

This module removes the abstract worker-soundness premise from automatic
routing.  Every selected route executes through `KMExactExecution`, whose
publication can be accepted only by one of the source-bound ELC, HT, or CB
wire checkers.

Operational completeness remains stated as the two observable liveness
obligations of the native supervisor: a selected route with no outer fallback
publishes, or the retained fallback publishes.  These are properties of
process execution, not logical assumptions about a route tag.  Given those
execution facts, the capstone proves exact taxonomy soundness and completeness
for the concrete routed source.
-/

namespace ContextCalculus.KMConcreteAutomaticSupervisor

open ContextCalculus
open ContextCalculus.Certification
open ContextCalculus.CertifiedRouting
open ContextCalculus.KMAutomaticRouting
open ContextCalculus.KMAutomaticSupervisor
open ContextCalculus.KMConcreteWorkerAdapters

abbrev RoutingSource := RequestedTaxonomySource

def KMRequestedExecution.certifiedProcedure (execution : KMRequestedExecution) :
    CertifiedProcedure RoutingSource TaxonomyAnswer RequestedCorrect where
  procedure := execution.worker.erase
  sound := execution.worker_soundAt

/-- The exact production boundary for automatic routing.  `execute` may vary
threading, scheduling, or internal portfolios by route, but every publication
must carry accepted ELC, HT, or CB evidence for the original source. -/
structure ConcreteSupervisor where
  decide : RoutingSource → Decision
  execute : Route → KMRequestedExecution
  selectedComplete : ∀ source,
    automaticFallback (select (decide source)) (decide source).fragment = none →
      (execute (select (decide source))).worker.CompleteAt source
  fallbackComplete : ∀ source fallback,
    automaticFallback (select (decide source)) (decide source).fragment =
        some fallback →
      (execute fallback).worker.CompleteAt source

def ConcreteSupervisor.worker (supervisor : ConcreteSupervisor)
    (route : Route) :
    CertifiedProcedure RoutingSource TaxonomyAnswer RequestedCorrect :=
  KMRequestedExecution.certifiedProcedure (supervisor.execute route)

def ConcreteSupervisor.certified (supervisor : ConcreteSupervisor) :
    KMAutomaticSupervisor.CertifiedSupervisor
      RoutingSource TaxonomyAnswer RequestedCorrect where
  decide := supervisor.decide
  worker := supervisor.worker
  selectedComplete := by
    intro source hnone
    simpa [ConcreteSupervisor.worker, KMRequestedExecution.certifiedProcedure] using
      (supervisor.execute (select (supervisor.decide source))).worker
        |>.erase_completeAt source (supervisor.selectedComplete source hnone)
  fallbackComplete := by
    intro source fallback hfallback
    simpa [ConcreteSupervisor.worker, KMRequestedExecution.certifiedProcedure] using
      (supervisor.execute fallback).worker.erase_completeAt source
        (supervisor.fallbackComplete source fallback hfallback)

def ConcreteSupervisor.run (supervisor : ConcreteSupervisor) :
    Procedure RoutingSource TaxonomyAnswer :=
  supervisor.certified.run

theorem ConcreteSupervisor.sound (supervisor : ConcreteSupervisor) :
    Sound RequestedCorrect supervisor.run :=
  supervisor.certified.sound

theorem ConcreteSupervisor.complete (supervisor : ConcreteSupervisor) :
    ∀ source, CompleteAt RequestedCorrect supervisor.run source :=
  supervisor.certified.complete

/-- Concrete automatic-routing capstone.  No route or profile predicate is
trusted for soundness: each publication is rechecked against the exact source.
Completeness follows from the native selected/fallback publication facts. -/
theorem ConcreteSupervisor.sound_and_complete
    (supervisor : ConcreteSupervisor) :
    (∀ source answer, supervisor.run.run source = .publish answer →
      RequestedCorrect source answer) ∧
    (∀ source, ∃ answer, supervisor.run.run source = .publish answer ∧
      RequestedCorrect source answer) :=
  supervisor.certified.sound_and_complete

/-- Changing profile decisions cannot make a published answer unsound.  It can
only change which checked execution is attempted and which liveness obligation
must establish coverage. -/
theorem ConcreteSupervisor.profile_independent_sound
    (supervisor : ConcreteSupervisor) (source : RoutingSource)
    (answer : TaxonomyAnswer)
    (hrun : supervisor.run.run source = .publish answer) :
    RequestedCorrect source answer :=
  supervisor.sound source answer hrun

#print axioms KMRequestedExecution.certifiedProcedure
#print axioms ConcreteSupervisor.certified
#print axioms ConcreteSupervisor.sound
#print axioms ConcreteSupervisor.complete
#print axioms ConcreteSupervisor.sound_and_complete
#print axioms ConcreteSupervisor.profile_independent_sound

end ContextCalculus.KMConcreteAutomaticSupervisor
