import ContextCalculus.KMConcreteWorkerAdapters
import ContextCalculus.KMAutomaticSupervisor

/-!
# Concrete certified KM automatic supervisor

This module removes the abstract worker-soundness premise from automatic
routing.  Every selected route executes through `KMRequestedExecution`, whose
publication can be accepted only by one of the source-bound ELC, HT, CB, or
reference checkers.

Completeness is the predicate `CoversAt`: one route of the execution plan
publishes at the source.  It is a property of the concrete executions, not a
field of the structure.  `KMSupervisorInstance` instantiates the supervisor
with the reference procedures as the last stage of every route and proves
coverage on the fragments those procedures cover; for every other source the
theorems below hold under the stated coverage hypothesis.
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
must carry accepted ELC, HT, CB, or reference evidence for the original
source. -/
structure ConcreteSupervisor where
  decide : RoutingSource → Decision
  execute : Route → KMRequestedExecution

def ConcreteSupervisor.worker (supervisor : ConcreteSupervisor)
    (route : Route) :
    CertifiedProcedure RoutingSource TaxonomyAnswer RequestedCorrect :=
  KMRequestedExecution.certifiedProcedure (supervisor.execute route)

def ConcreteSupervisor.certified (supervisor : ConcreteSupervisor) :
    KMAutomaticSupervisor.CertifiedSupervisor
      RoutingSource TaxonomyAnswer RequestedCorrect where
  decide := supervisor.decide
  worker := supervisor.worker

def ConcreteSupervisor.run (supervisor : ConcreteSupervisor) :
    Procedure RoutingSource TaxonomyAnswer :=
  supervisor.certified.run

/-- Coverage at a source: one route of the plan publishes there. -/
def ConcreteSupervisor.CoversAt (supervisor : ConcreteSupervisor)
    (source : RoutingSource) : Prop :=
  ∃ route ∈ executionRoutes (supervisor.decide source),
    (supervisor.execute route).worker.CompleteAt source

theorem ConcreteSupervisor.certified_coversAt (supervisor : ConcreteSupervisor)
    (source : RoutingSource) (hcovers : supervisor.CoversAt source) :
    supervisor.certified.CoversAt source := by
  rcases hcovers with ⟨route, hroute, hcomplete⟩
  refine ⟨route, hroute, ?_⟩
  simpa [ConcreteSupervisor.certified, ConcreteSupervisor.worker,
    KMRequestedExecution.certifiedProcedure] using
    (supervisor.execute route).worker.erase_completeAt source hcomplete

theorem ConcreteSupervisor.sound (supervisor : ConcreteSupervisor) :
    Sound RequestedCorrect supervisor.run :=
  supervisor.certified.sound

theorem ConcreteSupervisor.completeAt (supervisor : ConcreteSupervisor)
    (source : RoutingSource) (hcovers : supervisor.CoversAt source) :
    CompleteAt RequestedCorrect supervisor.run source :=
  supervisor.certified.completeAt source
    (supervisor.certified_coversAt source hcovers)

theorem ConcreteSupervisor.complete_on (supervisor : ConcreteSupervisor)
    (fragment : RoutingSource → Prop)
    (hcovers : ∀ source, fragment source → supervisor.CoversAt source) :
    CompleteOn RequestedCorrect fragment supervisor.run :=
  fun source hsource => supervisor.completeAt source (hcovers source hsource)

theorem ConcreteSupervisor.complete (supervisor : ConcreteSupervisor)
    (hcovers : ∀ source, supervisor.CoversAt source) :
    ∀ source, CompleteAt RequestedCorrect supervisor.run source :=
  fun source => supervisor.completeAt source (hcovers source)

/-- Concrete automatic-routing capstone.  No route or profile predicate is
trusted for soundness: each publication is rechecked against the exact source.
Completeness follows from coverage, which `KMSupervisorInstance` proves from
the reference procedures on their fragments. -/
theorem ConcreteSupervisor.sound_and_complete
    (supervisor : ConcreteSupervisor)
    (hcovers : ∀ source, supervisor.CoversAt source) :
    (∀ source answer, supervisor.run.run source = .publish answer →
      RequestedCorrect source answer) ∧
    (∀ source, ∃ answer, supervisor.run.run source = .publish answer ∧
      RequestedCorrect source answer) :=
  ⟨supervisor.sound, supervisor.complete hcovers⟩

/-- Changing profile decisions cannot make a published answer unsound.  It can
only change which checked execution is attempted and which coverage argument
applies. -/
theorem ConcreteSupervisor.profile_independent_sound
    (supervisor : ConcreteSupervisor) (source : RoutingSource)
    (answer : TaxonomyAnswer)
    (hrun : supervisor.run.run source = .publish answer) :
    RequestedCorrect source answer :=
  supervisor.sound source answer hrun

#print axioms KMRequestedExecution.certifiedProcedure
#print axioms ConcreteSupervisor.certified
#print axioms ConcreteSupervisor.sound
#print axioms ConcreteSupervisor.completeAt
#print axioms ConcreteSupervisor.complete_on
#print axioms ConcreteSupervisor.complete
#print axioms ConcreteSupervisor.sound_and_complete
#print axioms ConcreteSupervisor.profile_independent_sound

end ContextCalculus.KMConcreteAutomaticSupervisor
