import ContextCalculus.Certification

/-!
# Source-exact certification contracts for automatic routing

`Certification.lean` proves the control-flow algebra for procedures whose input
is already shared.  The executable KM workers additionally exchange certificate
documents.  This module records the missing delivery obligation: a publication
is admitted only when its evidence checker was run against the exact source
given to the router.

The checker is deliberately indexed by `Source`.  Consequently there is no
operation that can erase the routed source and later attach an unrelated ELC,
HT, or CB certificate.  Concrete worker adapters must instantiate `accept` and
`accept_sound` with their source-bound executable checkers.
-/

namespace ContextCalculus.CertifiedRouting

open ContextCalculus.Certification

universe u v w

/-- An answer accompanied by the worker evidence that was checked for the
exact routed source. -/
structure Publication (Source : Type u) (Answer : Type v)
    (Evidence : Type w) where
  source : Source
  answer : Answer
  evidence : Evidence

/-- A worker boundary whose acceptance predicate receives the routed source,
the proposed answer, and the evidence together. -/
structure SourceBoundWorker (Source : Type u) (Answer : Type v)
    (Evidence : Type w) (correct : Source → Answer → Prop) where
  run : Source → Outcome (Publication Source Answer Evidence)
  accept : Source → Answer → Evidence → Bool
  run_source_exact : ∀ source publication,
    run source = .publish publication → publication.source = source
  run_accepted : ∀ source publication,
    run source = .publish publication →
      accept source publication.answer publication.evidence = true
  accept_sound : ∀ source answer evidence,
    accept source answer evidence = true → correct source answer

def SourceBoundWorker.erase
    {Source : Type u} {Answer : Type v} {Evidence : Type w}
    {correct : Source → Answer → Prop}
    (worker : SourceBoundWorker Source Answer Evidence correct) :
    Procedure Source Answer where
  run source :=
    match worker.run source with
    | .publish publication => .publish publication.answer
    | .defer => .defer
    | .error => .error
    | .timeout => .timeout

theorem SourceBoundWorker.erase_soundAt
    {Source : Type u} {Answer : Type v} {Evidence : Type w}
    {correct : Source → Answer → Prop}
    (worker : SourceBoundWorker Source Answer Evidence correct)
    (source : Source) : SoundAt correct worker.erase source := by
  intro answer hrun
  unfold SourceBoundWorker.erase at hrun
  cases hworker : worker.run source with
  | publish publication =>
      have heq : publication.answer = answer := by
        simpa [hworker] using hrun
      rw [← heq]
      exact worker.accept_sound source publication.answer publication.evidence
        (worker.run_accepted source publication hworker)
  | defer => simp [hworker] at hrun
  | error => simp [hworker] at hrun
  | timeout => simp [hworker] at hrun

/-- A source-exact completeness witness.  Fragment-gated workers establish
this from their fragment theorem; fallback portfolios establish it from one of
their complete members. -/
def SourceBoundWorker.CompleteAt
    {Source : Type u} {Answer : Type v} {Evidence : Type w}
    {correct : Source → Answer → Prop}
    (worker : SourceBoundWorker Source Answer Evidence correct)
    (source : Source) : Prop :=
  ∃ publication, worker.run source = .publish publication

theorem SourceBoundWorker.erase_completeAt
    {Source : Type u} {Answer : Type v} {Evidence : Type w}
    {correct : Source → Answer → Prop}
    (worker : SourceBoundWorker Source Answer Evidence correct)
    (source : Source) (hcomplete : worker.CompleteAt source) :
    ContextCalculus.Certification.CompleteAt correct worker.erase source := by
  rcases hcomplete with ⟨publication, hpublication⟩
  refine ⟨publication.answer, ?_, ?_⟩
  · simp [SourceBoundWorker.erase, hpublication]
  · exact worker.accept_sound source publication.answer publication.evidence
      (worker.run_accepted source publication hpublication)

/-- A checked frontend boundary from the router's source language to one
worker's normalized source language.  `correct_iff` is the semantic
preservation obligation: translating the source changes neither the meaning of
the published taxonomy nor the consistency verdict represented by `Answer`.

This field is intentionally propositional rather than a hash or route tag. A
concrete ELC, HT, or CB adapter must prove it from the frontend normalization
theorems for the exact source it serializes.
-/
structure SourceTranslation (Source : Type u) (WorkerSource : Type v)
    (Answer : Type w) (sourceCorrect : Source → Answer → Prop)
    (workerCorrect : WorkerSource → Answer → Prop) where
  translate : Source → WorkerSource
  correct_iff : ∀ source answer,
    workerCorrect (translate source) answer ↔ sourceCorrect source answer

/-- Lift an already source-bound worker through a semantics-preserving
frontend translation.  The lifted publication records the original router
source, while acceptance reruns the worker checker against exactly the
translated source produced from it. -/
def SourceBoundWorker.liftTranslation
    {Source : Type u} {WorkerSource : Type v} {Answer : Type w}
    {Evidence : Type _} {sourceCorrect : Source → Answer → Prop}
    {workerCorrect : WorkerSource → Answer → Prop}
    (translation : SourceTranslation Source WorkerSource Answer
      sourceCorrect workerCorrect)
    (worker : SourceBoundWorker WorkerSource Answer Evidence workerCorrect) :
    SourceBoundWorker Source Answer Evidence sourceCorrect where
  run source :=
    match hrun : worker.run (translation.translate source) with
    | .publish publication => .publish {
        source
        answer := publication.answer
        evidence := publication.evidence
      }
    | .defer => .defer
    | .error => .error
    | .timeout => .timeout
  accept source answer evidence :=
    worker.accept (translation.translate source) answer evidence
  run_source_exact := by
    intro source publication hpublication
    split at hpublication
    next workerPublication hrun =>
      injection hpublication with hpublication
      rw [← hpublication]
    all_goals simp_all
  run_accepted := by
    intro source publication hpublication
    split at hpublication
    next workerPublication hrun =>
      simp only [Outcome.publish.injEq] at hpublication
      subst publication
      exact worker.run_accepted (translation.translate source)
        workerPublication hrun
    all_goals simp_all
  accept_sound := by
    intro source answer evidence haccept
    exact (translation.correct_iff source answer).mp
      (worker.accept_sound (translation.translate source) answer evidence haccept)

theorem SourceBoundWorker.liftTranslation_completeAt
    {Source : Type u} {WorkerSource : Type v} {Answer : Type w}
    {Evidence : Type _} {sourceCorrect : Source → Answer → Prop}
    {workerCorrect : WorkerSource → Answer → Prop}
    (translation : SourceTranslation Source WorkerSource Answer
      sourceCorrect workerCorrect)
    (worker : SourceBoundWorker WorkerSource Answer Evidence workerCorrect)
    (source : Source) (hcomplete : worker.CompleteAt (translation.translate source)) :
    (worker.liftTranslation translation).CompleteAt source := by
  rcases hcomplete with ⟨publication, hpublication⟩
  refine ⟨{
    source
    answer := publication.answer
    evidence := publication.evidence
  }, ?_⟩
  dsimp [SourceBoundWorker.liftTranslation]
  rw [hpublication]

/-- A heterogeneous worker erased only after every member has established the
same source-level correctness predicate. -/
structure CertifiedProcedure (Source : Type u) (Answer : Type v)
    (correct : Source → Answer → Prop) where
  procedure : Procedure Source Answer
  sound : ∀ source, SoundAt correct procedure source

def CertifiedProcedure.firstPublish
    {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (workers : List (CertifiedProcedure Source Answer correct)) :
    Procedure Source Answer where
  run source := Certification.firstPublish
    (workers.map CertifiedProcedure.procedure) source

theorem CertifiedProcedure.firstPublish_sound
    {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (workers : List (CertifiedProcedure Source Answer correct)) :
    Sound correct (CertifiedProcedure.firstPublish workers) := by
  intro source answer hrun
  apply Certification.firstPublish_soundAt correct
    (workers.map CertifiedProcedure.procedure) source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, hworker, rfl⟩
    exact worker.sound source
  · exact hrun

/-- Coverage is an explicit semantic obligation, never inferred from a route
tag or from a worker merely terminating. -/
def CertifiedProcedure.Covers
    {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (workers : List (CertifiedProcedure Source Answer correct))
    (source : Source) : Prop :=
  ∃ worker ∈ workers, Certification.CompleteAt correct worker.procedure source

theorem CertifiedProcedure.firstPublish_complete
    {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (workers : List (CertifiedProcedure Source Answer correct))
    (coverage : ∀ source, CertifiedProcedure.Covers workers source) :
    ∀ source, Certification.CompleteAt correct
      (CertifiedProcedure.firstPublish workers) source := by
  intro source
  apply Certification.firstPublish_completeAt correct
    (workers.map CertifiedProcedure.procedure) source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, hworker, rfl⟩
    exact worker.sound source
  · rcases coverage source with ⟨worker, hmember, hcomplete⟩
    exact ⟨worker.procedure, List.mem_map.mpr ⟨worker, hmember, rfl⟩, hcomplete⟩

/-- The automatic router may inspect a profile, but its selected leaves already
carry source-level soundness.  Profile mistakes can therefore affect coverage
or performance, never turn an unchecked publication into an answer. -/
structure AutomaticRouter (Profile : Type w) (Source : Type u) (Answer : Type v)
    (correct : Source → Answer → Prop) where
  profile : Source → Profile
  select : Profile → List (CertifiedProcedure Source Answer correct)
  coverage : ∀ source,
    CertifiedProcedure.Covers (select (profile source)) source

def AutomaticRouter.run
    {Profile : Type w} {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (router : AutomaticRouter Profile Source Answer correct) :
    Procedure Source Answer where
  run source := Certification.firstPublish
    ((router.select (router.profile source)).map CertifiedProcedure.procedure)
    source

theorem AutomaticRouter.sound
    {Profile : Type w} {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (router : AutomaticRouter Profile Source Answer correct) :
    Sound correct router.run := by
  intro source answer hrun
  apply Certification.firstPublish_soundAt correct
    ((router.select (router.profile source)).map CertifiedProcedure.procedure)
    source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, hworker, rfl⟩
    exact worker.sound source
  · exact hrun

theorem AutomaticRouter.complete
    {Profile : Type w} {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (router : AutomaticRouter Profile Source Answer correct) :
    ∀ source, Certification.CompleteAt correct router.run source := by
  intro source
  apply Certification.firstPublish_completeAt correct
    ((router.select (router.profile source)).map CertifiedProcedure.procedure)
    source
  · intro procedure hmember
    simp only [List.mem_map] at hmember
    rcases hmember with ⟨worker, hworker, rfl⟩
    exact worker.sound source
  · rcases router.coverage source with ⟨worker, hmember, hcomplete⟩
    exact ⟨worker.procedure, List.mem_map.mpr ⟨worker, hmember, rfl⟩, hcomplete⟩

/-- The integrated publication theorem: every answer returned by a covered
automatic route is exact, and every routed source receives such an answer. -/
theorem AutomaticRouter.sound_and_complete
    {Profile : Type w} {Source : Type u} {Answer : Type v}
    {correct : Source → Answer → Prop}
    (router : AutomaticRouter Profile Source Answer correct) :
    (∀ source answer, router.run.run source = .publish answer →
      correct source answer) ∧
    (∀ source, ∃ answer, router.run.run source = .publish answer ∧
      correct source answer) := by
  exact ⟨router.sound, router.complete⟩

#print axioms SourceBoundWorker.erase_soundAt
#print axioms SourceBoundWorker.erase_completeAt
#print axioms SourceBoundWorker.liftTranslation
#print axioms SourceBoundWorker.liftTranslation_completeAt
#print axioms CertifiedProcedure.firstPublish_sound
#print axioms CertifiedProcedure.firstPublish_complete
#print axioms AutomaticRouter.sound
#print axioms AutomaticRouter.complete
#print axioms AutomaticRouter.sound_and_complete

end ContextCalculus.CertifiedRouting
