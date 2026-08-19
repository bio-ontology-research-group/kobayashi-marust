/-!
# Certification contracts for workers, portfolios, races, and routing

This module formalises the control-flow boundary used by `km classify`.
A worker either publishes a complete answer or publishes nothing.  Deferral,
error, and timeout are distinct operational outcomes, but all are fail-closed.

The definitions here do not assert that a Rust worker implements a certified
procedure.  Engine-specific refinement theorems must establish `SoundAt` and
`CompleteAt`.  The results below then compose those theorems through sequential
fallbacks, races, and profile-based routing.
-/

namespace ContextCalculus.Certification

/-- A worker can publish an answer or terminate without publishing one. -/
inductive Outcome (Answer : Type u) where
  | publish (answer : Answer)
  | defer
  | error
  | timeout
  deriving DecidableEq, Repr

/-- The executable boundary of one reasoning procedure. -/
structure Procedure (Input : Type u) (Answer : Type v) where
  run : Input → Outcome Answer

variable {Input : Type u} {Answer : Type v}

/-- `correct i a` means that `a` is the exact semantic answer for `i`. -/
def SoundAt (correct : Input → Answer → Prop)
    (p : Procedure Input Answer) (i : Input) : Prop :=
  ∀ a, p.run i = .publish a → correct i a

/-- A procedure is complete at an input when it publishes an exact answer. -/
def CompleteAt (correct : Input → Answer → Prop)
    (p : Procedure Input Answer) (i : Input) : Prop :=
  ∃ a, p.run i = .publish a ∧ correct i a

def Sound (correct : Input → Answer → Prop) (p : Procedure Input Answer) : Prop :=
  ∀ i, SoundAt correct p i

def CompleteOn (correct : Input → Answer → Prop) (fragment : Input → Prop)
    (p : Procedure Input Answer) : Prop :=
  ∀ i, fragment i → CompleteAt correct p i

/-- Sequential portfolio execution.  Every non-publication falls through. -/
def firstPublish : List (Procedure Input Answer) → Input → Outcome Answer
  | [], _ => .defer
  | p :: ps, i =>
      match p.run i with
      | .publish a => .publish a
      | .defer => firstPublish ps i
      | .error => firstPublish ps i
      | .timeout => firstPublish ps i

theorem firstPublish_soundAt (correct : Input → Answer → Prop)
    (ps : List (Procedure Input Answer)) (i : Input)
    (hs : ∀ p ∈ ps, SoundAt correct p i) :
    ∀ a, firstPublish ps i = .publish a → correct i a := by
  induction ps with
  | nil => simp [firstPublish]
  | cons p ps ih =>
      intro a h
      cases hp : p.run i with
      | publish b =>
          simp [firstPublish, hp] at h
          subst a
          exact hs p (by simp) b hp
      | defer =>
          apply ih (fun q hq => hs q (by simp [hq])) a
          simpa [firstPublish, hp] using h
      | error =>
          apply ih (fun q hq => hs q (by simp [hq])) a
          simpa [firstPublish, hp] using h
      | timeout =>
          apply ih (fun q hq => hs q (by simp [hq])) a
          simpa [firstPublish, hp] using h

theorem firstPublish_preserves_publication
    (ps : List (Procedure Input Answer)) (i : Input)
    (h : ∃ p ∈ ps, ∃ a, p.run i = .publish a) :
    ∃ a, firstPublish ps i = .publish a := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
      cases hp : p.run i with
      | publish a => exact ⟨a, by simp [firstPublish, hp]⟩
      | defer =>
          rcases h with ⟨q, hq, a, ha⟩
          have htail : ∃ q ∈ ps, ∃ a, q.run i = .publish a := by
            refine ⟨q, ?_, a, ha⟩
            rcases List.mem_cons.mp hq with hqp | hq
            · subst q
              simp [hp] at ha
            · exact hq
          rcases ih htail with ⟨a, ha⟩
          exact ⟨a, by simpa [firstPublish, hp] using ha⟩
      | error =>
          rcases h with ⟨q, hq, a, ha⟩
          have htail : ∃ q ∈ ps, ∃ a, q.run i = .publish a := by
            refine ⟨q, ?_, a, ha⟩
            rcases List.mem_cons.mp hq with hqp | hq
            · subst q
              simp [hp] at ha
            · exact hq
          rcases ih htail with ⟨a, ha⟩
          exact ⟨a, by simpa [firstPublish, hp] using ha⟩
      | timeout =>
          rcases h with ⟨q, hq, a, ha⟩
          have htail : ∃ q ∈ ps, ∃ a, q.run i = .publish a := by
            refine ⟨q, ?_, a, ha⟩
            rcases List.mem_cons.mp hq with hqp | hq
            · subst q
              simp [hp] at ha
            · exact hq
          rcases ih htail with ⟨a, ha⟩
          exact ⟨a, by simpa [firstPublish, hp] using ha⟩

/-- A portfolio covers an input when at least one selected worker completes. -/
def CoveredAt (correct : Input → Answer → Prop)
    (ps : List (Procedure Input Answer)) (i : Input) : Prop :=
  ∃ p ∈ ps, CompleteAt correct p i

theorem firstPublish_completeAt (correct : Input → Answer → Prop)
    (ps : List (Procedure Input Answer)) (i : Input)
    (hs : ∀ p ∈ ps, SoundAt correct p i)
    (hc : CoveredAt correct ps i) :
    ∃ a, firstPublish ps i = .publish a ∧ correct i a := by
  rcases hc with ⟨p, hp, a, ha, hcorrect⟩
  have hpub : ∃ a, firstPublish ps i = .publish a :=
    firstPublish_preserves_publication ps i ⟨p, hp, a, ha⟩
  rcases hpub with ⟨out, hout⟩
  exact ⟨out, hout, firstPublish_soundAt correct ps i hs out hout⟩

/-- An operational race over a fixed set of workers. -/
structure Race (Input : Type u) (Answer : Type v) where
  members : List (Procedure Input Answer)
  run : Input → Outcome Answer

/-- Every answer published by the race came from one of its workers. -/
def RaceFaithful (r : Race Input Answer) : Prop :=
  ∀ i a, r.run i = .publish a →
    ∃ p ∈ r.members, p.run i = .publish a

/-- If a worker publishes, the supervisor eventually publishes some answer. -/
def RaceLive (r : Race Input Answer) : Prop :=
  ∀ i, (∃ p ∈ r.members, ∃ a, p.run i = .publish a) →
    ∃ a, r.run i = .publish a

theorem race_soundAt (correct : Input → Answer → Prop)
    (r : Race Input Answer) (i : Input)
    (faithful : RaceFaithful r)
    (hs : ∀ p ∈ r.members, SoundAt correct p i) :
    ∀ a, r.run i = .publish a → correct i a := by
  intro a ha
  rcases faithful i a ha with ⟨p, hp, hpa⟩
  exact hs p hp a hpa

theorem race_completeAt (correct : Input → Answer → Prop)
    (r : Race Input Answer) (i : Input)
    (faithful : RaceFaithful r) (live : RaceLive r)
    (hs : ∀ p ∈ r.members, SoundAt correct p i)
    (hc : CoveredAt correct r.members i) :
    ∃ a, r.run i = .publish a ∧ correct i a := by
  rcases hc with ⟨p, hp, a, ha, _⟩
  rcases live i ⟨p, hp, a, ha⟩ with ⟨out, hout⟩
  exact ⟨out, hout, race_soundAt correct r i faithful hs out hout⟩

/-- Profile-based routing followed by sequential fail-closed fallback. -/
structure Router (Profile : Type w) (Input : Type u) (Answer : Type v) where
  profile : Input → Profile
  select : Profile → List (Procedure Input Answer)

def Router.members (r : Router Profile Input Answer) (i : Input) :=
  r.select (r.profile i)

def Router.run (r : Router Profile Input Answer) (i : Input) : Outcome Answer :=
  firstPublish (r.members i) i

def RouterSound (correct : Input → Answer → Prop)
    (r : Router Profile Input Answer) : Prop :=
  ∀ i p, p ∈ r.members i → SoundAt correct p i

def RouterCoverage (correct : Input → Answer → Prop)
    (r : Router Profile Input Answer) : Prop :=
  ∀ i, CoveredAt correct (r.members i) i

theorem router_sound (correct : Input → Answer → Prop)
    (r : Router Profile Input Answer) (hs : RouterSound correct r) :
    ∀ i a, r.run i = .publish a → correct i a := by
  intro i
  exact firstPublish_soundAt correct (r.members i) i (hs i)

theorem router_complete (correct : Input → Answer → Prop)
    (r : Router Profile Input Answer)
    (hs : RouterSound correct r) (hc : RouterCoverage correct r) :
    ∀ i, ∃ a, r.run i = .publish a ∧ correct i a := by
  intro i
  exact firstPublish_completeAt correct (r.members i) i (hs i) (hc i)

end ContextCalculus.Certification
