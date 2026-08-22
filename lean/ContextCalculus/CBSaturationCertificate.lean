import ContextCalculus.Equivalence

/-!
# Executable certificates for finite CB saturations

This module checks the semantic core of a production CB terminal state. An
accepted document contains a sequential resolution derivation, retains every
input clause, and is closed under every ground resolution inference over its
finite atom vocabulary. The checker proves `Equiv.Saturation`, so the accepted
terminal set has exactly the same models and semantic consequences as its input.

This is the ground saturation component of the production CB boundary. The
later context-refinement wire must prove that the Rust contexts and messages
decode to such finite saturations and that the checked taxonomy is their exact
publication.
-/

namespace ContextCalculus.CBCert

open ContextCalculus.PropRes
open ContextCalculus.Equiv

variable {n : Nat}

abbrev Atom (n : Nat) := Fin n
abbrev Clause (n : Nat) := PClause (Atom n)

/-- One independently checkable derivation justification. -/
inductive Justification (n : Nat) where
  | premise (index : Nat)
  | resolve (positive negative : Nat) (atom : Atom n)
deriving DecidableEq, Repr

/-- One clause and the justification that derives it. -/
structure Entry (n : Nat) where
  clause : Clause n
  justification : Justification n
deriving DecidableEq

/-- Check one entry against the source premises and the already accepted
entries. References are therefore acyclic by construction. -/
def stepOk (premises : List (Clause n)) (done : List (Clause n))
    (entry : Entry n) : Bool :=
  match entry.justification with
  | .premise index =>
      match premises[index]? with
      | some source => decide (entry.clause = source)
      | none => false
  | .resolve positive negative atom =>
      match done[positive]?, done[negative]? with
      | some left, some right =>
          decide (atom ∈ left.pos) && decide (atom ∈ right.neg) &&
            decide (entry.clause = PropRes.resolvent left right atom)
      | _, _ => false

/-- Validate the trace while retaining the clauses accepted so far. -/
def checkFold (premises : List (Clause n)) :
    List (Clause n) → List (Entry n) → Option (List (Clause n))
  | done, [] => some done
  | done, entry :: rest =>
      if stepOk premises done entry then
        checkFold premises (done ++ [entry.clause]) rest
      else
        none

theorem stepOk_derivable (premises done : List (Clause n))
    (hdone : ∀ clause ∈ done, Derivable premises.toFinset clause)
    (entry : Entry n) (hcheck : stepOk premises done entry = true) :
    Derivable premises.toFinset entry.clause := by
  rcases entry with ⟨clause, justification⟩
  cases hjust : justification with
  | premise index =>
      simp only [stepOk, hjust] at hcheck
      cases hsource : premises[index]? with
      | none => simp [hsource] at hcheck
      | some source =>
          rw [hsource] at hcheck
          simp only [decide_eq_true_eq] at hcheck
          subst clause
          exact Derivable.premise (by
            simp only [List.mem_toFinset]
            exact List.mem_of_getElem? hsource)
  | resolve positive negative atom =>
      simp only [stepOk, hjust] at hcheck
      cases hleft : done[positive]? with
      | none => simp [hleft] at hcheck
      | some left =>
          cases hright : done[negative]? with
          | none => simp [hleft, hright] at hcheck
          | some right =>
              rw [hleft, hright] at hcheck
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
              rcases hcheck with ⟨⟨hpos, hneg⟩, heq⟩
              subst clause
              exact Derivable.resolve
                (hdone left (List.mem_of_getElem? hleft))
                (hdone right (List.mem_of_getElem? hright)) hpos hneg

theorem checkFold_derivable (premises : List (Clause n)) :
    ∀ {done : List (Clause n)} {trace : List (Entry n)}
      {final : List (Clause n)},
      (∀ clause ∈ done, Derivable premises.toFinset clause) →
      checkFold premises done trace = some final →
      ∀ clause ∈ final, Derivable premises.toFinset clause := by
  intro done trace
  induction trace generalizing done with
  | nil =>
      intro final hdone hcheck
      simp only [checkFold, Option.some.injEq] at hcheck
      subst final
      exact hdone
  | cons entry rest ih =>
      intro final hdone hcheck
      simp only [checkFold] at hcheck
      by_cases hstep : stepOk premises done entry
      · rw [if_pos hstep] at hcheck
        have hentry := stepOk_derivable premises done hdone entry hstep
        apply ih (done := done ++ [entry.clause])
        · intro clause hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hdone clause hmem
          · simp only [List.mem_singleton] at hmem
            subst clause
            exact hentry
        · exact hcheck
      · rw [if_neg hstep] at hcheck
        contradiction

/-- Full closure under the finite ground resolution rule. -/
def ResolutionClosed (clauses : Finset (Clause n)) : Prop :=
  ∀ left ∈ clauses, ∀ right ∈ clauses, ∀ atom : Atom n,
    atom ∈ left.pos → atom ∈ right.neg →
      PropRes.resolvent left right atom ∈ clauses

def checkResolutionClosed (clauses : List (Clause n)) : Bool :=
  clauses.all fun left =>
    clauses.all fun right =>
      (List.finRange n).all fun atom =>
        if atom ∈ left.pos ∧ atom ∈ right.neg then
          decide (PropRes.resolvent left right atom ∈ clauses)
        else
          true

theorem checkResolutionClosed_eq_true_iff (clauses : List (Clause n)) :
    checkResolutionClosed clauses = true ↔ ResolutionClosed clauses.toFinset := by
  simp only [checkResolutionClosed, List.all_eq_true]
  constructor
  · intro h left hleft right hright atom hpos hneg
    have hresult := h left (by simpa only [List.mem_toFinset] using hleft)
      right (by simpa only [List.mem_toFinset] using hright)
      atom (List.mem_finRange atom)
    simp only [hpos, hneg, and_self, if_true, decide_eq_true_eq] at hresult
    simpa only [List.mem_toFinset] using hresult
  · intro h left hleft right hright atom hatom
    by_cases hpremise : atom ∈ left.pos ∧ atom ∈ right.neg
    · rw [if_pos hpremise]
      exact decide_eq_true (by
        simpa only [List.mem_toFinset] using
          h left (by simpa only [List.mem_toFinset] using hleft)
            right (by simpa only [List.mem_toFinset] using hright)
            atom hpremise.1 hpremise.2)
    · rw [if_neg hpremise]

/-- A complete finite certificate. `trace` is both the derivation and the
terminal clause set; this prevents an unchecked clause from entering closure. -/
structure Certificate (n : Nat) where
  premises : List (Clause n)
  trace : List (Entry n)

def Certificate.check (certificate : Certificate n) : Bool :=
  match checkFold certificate.premises [] certificate.trace with
  | none => false
  | some terminal =>
      decide (certificate.premises.toFinset ⊆ terminal.toFinset) &&
        checkResolutionClosed terminal

def Certificate.terminal (certificate : Certificate n) : Finset (Clause n) :=
  (certificate.trace.map Entry.clause).toFinset

theorem checkFold_eq_traceClauses (premises : List (Clause n)) :
    ∀ {done : List (Clause n)} {trace : List (Entry n)}
      {final : List (Clause n)},
      checkFold premises done trace = some final →
      final = done ++ trace.map Entry.clause := by
  intro done trace
  induction trace generalizing done with
  | nil =>
      intro final hcheck
      simp only [checkFold, Option.some.injEq] at hcheck
      subst final
      simp
  | cons entry rest ih =>
      intro final hcheck
      simp only [checkFold] at hcheck
      by_cases hstep : stepOk premises done entry
      · rw [if_pos hstep] at hcheck
        rw [ih hcheck]
        simp only [List.map_cons, List.append_assoc, List.singleton_append]
      · rw [if_neg hstep] at hcheck
        contradiction

/-- Main checker theorem: acceptance produces the exact abstract saturation
contract consumed by `Equiv.saturation_models_iff` and
`Equiv.saturation_entails_iff`. -/
theorem Certificate.check_saturation (certificate : Certificate n)
    (hcheck : certificate.check = true) :
    Saturation certificate.premises.toFinset certificate.terminal := by
  unfold Certificate.check at hcheck
  cases hfold : checkFold certificate.premises [] certificate.trace with
  | none => simp [hfold] at hcheck
  | some terminal =>
      rw [hfold] at hcheck
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        checkResolutionClosed_eq_true_iff] at hcheck
      rcases hcheck with ⟨hincl, hclosed⟩
      have hterminal : terminal.toFinset = certificate.terminal := by
        have heq := checkFold_eq_traceClauses certificate.premises hfold
        simp only [List.nil_append] at heq
        rw [Certificate.terminal, ← heq]
      constructor
      · simpa [hterminal] using hincl
      · intro left right atom hleft hright hpos hneg
        rw [← hterminal] at hleft hright ⊢
        exact hclosed left hleft right hright atom hpos hneg
      · intro clause hclause
        rw [← hterminal] at hclause
        exact checkFold_derivable certificate.premises
          (by intro clause hmem; cases hmem) hfold clause
          (by simpa only [List.mem_toFinset] using hclause)

theorem Certificate.check_models_iff (certificate : Certificate n)
    (hcheck : certificate.check = true) (interpretation : Atom n → Prop) :
    Models certificate.terminal interpretation ↔
      Models certificate.premises.toFinset interpretation :=
  saturation_models_iff (certificate.check_saturation hcheck) interpretation

theorem Certificate.check_entails_iff (certificate : Certificate n)
    (hcheck : certificate.check = true) (target : Clause n) :
    (∀ interpretation,
        Models certificate.premises.toFinset interpretation →
          target.sat interpretation) ↔
      (∀ interpretation,
        Models certificate.terminal interpretation →
          target.sat interpretation) :=
  saturation_entails_iff (certificate.check_saturation hcheck) target

/-! ## Executable acceptance and tampering examples -/

private def exampleP : Atom 2 := ⟨0, by omega⟩
private def exampleQ : Atom 2 := ⟨1, by omega⟩

private def exampleFact : Clause 2 := ⟨∅, {exampleP}⟩
private def exampleRule : Clause 2 := ⟨{exampleP}, {exampleQ}⟩
private def exampleConclusion : Clause 2 := ⟨∅, {exampleQ}⟩

private def acceptedExample : Certificate 2 where
  premises := [exampleFact, exampleRule]
  trace :=
    [ ⟨exampleFact, .premise 0⟩
    , ⟨exampleRule, .premise 1⟩
    , ⟨exampleConclusion, .resolve 0 1 exampleP⟩ ]

/-- The complete retained saturation is accepted. -/
example : acceptedExample.check = true := by native_decide

private def missingResolventExample : Certificate 2 where
  premises := [exampleFact, exampleRule]
  trace :=
    [ ⟨exampleFact, .premise 0⟩
    , ⟨exampleRule, .premise 1⟩ ]

/-- Omitting an applicable resolvent violates terminal closure. -/
example : missingResolventExample.check = false := by native_decide

private def forgedDerivationExample : Certificate 2 where
  premises := [exampleFact, exampleRule]
  trace :=
    [ ⟨exampleFact, .premise 0⟩
    , ⟨exampleRule, .premise 1⟩
    , ⟨exampleConclusion, .premise 0⟩ ]

/-- A forged premise reference cannot introduce the missing conclusion. -/
example : forgedDerivationExample.check = false := by native_decide

#print axioms Certificate.check_saturation
#print axioms Certificate.check_models_iff
#print axioms Certificate.check_entails_iff

end ContextCalculus.CBCert
