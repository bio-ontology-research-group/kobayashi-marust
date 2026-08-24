import ContextCalculus.CBSourceLocalClosure
import ContextCalculus.CompletenessOrderedSubsumption

/-!
# Feature-independent local CB candidate model

Before equality literals receive their first-order meaning, every production
`FLit` is a propositional atom.  At this level KM's local Resolution rule is
exact for concepts, roles, equalities, and inequalities alike.  This module
transports source-bound retained-antichain closure into ordered-resolution
closure and constructs the corresponding candidate valuation.
-/

namespace ContextCalculus.CBLocalPropositionalModel

open ContextCalculus ContextCalculus.CheckerTerm ContextCalculus.PropRes
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBSourceLocalClosure

def rawClause (clause : FCL) : PClause FLit :=
  ⟨clause.body.toFinset, clause.head.toFinset⟩

def rawSet (clauses : List FCL) : Finset (PClause FLit) :=
  (clauses.map rawClause).toFinset

theorem mem_rawSet_iff (clauses : List FCL) (raw : PClause FLit) :
    raw ∈ rawSet clauses ↔ ∃ clause ∈ clauses, rawClause clause = raw := by
  simp [rawSet, eq_comm]

theorem rawClause_sat_iff (valuation : FLit → Prop) (clause : FCL) :
    (rawClause clause).sat valuation ↔ ContextCalculus.sat valuation clause := by
  unfold rawClause PClause.sat ContextCalculus.sat
  simp only [List.mem_toFinset]

theorem rawClause_strengthens {stronger weaker : FCL}
    (hstrengthens : Strengthens stronger weaker) :
    OrdResModulo.Strengthens (rawClause stronger) (rawClause weaker) := by
  constructor
  · intro literal hliteral
    exact List.mem_toFinset.mpr
      (hstrengthens.1 (List.mem_toFinset.mp hliteral))
  · intro literal hliteral
    exact List.mem_toFinset.mpr
      (hstrengthens.2 (List.mem_toFinset.mp hliteral))

theorem toFinset_without (literal : FLit) (literals : List FLit) :
    (without literal literals).toFinset = literals.toFinset.erase literal := by
  ext candidate
  simp [mem_without, and_comm]

theorem rawClause_resolvent (positive negative : FCL) (literal : FLit) :
    rawClause (ContextCalculus.resolvent positive negative literal) =
      PropRes.resolvent (rawClause positive) (rawClause negative) literal := by
  rw [PClause.mk.injEq]
  constructor <;>
    simp [rawClause, ContextCalculus.resolvent, PropRes.resolvent,
      List.toFinset_append, toFinset_without]

theorem exists_raw_strengthening {clauses : List FCL} {candidate : FCL}
    (hretained : ∃ retained ∈ clauses, Strengthens retained candidate) :
    ∃ retainedRaw ∈ rawSet clauses,
      OrdResModulo.Strengthens retainedRaw (rawClause candidate) := by
  obtain ⟨retained, hmember, hstrengthens⟩ := hretained
  exact ⟨rawClause retained,
    (mem_rawSet_iff clauses _).mpr ⟨retained, hmember, rfl⟩,
    rawClause_strengthens hstrengthens⟩

theorem local_raw_resolution_closed (retained : List FCL)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, Strengthens clause candidate) :
    ∀ positiveRaw ∈ rawSet retained, ∀ negativeRaw ∈ rawSet retained,
      ∀ literal : FLit, literal ∈ positiveRaw.pos →
        literal ∈ negativeRaw.neg →
        ∃ retainedRaw ∈ rawSet retained,
          OrdResModulo.Strengthens retainedRaw
            (PropRes.resolvent positiveRaw negativeRaw literal) := by
  intro positiveRaw hpositiveRaw negativeRaw hnegativeRaw literal
    hpositiveLiteral hnegativeLiteral
  obtain ⟨positive, hpositive, rfl⟩ :=
    (mem_rawSet_iff retained positiveRaw).mp hpositiveRaw
  obtain ⟨negative, hnegative, rfl⟩ :=
    (mem_rawSet_iff retained negativeRaw).mp hnegativeRaw
  have hhead : literal ∈ positive.head := List.mem_toFinset.mp hpositiveLiteral
  have hbody : literal ∈ negative.body := List.mem_toFinset.mp hnegativeLiteral
  let candidate := ContextCalculus.resolvent positive negative literal
  have hcandidate : candidate ∈ localResolutionCandidates retained := by
    simp only [localResolutionCandidates, List.mem_flatMap]
    refine ⟨positive, hpositive, negative, hnegative, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨literal, hhead, by simp [hbody, candidate]⟩
  rw [← rawClause_resolvent positive negative literal]
  exact exists_raw_strengthening (hclosed candidate hcandidate)

theorem local_raw_closedModulo [LinearOrder FLit] (retained : List FCL)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, Strengthens clause candidate) :
    OrdResModulo.ClosedModulo (rawSet retained) := by
  intro positive hpositive negative hnegative literal hmax hnegativeLiteral _
  exact local_raw_resolution_closed retained hclosed positive hpositive negative
    hnegative literal hmax.1 hnegativeLiteral

/-- A clash-free locally closed production context has a candidate valuation
for all of its retained clauses, with no feature restriction. -/
theorem local_raw_model [LinearOrder FLit] [WellFoundedLT FLit]
    (retained : List FCL)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, Strengthens clause candidate)
    (hbot : PClause.bot ∉ rawSet retained) :
    ∃ valuation : FLit → Prop,
      ∀ clause ∈ retained, ContextCalculus.sat valuation clause := by
  obtain ⟨valuation, hmodel⟩ := OrdResModulo.ordered_model_exists
    (rawSet retained) (local_raw_closedModulo retained hclosed) hbot
  refine ⟨valuation, ?_⟩
  intro clause hclause
  rw [← rawClause_sat_iff]
  exact hmodel (rawClause clause)
    ((mem_rawSet_iff retained _).mpr ⟨clause, hclause, rfl⟩)

#print axioms rawClause_resolvent
#print axioms local_raw_resolution_closed
#print axioms local_raw_closedModulo
#print axioms local_raw_model

end ContextCalculus.CBLocalPropositionalModel
