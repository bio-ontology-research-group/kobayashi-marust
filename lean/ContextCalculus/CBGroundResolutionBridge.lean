import ContextCalculus.CBGroundEqualityBridge
import ContextCalculus.CBSourceLocalClosure

/-!
# Production local Resolution as ground resolution

The production rule resolves the same `FLit` from one head and one body.  This
file proves that operation translates exactly to propositional resolution when
the two clauses contain no explicit inequality literals.  Inequalities encode
the negative polarity of equality and therefore belong to the separate
Factor/ordered-paramodulation bridge.
-/

namespace ContextCalculus.CBGroundResolutionBridge

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace ContextCalculus.PropRes
open ContextCalculus.CBGroundEqualityBridge
open ContextCalculus.CBSourceLocalClosure

def InequalityFree (clause : FCL) : Prop :=
  (∀ literal ∈ clause.body, inequalityAtom? literal = none) ∧
  (∀ literal ∈ clause.head, inequalityAtom? literal = none)

def literalOfGroundAtom : GroundAtom → FLit
  | .con concept term => .P (.concept concept term)
  | .rol role source target => .P (.role role source target)
  | .eqa left right => .eq left right

theorem literalOfGroundAtom_positive {literal : FLit} {atom : GroundAtom}
    (hpositive : positiveAtom? literal = some atom) :
    literalOfGroundAtom atom = literal := by
  cases literal with
  | P predicate =>
      cases predicate <;> simp only [positiveAtom?] at hpositive <;>
        cases hpositive <;> rfl
  | eq left right =>
      simp only [positiveAtom?] at hpositive
      cases hpositive
      rfl
  | ineq left right => simp_all [positiveAtom?]

theorem positiveAtom_injective {first second : FLit} {atom : GroundAtom}
    (hfirst : positiveAtom? first = some atom)
    (hsecond : positiveAtom? second = some atom) :
    first = second := by
  rw [← literalOfGroundAtom_positive hfirst,
    ← literalOfGroundAtom_positive hsecond]

theorem positiveAtom_exists_of_inequality_none {literal : FLit}
    (hineq : inequalityAtom? literal = none) :
    ∃ atom, positiveAtom? literal = some atom := by
  cases literal with
  | P predicate => cases predicate <;> simp [positiveAtom?]
  | eq left right => exact ⟨.eqa left right, rfl⟩
  | ineq left right => simp [inequalityAtom?] at hineq

theorem filterMap_positive_without (literals : List FLit) (literal : FLit)
    (atom : GroundAtom) (hliteral : positiveAtom? literal = some atom) :
    ((without literal literals).filterMap positiveAtom?).toFinset =
      (literals.filterMap positiveAtom?).toFinset.erase atom := by
  ext candidate
  constructor
  · intro hcandidate
    simp only [List.mem_toFinset, List.mem_filterMap] at hcandidate
    obtain ⟨source, hsource, hencoded⟩ := hcandidate
    rw [mem_without] at hsource
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro heq
      subst candidate
      exact hsource.2 (positiveAtom_injective hencoded hliteral)
    · rw [List.mem_toFinset, List.mem_filterMap]
      exact ⟨source, hsource.1, hencoded⟩
  · intro hcandidate
    rw [Finset.mem_erase] at hcandidate
    rw [List.mem_toFinset, List.mem_filterMap] at hcandidate
    obtain ⟨hne, source, hsource, hencoded⟩ := hcandidate
    rw [List.mem_toFinset, List.mem_filterMap]
    refine ⟨source, (mem_without).mpr ⟨hsource, ?_⟩, hencoded⟩
    intro heq
    subst source
    exact hne (Option.some.inj (hencoded.symm.trans hliteral))

theorem filterMap_inequality_eq_nil (literals : List FLit)
    (hfree : ∀ literal ∈ literals, inequalityAtom? literal = none) :
    literals.filterMap inequalityAtom? = [] := by
  induction literals with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.mem_cons] at hfree
      simp [hfree first (Or.inl rfl), ih (fun literal hliteral =>
        hfree literal (Or.inr hliteral))]

theorem negativeAtoms_eq (clause : FCL) (hfree : InequalityFree clause) :
    negativeAtoms clause = clause.body.filterMap positiveAtom? := by
  simp [negativeAtoms, filterMap_inequality_eq_nil clause.head hfree.2]

theorem positiveAtoms_eq (clause : FCL) (hfree : InequalityFree clause) :
    positiveAtoms clause = clause.head.filterMap positiveAtom? := by
  simp [positiveAtoms, filterMap_inequality_eq_nil clause.body hfree.1]

theorem resolvent_inequalityFree {positive negative : FCL} {literal : FLit}
    (hpositive : InequalityFree positive) (hnegative : InequalityFree negative)
    (hhead : literal ∈ positive.head) (hbody : literal ∈ negative.body) :
    InequalityFree (ContextCalculus.resolvent positive negative literal) := by
  constructor
  · intro candidate hcandidate
    simp only [ContextCalculus.resolvent, List.mem_append] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · exact hpositive.1 candidate hcandidate
    · exact hnegative.1 candidate (mem_without.mp hcandidate).1
  · intro candidate hcandidate
    simp only [ContextCalculus.resolvent, List.mem_append] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · exact hpositive.2 candidate (mem_without.mp hcandidate).1
    · exact hnegative.2 candidate hcandidate

/-- Exact correspondence for the ordinary local Resolution rule. -/
theorem groundClause_resolvent {positive negative : FCL} {literal : FLit}
    (hpositive : InequalityFree positive) (hnegative : InequalityFree negative)
    (hhead : literal ∈ positive.head) (hbody : literal ∈ negative.body) :
    ∃ atom : GroundAtom,
      positiveAtom? literal = some atom ∧
      groundClause (ContextCalculus.resolvent positive negative literal) =
        PropRes.resolvent (groundClause positive) (groundClause negative) atom := by
  obtain ⟨atom, hatom⟩ := positiveAtom_exists_of_inequality_none
    (hpositive.2 literal hhead)
  refine ⟨atom, hatom, ?_⟩
  have hresfree :=
    resolvent_inequalityFree hpositive hnegative hhead hbody
  rw [PClause.mk.injEq]
  constructor
  · change (negativeAtoms
        (ContextCalculus.resolvent positive negative literal)).toFinset =
      (negativeAtoms positive).toFinset ∪
        (negativeAtoms negative).toFinset.erase atom
    rw [negativeAtoms_eq positive hpositive,
      negativeAtoms_eq negative hnegative,
      negativeAtoms_eq _ hresfree]
    simp only [ContextCalculus.resolvent, List.filterMap_append,
      List.toFinset_append]
    rw [filterMap_positive_without negative.body literal atom hatom]
  · change (positiveAtoms
        (ContextCalculus.resolvent positive negative literal)).toFinset =
      (positiveAtoms positive).toFinset.erase atom ∪
        (positiveAtoms negative).toFinset
    rw [positiveAtoms_eq positive hpositive,
      positiveAtoms_eq negative hnegative,
      positiveAtoms_eq _ hresfree]
    simp only [ContextCalculus.resolvent, List.filterMap_append,
      List.toFinset_append]
    rw [filterMap_positive_without positive.head literal atom hatom]

/-- Source-bound local closure supplies every propositional resolvent of an
inequality-free retained context, modulo the same retained antichain. -/
theorem local_ground_resolution_closed (retained : List FCL)
    (hfree : ∀ clause ∈ retained, InequalityFree clause)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, CBProductionTrace.Strengthens clause candidate) :
    ∀ positiveGround ∈ groundSet retained,
      ∀ negativeGround ∈ groundSet retained, ∀ atom : GroundAtom,
        atom ∈ positiveGround.pos → atom ∈ negativeGround.neg →
        ∃ retainedGround ∈ groundSet retained,
          OrdResModulo.Strengthens retainedGround
            (PropRes.resolvent positiveGround negativeGround atom) := by
  intro positiveGround hpositiveGround negativeGround hnegativeGround atom
    hatomPositive hatomNegative
  obtain ⟨positive, hpositive, rfl⟩ :=
    (mem_groundSet_iff retained positiveGround).mp hpositiveGround
  obtain ⟨negative, hnegative, rfl⟩ :=
    (mem_groundSet_iff retained negativeGround).mp hnegativeGround
  have hpositiveFree := hfree positive hpositive
  have hnegativeFree := hfree negative hnegative
  have hatomPositive' : atom ∈ positiveAtoms positive := by
    exact List.mem_toFinset.mp hatomPositive
  rw [positiveAtoms_eq positive hpositiveFree, List.mem_filterMap] at hatomPositive'
  obtain ⟨positiveLiteral, hpositiveHead, hpositiveAtom⟩ := hatomPositive'
  have hatomNegative' : atom ∈ negativeAtoms negative := by
    exact List.mem_toFinset.mp hatomNegative
  rw [negativeAtoms_eq negative hnegativeFree, List.mem_filterMap] at hatomNegative'
  obtain ⟨negativeLiteral, hnegativeBody, hnegativeAtom⟩ := hatomNegative'
  have hliteral : positiveLiteral = negativeLiteral :=
    positiveAtom_injective hpositiveAtom hnegativeAtom
  subst negativeLiteral
  let candidate := ContextCalculus.resolvent positive negative positiveLiteral
  have hcandidate : candidate ∈ localResolutionCandidates retained := by
    simp only [localResolutionCandidates, List.mem_flatMap]
    refine ⟨positive, hpositive, negative, hnegative, ?_⟩
    rw [List.mem_filterMap]
    refine ⟨positiveLiteral, hpositiveHead, ?_⟩
    simp [hnegativeBody, candidate]
  have hretained := hclosed candidate hcandidate
  obtain ⟨translatedAtom, htranslatedAtom, htranslation⟩ :=
    groundClause_resolvent hpositiveFree hnegativeFree hpositiveHead hnegativeBody
  have hatomsEqual : translatedAtom = atom :=
    Option.some.inj (htranslatedAtom.symm.trans hpositiveAtom)
  subst translatedAtom
  rw [← htranslation]
  exact exists_ground_strengthening hretained

theorem local_ground_closedModulo [LinearOrder GroundAtom]
    (retained : List FCL)
    (hfree : ∀ clause ∈ retained, InequalityFree clause)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, CBProductionTrace.Strengthens clause candidate) :
    OrdResModulo.ClosedModulo (groundSet retained) := by
  intro positive hpositive negative hnegative atom hmax hnegativeAtom _
  exact local_ground_resolution_closed retained hfree hclosed positive hpositive
    negative hnegative atom hmax.1 hnegativeAtom

/-- Canonical valuation for a clash-free, source-checked local production
context on the inequality-free slice. -/
theorem local_ground_model [LinearOrder GroundAtom] [WellFoundedLT GroundAtom]
    (retained : List FCL)
    (hfree : ∀ clause ∈ retained, InequalityFree clause)
    (hclosed : ∀ candidate ∈ localResolutionCandidates retained,
      ∃ clause ∈ retained, CBProductionTrace.Strengthens clause candidate)
    (hbot : PClause.bot ∉ groundSet retained) :
    ∃ valuation : GroundAtom → Prop,
      ∀ clause ∈ retained, sat (evalGroundLiteral valuation) clause :=
  groundSet_model_of_closed retained
    (local_ground_closedModulo retained hfree hclosed) hbot

#print axioms positiveAtom_injective
#print axioms filterMap_positive_without
#print axioms groundClause_resolvent
#print axioms local_ground_resolution_closed
#print axioms local_ground_closedModulo
#print axioms local_ground_model

end ContextCalculus.CBGroundResolutionBridge
