import ContextCalculus.CBFiniteOrderAdmissibilityWire
import ContextCalculus.CompletenessEq
import ContextCalculus.CompletenessOrderedSubsumption

/-!
# Ground CB clauses as propositional equality clauses

This module connects the production `FLit` clause language to the ground atom
language used by `CompletenessEq`. Disequality needs polarity-aware handling:
an inequality in a CB body becomes a positive equality atom, while an
inequality in a CB head becomes a negative equality atom. The central theorem
proves exact satisfaction equivalence for every clause and valuation.
-/

namespace ContextCalculus.CBGroundEqualityBridge

open ContextCalculus CheckerTerm PropRes Eqv

abbrev GroundAtom := GAtom Nat Nat FTerm

def positiveAtom? : FLit → Option GroundAtom
  | .P (.concept concept term) => some (.con concept term)
  | .P (.role role source target) => some (.rol role source target)
  | .eq left right => some (.eqa left right)
  | .ineq _ _ => none

def inequalityAtom? : FLit → Option GroundAtom
  | .ineq left right => some (.eqa left right)
  | _ => none

def negativeAtoms (clause : FCL) : List GroundAtom :=
  clause.body.filterMap positiveAtom? ++ clause.head.filterMap inequalityAtom?

def positiveAtoms (clause : FCL) : List GroundAtom :=
  clause.head.filterMap positiveAtom? ++ clause.body.filterMap inequalityAtom?

def groundClause (clause : FCL) : PClause GroundAtom :=
  ⟨(negativeAtoms clause).toFinset, (positiveAtoms clause).toFinset⟩

def evalGroundLiteral (valuation : GroundAtom → Prop) : FLit → Prop
  | .P (.concept concept term) => valuation (.con concept term)
  | .P (.role role source target) => valuation (.rol role source target)
  | .eq left right => valuation (.eqa left right)
  | .ineq left right => ¬ valuation (.eqa left right)

theorem mem_negativeAtoms_iff (clause : FCL) (atom : GroundAtom) :
    atom ∈ negativeAtoms clause ↔
      (∃ literal ∈ clause.body, positiveAtom? literal = some atom) ∨
      (∃ literal ∈ clause.head, inequalityAtom? literal = some atom) := by
  simp [negativeAtoms, List.mem_filterMap]

theorem mem_positiveAtoms_iff (clause : FCL) (atom : GroundAtom) :
    atom ∈ positiveAtoms clause ↔
      (∃ literal ∈ clause.head, positiveAtom? literal = some atom) ∨
      (∃ literal ∈ clause.body, inequalityAtom? literal = some atom) := by
  simp [positiveAtoms, List.mem_filterMap]

/-- Production antichain subsumption is preserved exactly by the
polarity-aware ground-clause translation. -/
theorem groundClause_strengthens {stronger weaker : FCL}
    (hstrengthens : CBProductionTrace.Strengthens stronger weaker) :
    OrdResModulo.Strengthens (groundClause stronger) (groundClause weaker) := by
  constructor
  · intro atom hatom
    rw [show (groundClause stronger).neg =
        (negativeAtoms stronger).toFinset from rfl,
      List.mem_toFinset, mem_negativeAtoms_iff] at hatom
    rw [show (groundClause weaker).neg =
        (negativeAtoms weaker).toFinset from rfl,
      List.mem_toFinset, mem_negativeAtoms_iff]
    rcases hatom with ⟨literal, hliteral, hatom⟩ |
        ⟨literal, hliteral, hatom⟩
    · exact Or.inl ⟨literal, hstrengthens.1 hliteral, hatom⟩
    · exact Or.inr ⟨literal, hstrengthens.2 hliteral, hatom⟩
  · intro atom hatom
    rw [show (groundClause stronger).pos =
        (positiveAtoms stronger).toFinset from rfl,
      List.mem_toFinset, mem_positiveAtoms_iff] at hatom
    rw [show (groundClause weaker).pos =
        (positiveAtoms weaker).toFinset from rfl,
      List.mem_toFinset, mem_positiveAtoms_iff]
    rcases hatom with ⟨literal, hliteral, hatom⟩ |
        ⟨literal, hliteral, hatom⟩
    · exact Or.inl ⟨literal, hstrengthens.2 hliteral, hatom⟩
    · exact Or.inr ⟨literal, hstrengthens.1 hliteral, hatom⟩

theorem positiveAtom_eval {valuation : GroundAtom → Prop}
    {literal : FLit} {atom : GroundAtom}
    (hatom : positiveAtom? literal = some atom) :
    evalGroundLiteral valuation literal ↔ valuation atom := by
  cases literal <;> simp_all [positiveAtom?, evalGroundLiteral]
  next predicate => cases predicate <;> simp_all [positiveAtom?, evalGroundLiteral]

theorem inequalityAtom_eval {valuation : GroundAtom → Prop}
    {literal : FLit} {atom : GroundAtom}
    (hatom : inequalityAtom? literal = some atom) :
    evalGroundLiteral valuation literal ↔ ¬ valuation atom := by
  cases literal <;> simp_all [inequalityAtom?, evalGroundLiteral]

theorem groundClause_sat_iff (valuation : GroundAtom → Prop) (clause : FCL) :
    (groundClause clause).sat valuation ↔
      sat (evalGroundLiteral valuation) clause := by
  constructor
  · intro hground hbody
    by_contra hnoHead
    push_neg at hnoHead
    have hnegative : ∀ atom ∈ (groundClause clause).neg, valuation atom := by
      intro atom hatom
      rw [show (groundClause clause).neg = (negativeAtoms clause).toFinset from rfl,
        List.mem_toFinset, mem_negativeAtoms_iff] at hatom
      rcases hatom with ⟨literal, hliteral, hpositive⟩ |
          ⟨literal, hliteral, hinequality⟩
      · exact (positiveAtom_eval hpositive).mp (hbody literal hliteral)
      · by_contra hfalse
        exact hnoHead literal hliteral
          ((inequalityAtom_eval hinequality).mpr hfalse)
    obtain ⟨atom, hatom, htrue⟩ := hground hnegative
    rw [show (groundClause clause).pos = (positiveAtoms clause).toFinset from rfl,
      List.mem_toFinset, mem_positiveAtoms_iff] at hatom
    rcases hatom with ⟨literal, hliteral, hpositive⟩ |
        ⟨literal, hliteral, hinequality⟩
    · exact hnoHead literal hliteral ((positiveAtom_eval hpositive).mpr htrue)
    · exact (inequalityAtom_eval hinequality).mp
        (hbody literal hliteral) htrue
  · intro hclause hnegative
    by_cases hbody : ∀ literal ∈ clause.body,
        evalGroundLiteral valuation literal
    · obtain ⟨literal, hliteral, htrue⟩ := hclause hbody
      cases hpositive : positiveAtom? literal with
      | some atom =>
          refine ⟨atom, ?_, (positiveAtom_eval hpositive).mp htrue⟩
          rw [show (groundClause clause).pos = (positiveAtoms clause).toFinset from rfl,
            List.mem_toFinset, mem_positiveAtoms_iff]
          exact Or.inl ⟨literal, hliteral, hpositive⟩
      | none =>
          cases literal with
          | P predicate => cases predicate <;> simp [positiveAtom?] at hpositive
          | eq left right => simp [positiveAtom?] at hpositive
          | ineq left right =>
              exact False.elim (htrue (hnegative _ (by
                rw [show (groundClause clause).neg =
                  (negativeAtoms clause).toFinset from rfl,
                  List.mem_toFinset, mem_negativeAtoms_iff]
                exact Or.inr ⟨.ineq left right, hliteral, rfl⟩)))
    · push_neg at hbody
      obtain ⟨literal, hliteral, hfalse⟩ := hbody
      cases hinequality : inequalityAtom? literal with
      | some atom =>
          refine ⟨atom, ?_, ?_⟩
          · rw [show (groundClause clause).pos =
                (positiveAtoms clause).toFinset from rfl,
              List.mem_toFinset, mem_positiveAtoms_iff]
            exact Or.inr ⟨literal, hliteral, hinequality⟩
          · by_contra hatom
            exact hfalse ((inequalityAtom_eval hinequality).mpr hatom)
      | none =>
          cases hpositive : positiveAtom? literal with
          | none =>
              cases literal <;> simp_all [positiveAtom?, inequalityAtom?]
              next predicate => cases predicate <;> simp_all [positiveAtom?, inequalityAtom?]
          | some atom =>
              have hatomNeg : atom ∈ (groundClause clause).neg := by
                rw [show (groundClause clause).neg =
                    (negativeAtoms clause).toFinset from rfl,
                  List.mem_toFinset, mem_negativeAtoms_iff]
                exact Or.inl ⟨literal, hliteral, hpositive⟩
              exact False.elim (hfalse ((positiveAtom_eval hpositive).mpr
                (hnegative atom hatomNeg)))

def groundSet (clauses : List FCL) : Finset (PClause GroundAtom) :=
  (clauses.map groundClause).toFinset

theorem mem_groundSet_iff (clauses : List FCL) (ground : PClause GroundAtom) :
    ground ∈ groundSet clauses ↔ ∃ clause ∈ clauses, groundClause clause = ground := by
  simp [groundSet, eq_comm]

/-- A retained production strengthening becomes a retained strengthening in
the translated ground antichain. -/
theorem exists_ground_strengthening {clauses : List FCL} {candidate : FCL}
    (hretained : ∃ retained ∈ clauses,
      CBProductionTrace.Strengthens retained candidate) :
    ∃ retainedGround ∈ groundSet clauses,
      OrdResModulo.Strengthens retainedGround (groundClause candidate) := by
  obtain ⟨retained, hmember, hstrengthens⟩ := hretained
  exact ⟨groundClause retained,
    (mem_groundSet_iff clauses _).mpr ⟨retained, hmember, rfl⟩,
    groundClause_strengthens hstrengthens⟩

theorem models_groundSet_iff (valuation : GroundAtom → Prop) (clauses : List FCL) :
    (∀ ground ∈ groundSet clauses, ground.sat valuation) ↔
      ∀ clause ∈ clauses, sat (evalGroundLiteral valuation) clause := by
  constructor
  · intro hground clause hclause
    rw [← groundClause_sat_iff]
    exact hground (groundClause clause)
      ((mem_groundSet_iff clauses _).mpr ⟨clause, hclause, rfl⟩)
  · intro hclauses ground hground
    obtain ⟨clause, hclause, rfl⟩ :=
      (mem_groundSet_iff clauses ground).mp hground
    rw [groundClause_sat_iff]
    exact hclauses clause hclause

theorem unsat_groundSet_iff (clauses : List FCL) :
    PropRes.Unsat (groundSet clauses) ↔
      ¬ ∃ valuation : GroundAtom → Prop,
        ∀ clause ∈ clauses, sat (evalGroundLiteral valuation) clause := by
  simp only [PropRes.Unsat, models_groundSet_iff]

/-- The canonical ordered model for a translated production antichain.  The
remaining source-bound CB bridge has to establish `ClosedModulo` from the
checked rule-family closure; it no longer has to reconstruct the model proof. -/
theorem groundSet_model_of_closed [LinearOrder GroundAtom]
    [WellFoundedLT GroundAtom] (clauses : List FCL)
    (hclosed : OrdResModulo.ClosedModulo (groundSet clauses))
    (hbot : PClause.bot ∉ groundSet clauses) :
    ∃ valuation : GroundAtom → Prop,
      ∀ clause ∈ clauses, sat (evalGroundLiteral valuation) clause := by
  obtain ⟨valuation, hmodel⟩ :=
    OrdResModulo.ordered_model_exists (groundSet clauses) hclosed hbot
  exact ⟨valuation, (models_groundSet_iff valuation clauses).mp hmodel⟩

/-- Canonical ordered model when generated tautologies are deleted instead of
being represented in the retained antichain. -/
theorem groundSet_model_of_closedModuloTautology [LinearOrder GroundAtom]
    [WellFoundedLT GroundAtom] (clauses : List FCL)
    (hclosed : OrdResModulo.ClosedModuloTautology (groundSet clauses))
    (hbot : PClause.bot ∉ groundSet clauses) :
    ∃ valuation : GroundAtom → Prop,
      ∀ clause ∈ clauses, sat (evalGroundLiteral valuation) clause := by
  obtain ⟨valuation, hmodel⟩ :=
    OrdResModulo.ordered_model_exists_of_closedModuloTautology
      (groundSet clauses) hclosed hbot
  exact ⟨valuation, (models_groundSet_iff valuation clauses).mp hmodel⟩

#print axioms groundClause_sat_iff
#print axioms groundClause_strengthens
#print axioms exists_ground_strengthening
#print axioms models_groundSet_iff
#print axioms unsat_groundSet_iff
#print axioms groundSet_model_of_closed
#print axioms groundSet_model_of_closedModuloTautology

end ContextCalculus.CBGroundEqualityBridge
