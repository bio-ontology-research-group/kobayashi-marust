import ContextCalculus.CBBlockedCarrierWire
import ContextCalculus.CBSaturationWire

/-! Canonical executable finite atom encoding for blocked CB grounding. -/

namespace ContextCalculus.CBFiniteAtomEncoding

open ContextCalculus PropRes Eqv

abbrev GroundAtom (conceptCount roleCount carrierCount : Nat) :=
  GAtom (Fin conceptCount) (Fin roleCount) (Fin carrierCount)

def allAtoms (conceptCount roleCount carrierCount : Nat) :
    List (GroundAtom conceptCount roleCount carrierCount) :=
  ((List.finRange conceptCount).flatMap fun concept =>
    (List.finRange carrierCount).map fun carrier => .con concept carrier) ++
  ((List.finRange roleCount).flatMap fun role =>
    (List.finRange carrierCount).flatMap fun source =>
      (List.finRange carrierCount).map fun target => .rol role source target) ++
  ((List.finRange carrierCount).flatMap fun left =>
    (List.finRange carrierCount).map fun right => .eqa left right)

theorem mem_allAtoms (atom : GroundAtom conceptCount roleCount carrierCount) :
    atom ∈ allAtoms conceptCount roleCount carrierCount := by
  cases atom <;> simp [allAtoms]

def atomIndex (atom : GroundAtom conceptCount roleCount carrierCount) :
    Fin (allAtoms conceptCount roleCount carrierCount).length :=
  ⟨(allAtoms conceptCount roleCount carrierCount).idxOf atom,
    List.idxOf_lt_length_iff.mpr (mem_allAtoms atom)⟩

theorem atomIndex_injective :
    Function.Injective (atomIndex (conceptCount := conceptCount)
      (roleCount := roleCount) (carrierCount := carrierCount)) := by
  intro left right hequal
  have hindex : (allAtoms conceptCount roleCount carrierCount).idxOf left =
      (allAtoms conceptCount roleCount carrierCount).idxOf right :=
    congrArg Fin.val hequal
  exact (List.idxOf_inj (mem_allAtoms left)).mp hindex

def encodeClause
    (clause : PClause (GroundAtom conceptCount roleCount carrierCount)) :
    PClause (Fin (allAtoms conceptCount roleCount carrierCount).length) :=
  ⟨clause.neg.image atomIndex, clause.pos.image atomIndex⟩

theorem mem_encodeClause_neg_iff
    (clause : PClause (GroundAtom conceptCount roleCount carrierCount))
    (index : Fin (allAtoms conceptCount roleCount carrierCount).length) :
    index ∈ (encodeClause clause).neg ↔
      ∃ atom ∈ clause.neg, atomIndex atom = index := by
  simp [encodeClause]

theorem mem_encodeClause_pos_iff
    (clause : PClause (GroundAtom conceptCount roleCount carrierCount))
    (index : Fin (allAtoms conceptCount roleCount carrierCount).length) :
    index ∈ (encodeClause clause).pos ↔
      ∃ atom ∈ clause.pos, atomIndex atom = index := by
  simp [encodeClause]

theorem encodeClause_sat_iff
    (valuation : Fin (allAtoms conceptCount roleCount carrierCount).length → Prop)
    (clause : PClause (GroundAtom conceptCount roleCount carrierCount)) :
    (encodeClause clause).sat valuation ↔
      clause.sat (fun atom => valuation (atomIndex atom)) := by
  constructor
  · intro hencoded hnegative
    obtain ⟨index, hindex, htrue⟩ := hencoded (by
      intro index hindex
      obtain ⟨atom, hatom, rfl⟩ := (mem_encodeClause_neg_iff clause index).mp hindex
      exact hnegative atom hatom)
    obtain ⟨atom, hatom, heq⟩ := (mem_encodeClause_pos_iff clause index).mp hindex
    subst index
    exact ⟨atom, hatom, htrue⟩
  · intro horiginal hnegative
    obtain ⟨atom, hatom, htrue⟩ := horiginal (fun atom hatom =>
      hnegative (atomIndex atom) ((mem_encodeClause_neg_iff clause _).mpr
        ⟨atom, hatom, rfl⟩))
    exact ⟨atomIndex atom,
      (mem_encodeClause_pos_iff clause _).mpr ⟨atom, hatom, rfl⟩, htrue⟩

def encodeSet
    (clauses : Finset (PClause (GroundAtom conceptCount roleCount carrierCount))) :
    Finset (PClause (Fin (allAtoms conceptCount roleCount carrierCount).length)) :=
  clauses.image encodeClause

theorem encodeClause_injective : Function.Injective
    (encodeClause (conceptCount := conceptCount) (roleCount := roleCount)
      (carrierCount := carrierCount)) := by
  intro left right hequal
  cases left with
  | mk leftNeg leftPos =>
    cases right with
    | mk rightNeg rightPos =>
      simp only [encodeClause, PClause.mk.injEq] at hequal ⊢
      constructor
      · exact Finset.image_injective atomIndex_injective hequal.1
      · exact Finset.image_injective atomIndex_injective hequal.2

theorem mem_encodeSet_iff
    (clauses : Finset (PClause (GroundAtom conceptCount roleCount carrierCount)))
    (encoded : PClause (Fin (allAtoms conceptCount roleCount carrierCount).length)) :
    encoded ∈ encodeSet clauses ↔
      ∃ clause ∈ clauses, encodeClause clause = encoded := by
  simp [encodeSet]

theorem models_encodeSet_iff
    (valuation : Fin (allAtoms conceptCount roleCount carrierCount).length → Prop)
    (clauses : Finset (PClause (GroundAtom conceptCount roleCount carrierCount))) :
    (∀ encoded ∈ encodeSet clauses, encoded.sat valuation) ↔
      ∀ clause ∈ clauses,
        clause.sat (fun atom => valuation (atomIndex atom)) := by
  constructor
  · intro hencoded clause hclause
    rw [← encodeClause_sat_iff]
    exact hencoded (encodeClause clause)
      ((mem_encodeSet_iff clauses _).mpr ⟨clause, hclause, rfl⟩)
  · intro horiginal encoded hencoded
    obtain ⟨clause, hclause, rfl⟩ := (mem_encodeSet_iff clauses encoded).mp hencoded
    rw [encodeClause_sat_iff]
    exact horiginal clause hclause

#print axioms atomIndex_injective
#print axioms encodeClause_sat_iff
#print axioms encodeClause_injective
#print axioms models_encodeSet_iff

end ContextCalculus.CBFiniteAtomEncoding
