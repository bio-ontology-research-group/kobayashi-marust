import ContextCalculus.HTCheckerTermEmbedding
import ContextCalculus.HypertableauCardinalityProjection
import Mathlib.Data.Nat.Pairing

/-!
# Cardinality frontend clauses in the common proper-term source

This module reconstructs the clauses erased when the HT worker turns frontend
cardinality families into first-class definitions.  Function identifiers are
derived from both the definition slot and witness slot, so witnesses belonging
to different definitions cannot alias at the source-language boundary.

The first layer below covers a minimum-cardinality expansion exactly: for every
witness it emits the role and filler clauses, and for every ordered witness pair
it emits the required disequality clause.  The semantic theorem is pointwise in
the definition slot and therefore composes without trusting serialized names.
-/

namespace ContextCalculus.HTCardinalityCheckerTermEmbedding

open ContextCalculus
open ContextCalculus.CheckerTerm
open ContextCalculus.Hypertableau

def sourceTerm : FTerm := .var 0

def minimumFunctionCode (definitionSlot witnessSlot : Nat) : Nat :=
  Nat.pair definitionSlot witnessSlot

def minimumWitnessTerm (definitionSlot : Nat) (witnessSlot : Nat) : FTerm :=
  .app (minimumFunctionCode definitionSlot witnessSlot) sourceTerm

def minimumRoleClause (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) (witnessSlot : Nat) : FCL := {
  body := [.P (.concept definition.marker sourceTerm)]
  head := [.P (.role definition.role sourceTerm
    (minimumWitnessTerm definitionSlot witnessSlot))]
}

def minimumFillerClause (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) (witnessSlot : Nat) : FCL := {
  body := [.P (.concept definition.marker sourceTerm)]
  head := [.P (.concept definition.filler
    (minimumWitnessTerm definitionSlot witnessSlot))]
}

def minimumDistinctClause (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) (left right : Nat) : FCL := {
  body := [.P (.concept definition.marker sourceTerm)]
  head := [.ineq (minimumWitnessTerm definitionSlot left)
    (minimumWitnessTerm definitionSlot right)]
}

def minimumWitnessClauses (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) : List FCL :=
  (List.range definition.bound).flatMap fun witnessSlot =>
    [minimumRoleClause definitionSlot definition witnessSlot,
      minimumFillerClause definitionSlot definition witnessSlot]

def minimumDistinctClauses (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) : List FCL :=
  (List.range definition.bound).flatMap fun left =>
    (List.range definition.bound).filterMap fun right =>
      if left < right then
        some (minimumDistinctClause definitionSlot definition left right)
      else none

def minimumClauses (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) : List FCL :=
  minimumWitnessClauses definitionSlot definition ++
    minimumDistinctClauses definitionSlot definition

def minimumFunctions (model : TModel Domain) (definitionSlot : Nat)
    (definition : CardinalityDef Nat Nat) :
    MinimumSkolemInterp Domain definition.bound :=
  fun witness source =>
    model.fn (minimumFunctionCode definitionSlot witness.val) source

@[simp] theorem eval_minimumWitnessTerm (model : TModel Domain)
    (assignment : Int → Domain) (definitionSlot witnessSlot : Nat) :
    model.evalT assignment (minimumWitnessTerm definitionSlot witnessSlot) =
      model.fn (minimumFunctionCode definitionSlot witnessSlot) (assignment 0) :=
  rfl

private theorem mem_filterMap_if_lt {α : Type} {f : Nat → α}
    {value : α} {bound : Nat} :
    value ∈ (List.range bound).filterMap
        (fun right => if left < right then some (f right) else none) ↔
      ∃ right < bound, left < right ∧ value = f right := by
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨right, hright, hif⟩
    split at hif
    · injection hif with hvalue
      exact ⟨right, hright, by assumption, hvalue.symm⟩
    · contradiction
  · rintro ⟨right, hright, hlt, rfl⟩
    exact ⟨right, hright, by simp [hlt]⟩

theorem valid_minimumRoleClause_iff (model : TModel Domain)
    (definitionSlot witnessSlot : Nat)
    (definition : CardinalityDef Nat Nat) :
    valid model (minimumRoleClause definitionSlot definition witnessSlot) ↔
      ∀ source, model.conc definition.marker source →
        model.rol definition.role source
          (model.fn (minimumFunctionCode definitionSlot witnessSlot) source) := by
  constructor
  · intro hvalid source hmarker
    let assignment : Int → Domain := fun _ => source
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [minimumRoleClause, List.mem_singleton] at hliteral
      subst literal
      exact hmarker) with ⟨literal, hmem, htrue⟩
    simp only [minimumRoleClause, List.mem_singleton] at hmem
    subst literal
    exact htrue
  · intro hmodels assignment hbody
    refine ⟨.P (.role definition.role sourceTerm
      (minimumWitnessTerm definitionSlot witnessSlot)), by simp [minimumRoleClause], ?_⟩
    apply hmodels (assignment 0)
    exact hbody (.P (.concept definition.marker sourceTerm))
      (by simp [minimumRoleClause])

theorem valid_minimumFillerClause_iff (model : TModel Domain)
    (definitionSlot witnessSlot : Nat)
    (definition : CardinalityDef Nat Nat) :
    valid model (minimumFillerClause definitionSlot definition witnessSlot) ↔
      ∀ source, model.conc definition.marker source →
        model.conc definition.filler
          (model.fn (minimumFunctionCode definitionSlot witnessSlot) source) := by
  constructor
  · intro hvalid source hmarker
    let assignment : Int → Domain := fun _ => source
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [minimumFillerClause, List.mem_singleton] at hliteral
      subst literal
      exact hmarker) with ⟨literal, hmem, htrue⟩
    simp only [minimumFillerClause, List.mem_singleton] at hmem
    subst literal
    exact htrue
  · intro hmodels assignment hbody
    refine ⟨.P (.concept definition.filler
      (minimumWitnessTerm definitionSlot witnessSlot)),
      by simp [minimumFillerClause], ?_⟩
    apply hmodels (assignment 0)
    exact hbody (.P (.concept definition.marker sourceTerm))
      (by simp [minimumFillerClause])

theorem valid_minimumDistinctClause_iff (model : TModel Domain)
    (definitionSlot left right : Nat)
    (definition : CardinalityDef Nat Nat) :
    valid model (minimumDistinctClause definitionSlot definition left right) ↔
      ∀ source, model.conc definition.marker source →
        model.fn (minimumFunctionCode definitionSlot left) source ≠
          model.fn (minimumFunctionCode definitionSlot right) source := by
  constructor
  · intro hvalid source hmarker
    let assignment : Int → Domain := fun _ => source
    rcases hvalid assignment (by
      intro literal hliteral
      simp only [minimumDistinctClause, List.mem_singleton] at hliteral
      subst literal
      exact hmarker) with ⟨literal, hmem, htrue⟩
    simp only [minimumDistinctClause, List.mem_singleton] at hmem
    subst literal
    exact htrue
  · intro hmodels assignment hbody
    refine ⟨.ineq (minimumWitnessTerm definitionSlot left)
      (minimumWitnessTerm definitionSlot right),
      by simp [minimumDistinctClause], ?_⟩
    apply hmodels (assignment 0)
    exact hbody (.P (.concept definition.marker sourceTerm))
      (by simp [minimumDistinctClause])

/-- The emitted proper-term clause family is exactly one minimum-cardinality
Skolem expansion, including witness pairwise distinctness. -/
theorem models_minimumClauses_iff (model : TModel Domain)
    (definitionSlot : Nat) (definition : CardinalityDef Nat Nat) :
    (∀ clause ∈ minimumClauses definitionSlot definition, valid model clause) ↔
      ModelsMinimumExpansion (HTCheckerTermEmbedding.htInterp model) definition
        (minimumFunctions model definitionSlot definition) := by
  constructor
  · intro hclauses source hmarker
    constructor
    · intro witness
      have hwitness : witness.val ∈ List.range definition.bound := by simp
      constructor
      · exact (valid_minimumRoleClause_iff model definitionSlot witness.val definition).1
          (hclauses _ (by
            simp only [minimumClauses, minimumWitnessClauses, List.mem_append,
              List.mem_flatMap]
            exact Or.inl ⟨witness.val, hwitness, by simp⟩)) source hmarker
      · exact (valid_minimumFillerClause_iff model definitionSlot witness.val definition).1
          (hclauses _ (by
            simp only [minimumClauses, minimumWitnessClauses, List.mem_append,
              List.mem_flatMap]
            exact Or.inl ⟨witness.val, hwitness, by simp⟩)) source hmarker
    · intro left right hequal
      by_contra hne
      have horder : left.val < right.val ∨ right.val < left.val :=
        lt_or_gt_of_ne (Fin.val_ne_of_ne hne)
      rcases horder with hlt | hlt
      · exact (valid_minimumDistinctClause_iff model definitionSlot left.val right.val
          definition).1 (hclauses _ (by
            simp only [minimumClauses, minimumDistinctClauses, List.mem_append,
              List.mem_flatMap]
            refine Or.inr ⟨left.val, by simp, ?_⟩
            exact mem_filterMap_if_lt.mpr ⟨right.val, by simp, hlt, rfl⟩))
          source hmarker hequal
      · exact (valid_minimumDistinctClause_iff model definitionSlot right.val left.val
          definition).1 (hclauses _ (by
            simp only [minimumClauses, minimumDistinctClauses, List.mem_append,
              List.mem_flatMap]
            refine Or.inr ⟨right.val, by simp, ?_⟩
            exact mem_filterMap_if_lt.mpr ⟨left.val, by simp, hlt, rfl⟩))
          source hmarker hequal.symm
  · intro hexpansion clause hclause
    simp only [minimumClauses, List.mem_append] at hclause
    rcases hclause with hwitness | hdistinct
    · simp only [minimumWitnessClauses, List.mem_flatMap] at hwitness
      rcases hwitness with ⟨slot, hslot, hclause⟩
      simp at hclause
      rcases hclause with rfl | rfl
      · apply (valid_minimumRoleClause_iff model definitionSlot slot definition).2
        intro source hmarker
        exact (hexpansion source hmarker).1 ⟨slot, by simpa using hslot⟩ |>.1
      · apply (valid_minimumFillerClause_iff model definitionSlot slot definition).2
        intro source hmarker
        exact (hexpansion source hmarker).1 ⟨slot, by simpa using hslot⟩ |>.2
    · simp only [minimumDistinctClauses, List.mem_flatMap] at hdistinct
      rcases hdistinct with ⟨left, hleft, hclause⟩
      rcases mem_filterMap_if_lt.mp hclause with ⟨right, hright, hlt, rfl⟩
      apply (valid_minimumDistinctClause_iff model definitionSlot left right definition).2
      intro source hmarker hequal
      let leftFin : Fin definition.bound := ⟨left, by simpa using hleft⟩
      let rightFin : Fin definition.bound := ⟨right, by simpa using hright⟩
      have hequalFin :
          minimumFunctions model definitionSlot definition leftFin source =
            minimumFunctions model definitionSlot definition rightFin source := by
        simpa [minimumFunctions, leftFin, rightFin] using hequal
      exact (ne_of_lt hlt) (congrArg Fin.val
        ((hexpansion source hmarker).2 hequalFin))

def maximumTerm : MaximumVariable bound → FTerm
  | none => sourceTerm
  | some witness => .var (Int.ofNat (witness.val + 1))

def maximumAtom : Atom (MaximumVariable bound) Nat Nat → FLit
  | .concept literal node =>
      .P (.concept literal.concept (maximumTerm node))
  | .role role source target =>
      .P (.role role (maximumTerm source) (maximumTerm target))
  | .exists_ role filler source =>
      .P (.role role (maximumTerm source) (maximumTerm source))
  | .eq left right => .eq (maximumTerm left) (maximumTerm right)

def maximumClause (definition : CardinalityDef Nat Nat) : FCL := {
  body := (maximumProjectionClause definition).body.map maximumAtom
  head := (maximumProjectionClause definition).head.map maximumAtom
}

def maximumEnvironment (assignment : Int → Domain) :
    MaximumVariable bound → Domain
  | none => assignment 0
  | some witness => assignment (Int.ofNat (witness.val + 1))

@[simp] theorem eval_maximumTerm (model : TModel Domain)
    (assignment : Int → Domain) (node : MaximumVariable bound) :
    model.evalT assignment (maximumTerm node) =
      maximumEnvironment assignment node := by
  cases node <;> rfl

theorem eval_maximumAtom (model : TModel Domain) (assignment : Int → Domain)
    (atom : Atom (MaximumVariable bound) Nat Nat)
    (hsource : atom ∈ maximumBody marker filler role bound ∨
      atom ∈ maximumHead bound) :
    model.evalL assignment (maximumAtom atom) ↔
      (HTCheckerTermEmbedding.htInterp model).satAtom
        (maximumEnvironment assignment) atom := by
  cases atom with
  | concept literal node =>
      have hpositive : literal.neg = false := by
        rcases hsource with hbody | hhead
        · rw [mem_maximumBody] at hbody
          rcases hbody with hmarker | ⟨_, hrole | hfiller⟩
          · injection hmarker with hliteral _
            cases hliteral
            rfl
          · injection hrole
          · injection hfiller with hliteral _
            cases hliteral
            rfl
        · rw [mem_maximumHead] at hhead
          rcases hhead with ⟨_, _, _, hfalse⟩
          contradiction
      simp [maximumAtom, TModel.evalL, eval_maximumTerm,
        HTCheckerTermEmbedding.htInterp, Interp.satAtom, Interp.satLit, hpositive]
  | role sourceRole source target =>
      simp [maximumAtom, TModel.evalL, eval_maximumTerm,
        HTCheckerTermEmbedding.htInterp, Interp.satAtom]
  | exists_ sourceRole filler source =>
      rcases hsource with hbody | hhead
      · rw [mem_maximumBody] at hbody
        rcases hbody with hfalse | ⟨_, hfalse | hfalse⟩ <;> contradiction
      · rw [mem_maximumHead] at hhead
        rcases hhead with ⟨_, _, _, hfalse⟩
        contradiction
  | eq left right =>
      simp [maximumAtom, TModel.evalL, eval_maximumTerm, Interp.satAtom]

/-- The common proper-term maximum clause is exactly the frontend's universal
pigeonhole clause. -/
theorem valid_maximumClause_iff (model : TModel Domain)
    (definition : CardinalityDef Nat Nat) :
    valid model (maximumClause definition) ↔
      (HTCheckerTermEmbedding.htInterp model).modelsClause
        (maximumProjectionClause definition) := by
  constructor
  · intro hvalid environment hbody
    let assignment : Int → Domain
      | .ofNat 0 => environment none
      | .ofNat (index + 1) =>
          if hindex : index < definition.bound + 1 then
            environment (some ⟨index, hindex⟩)
          else environment none
      | .negSucc _ => environment none
    have hassignment : maximumEnvironment assignment = environment := by
      funext node
      cases node with
      | none => rfl
      | some witness =>
          change assignment (Int.ofNat (witness.val + 1)) = environment (some witness)
          simp only [assignment]
          rw [dif_pos witness.isLt]
    have hbodyCommon : ∀ literal ∈ (maximumClause definition).body,
        model.evalL assignment literal := by
      intro literal hliteral
      rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
      apply (eval_maximumAtom model assignment atom (Or.inl hatom)).2
      rw [hassignment]
      exact hbody atom hatom
    rcases hvalid assignment hbodyCommon with ⟨literal, hliteral, htrue⟩
    rcases List.mem_map.mp hliteral with ⟨atom, hatom, rfl⟩
    refine ⟨atom, hatom, ?_⟩
    have := (eval_maximumAtom (marker := definition.marker)
      (filler := definition.filler) (role := definition.role)
      model assignment atom (Or.inr hatom)).1 htrue
    rw [hassignment] at this
    exact this
  · intro hmodels assignment hbody
    have hbodyHT : ∀ atom ∈ (maximumProjectionClause definition).body,
        (HTCheckerTermEmbedding.htInterp model).satAtom
          (maximumEnvironment assignment) atom := by
      intro atom hatom
      apply (eval_maximumAtom model assignment atom (Or.inl hatom)).1
      exact hbody (maximumAtom atom)
        (List.mem_map.mpr ⟨atom, hatom, rfl⟩)
    rcases hmodels (maximumEnvironment assignment) hbodyHT with
      ⟨atom, hatom, htrue⟩
    refine ⟨maximumAtom atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩, ?_⟩
    exact (eval_maximumAtom (marker := definition.marker)
      (filler := definition.filler) (role := definition.role)
      model assignment atom (Or.inr hatom)).2 htrue

def splitClause (maximum minimum : CardinalityDef Nat Nat) : FCL := {
  body := []
  head := [.P (.concept maximum.marker sourceTerm),
    .P (.concept minimum.marker sourceTerm)]
}

def clashClause (maximum minimum : CardinalityDef Nat Nat) : FCL := {
  body := [.P (.concept maximum.marker sourceTerm),
    .P (.concept minimum.marker sourceTerm)]
  head := []
}

def pairClauses (pair : PairedCardinality Nat Nat) : List FCL :=
  [splitClause pair.maximum pair.minimum,
    clashClause pair.maximum pair.minimum]

theorem valid_splitClause_iff (model : TModel Domain)
    (maximum minimum : CardinalityDef Nat Nat) :
    valid model (splitClause maximum minimum) ↔
      ∀ source, model.conc maximum.marker source ∨
        model.conc minimum.marker source := by
  constructor
  · intro hvalid source
    let assignment : Int → Domain := fun _ => source
    rcases hvalid assignment (by simp [splitClause]) with
      ⟨literal, hliteral, htrue⟩
    simp [splitClause] at hliteral
    rcases hliteral with rfl | rfl
    · exact Or.inl htrue
    · exact Or.inr htrue
  · intro hsplit assignment _
    rcases hsplit (assignment 0) with hmaximum | hminimum
    · exact ⟨.P (.concept maximum.marker sourceTerm),
        by simp [splitClause], hmaximum⟩
    · exact ⟨.P (.concept minimum.marker sourceTerm),
        by simp [splitClause], hminimum⟩

theorem valid_clashClause_iff (model : TModel Domain)
    (maximum minimum : CardinalityDef Nat Nat) :
    valid model (clashClause maximum minimum) ↔
      ∀ source, ¬(model.conc maximum.marker source ∧
        model.conc minimum.marker source) := by
  constructor
  · intro hvalid source hboth
    let assignment : Int → Domain := fun _ => source
    rcases hvalid assignment (by
      intro literal hliteral
      simp [clashClause] at hliteral
      rcases hliteral with rfl | rfl
      · exact hboth.1
      · exact hboth.2) with ⟨literal, hliteral, _⟩
    simp [clashClause] at hliteral
  · intro hclash assignment hbody
    exfalso
    apply hclash (assignment 0)
    constructor
    · exact hbody (.P (.concept maximum.marker sourceTerm))
        (by simp [clashClause])
    · exact hbody (.P (.concept minimum.marker sourceTerm))
        (by simp [clashClause])

/-- The two common-source clauses preserve the exact excluded-middle and clash
theory attached to a checked complementary cardinality pair. -/
theorem models_pairClauses_iff (model : TModel Domain)
    (pair : PairedCardinality Nat Nat) :
    (∀ clause ∈ pairClauses pair, valid model clause) ↔
      (HTCheckerTermEmbedding.htInterp model).models
        (cardinalitySplitTheory pair.maximum pair.minimum) := by
  rw [models_cardinalitySplitTheory_iff]
  constructor
  · intro hclauses source
    constructor
    · exact (valid_splitClause_iff model pair.maximum pair.minimum).1
        (hclauses _ (by simp [pairClauses])) source
    · exact (valid_clashClause_iff model pair.maximum pair.minimum).1
        (hclauses _ (by simp [pairClauses])) source
  · intro hsplit clause hclause
    simp [pairClauses] at hclause
    rcases hclause with rfl | rfl
    · exact (valid_splitClause_iff model pair.maximum pair.minimum).2
        fun source => (hsplit source).1
    · exact (valid_clashClause_iff model pair.maximum pair.minimum).2
        fun source => (hsplit source).2

#print axioms models_minimumClauses_iff
#print axioms valid_maximumClause_iff
#print axioms models_pairClauses_iff

end ContextCalculus.HTCardinalityCheckerTermEmbedding
