import ContextCalculus.CheckerTerm
import Mathlib.Data.List.FinRange

/-!
# Checked finite countermodels for CB term clauses

An exact CB taxonomy needs evidence for both answers.  Derivation traces prove
positive cells.  This module supplies the other half: an executable finite
model check for the same nested-term semantics used by `CheckerTerm`.

Clause validity is checked over every valuation of the finitely many vars
that actually occur in that clause.  The theorems below prove that this finite
enumeration implies `CheckerTerm.valid`, whose definition quantifies over all
assignments `Int → Domain`.
-/

namespace ContextCalculus.CBFiniteModel

open ContextCalculus CheckerTerm

def varsT : FTerm → List Int
  | .var varId => [varId]
  | .const _ => []
  | .app _ argument => varsT argument

def varsP : FPred → List Int
  | .concept _ term => varsT term
  | .role _ source target => varsT source ++ varsT target

def varsL : FLit → List Int
  | .P predicate => varsP predicate
  | .eq left right => varsT left ++ varsT right
  | .ineq left right => varsT left ++ varsT right

def varsC (clause : FCL) : List Int :=
  (clause.body.flatMap varsL ++ clause.head.flatMap varsL).eraseDups

/-- Two assignments that agree on a term's vars evaluate that term
identically. -/
theorem evalT_eq_of_agree (model : TModel D) (left right : Int → D) :
    ∀ term : FTerm,
      (∀ varId ∈ varsT term, left varId = right varId) →
      model.evalT left term = model.evalT right term := by
  intro term hagree
  induction term with
  | var varId => exact hagree varId (by simp [varsT])
  | const individual => rfl
  | app function argument ih =>
      simp only [TModel.evalT]
      congr 1
      exact ih (by simpa [varsT] using hagree)

theorem evalL_eq_of_agree (model : TModel D) (left right : Int → D)
    (literal : FLit)
    (hagree : ∀ varId ∈ varsL literal,
      left varId = right varId) :
    model.evalL left literal ↔ model.evalL right literal := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept term =>
          simp only [TModel.evalL]
          rw [evalT_eq_of_agree model left right term]
          intro varId hvarId
          exact hagree varId (by simpa [varsL, varsP] using hvarId)
      | role role source target =>
          simp only [TModel.evalL]
          rw [evalT_eq_of_agree model left right source, evalT_eq_of_agree model left right target]
          · intro varId hvarId
            exact hagree varId (by simp [varsL, varsP, hvarId])
          · intro varId hvarId
            exact hagree varId (by simp [varsL, varsP, hvarId])
  | eq leftTerm rightTerm =>
      simp only [TModel.evalL]
      rw [evalT_eq_of_agree model left right leftTerm,
        evalT_eq_of_agree model left right rightTerm]
      · intro varId hvarId
        exact hagree varId (by simp [varsL, hvarId])
      · intro varId hvarId
        exact hagree varId (by simp [varsL, hvarId])
  | ineq leftTerm rightTerm =>
      simp only [TModel.evalL]
      rw [evalT_eq_of_agree model left right leftTerm,
        evalT_eq_of_agree model left right rightTerm]
      · intro varId hvarId
        exact hagree varId (by simp [varsL, hvarId])
      · intro varId hvarId
        exact hagree varId (by simp [varsL, hvarId])

structure FiniteTModel (domainSize : Nat) where
  domain_nonempty : 0 < domainSize
  concept : Nat → Fin domainSize → Bool
  role : Nat → Fin domainSize → Fin domainSize → Bool
  constant : Nat → Fin domainSize
  function : Nat → Fin domainSize → Fin domainSize

def FiniteTModel.toModel (model : FiniteTModel domainSize) :
    TModel (Fin domainSize) where
  conc concept element := model.concept concept element = true
  rol role source target := model.role role source target = true
  const := model.constant
  fn := model.function

def FiniteTModel.evalTB (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) : FTerm → Fin domainSize
  | .var varId => assignment varId
  | .const individual => model.constant individual
  | .app function argument => model.function function (model.evalTB assignment argument)

def FiniteTModel.evalLB (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) : FLit → Bool
  | .P (.concept concept term) => model.concept concept (model.evalTB assignment term)
  | .P (.role role source target) =>
      model.role role (model.evalTB assignment source) (model.evalTB assignment target)
  | .eq left right => model.evalTB assignment left == model.evalTB assignment right
  | .ineq left right => model.evalTB assignment left != model.evalTB assignment right

def FiniteTModel.satB (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) (clause : FCL) : Bool :=
  clause.body.all (model.evalLB assignment) →
    clause.head.any (model.evalLB assignment)

theorem FiniteTModel.evalTB_eq (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) (term : FTerm) :
    model.evalTB assignment term = model.toModel.evalT assignment term := by
  induction term with
  | var => rfl
  | const => rfl
  | app function argument ih => simp [FiniteTModel.evalTB, TModel.evalT, ih,
      FiniteTModel.toModel]

theorem FiniteTModel.evalLB_eq_true_iff (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) (literal : FLit) :
    model.evalLB assignment literal = true ↔ model.toModel.evalL assignment literal := by
  cases literal with
  | P predicate => cases predicate <;> simp [FiniteTModel.evalLB, TModel.evalL,
      FiniteTModel.toModel, model.evalTB_eq]
  | eq => simp [FiniteTModel.evalLB, TModel.evalL, model.evalTB_eq]
  | ineq => simp [FiniteTModel.evalLB, TModel.evalL, model.evalTB_eq]

theorem FiniteTModel.satB_sound (model : FiniteTModel domainSize)
    (assignment : Int → Fin domainSize) (clause : FCL)
    (hcheck : model.satB assignment clause = true) :
    sat (model.toModel.evalL assignment) clause := by
  intro hbody
  have hbodyB : clause.body.all (model.evalLB assignment) = true := by
    simp only [List.all_eq_true]
    intro literal hliteral
    exact (model.evalLB_eq_true_iff assignment literal).2 (hbody literal hliteral)
  have hheadB : clause.head.any (model.evalLB assignment) = true := by
    simpa [FiniteTModel.satB, hbodyB] using hcheck
  simp only [List.any_eq_true] at hheadB
  rcases hheadB with ⟨literal, hliteral, htrue⟩
  exact ⟨literal, hliteral, (model.evalLB_eq_true_iff assignment literal).1 htrue⟩

def assignmentOf (model : FiniteTModel domainSize)
    (vars : List Int) (values : Fin vars.length → Fin domainSize) :
    Int → Fin domainSize := fun varId =>
  if h : varId ∈ vars then values ⟨vars.idxOf varId,
    List.idxOf_lt_length_iff.mpr h⟩ else ⟨0, model.domain_nonempty⟩

/-- Enumerate functions between two finite ordinal types without relying on a
noncomputable `Finset` conversion. -/
def allValues (domainSize : Nat) :
    (width : Nat) → List (Fin width → Fin domainSize)
  | 0 => [fun index => Fin.elim0 index]
  | width + 1 =>
      (List.finRange domainSize).flatMap fun head =>
        (allValues domainSize width).map fun tail =>
          Fin.cases head tail

theorem mem_allValues (domainSize width : Nat)
    (values : Fin width → Fin domainSize) :
    values ∈ allValues domainSize width := by
  induction width with
  | zero =>
      simp only [allValues, List.mem_singleton]
      funext index
      exact Fin.elim0 index
  | succ width ih =>
      simp only [allValues, List.mem_flatMap, List.mem_finRange, true_and,
        List.mem_map]
      refine ⟨values 0, ?_⟩
      let tail : Fin width → Fin domainSize := fun index => values index.succ
      refine ⟨tail, ih tail, ?_⟩
      funext index
      refine Fin.cases ?_ (fun predecessor => ?_) index
      · rfl
      · rfl

def FiniteTModel.satisfiesClauseB (model : FiniteTModel domainSize)
    (clause : FCL) : Bool :=
  (allValues domainSize (varsC clause).length).all
    fun values => model.satB (assignmentOf model (varsC clause) values) clause

def FiniteTModel.modelsB (model : FiniteTModel domainSize)
    (ontology : List FCL) : Bool :=
  ontology.all model.satisfiesClauseB

theorem assignmentOf_agrees (model : FiniteTModel domainSize)
    (vars : List Int) (assignment : Int → Fin domainSize)
    (varId : Int) (hvarId : varId ∈ vars) :
    assignmentOf model vars
      (fun index => assignment (vars.get index)) varId = assignment varId := by
  simp only [assignmentOf, dif_pos hvarId]
  congr 1
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hvarId)

theorem FiniteTModel.satisfiesClauseB_sound
    (model : FiniteTModel domainSize) (clause : FCL)
    (hcheck : model.satisfiesClauseB clause = true) :
    valid model.toModel clause := by
  intro assignment
  let values : Fin (varsC clause).length → Fin domainSize :=
    fun index => assignment ((varsC clause).get index)
  have hall : ∀ candidate ∈ allValues domainSize (varsC clause).length,
      model.satB (assignmentOf model (varsC clause) candidate) clause = true := by
    simpa [FiniteTModel.satisfiesClauseB] using hcheck
  have hfinite : sat (model.toModel.evalL
      (assignmentOf model (varsC clause) values)) clause := by
    exact model.satB_sound _ clause (hall values (mem_allValues _ _ values))
  intro hbody
  have hbodyFinite : ∀ literal ∈ clause.body,
      model.toModel.evalL (assignmentOf model (varsC clause) values) literal := by
    intro literal hliteral
    apply (evalL_eq_of_agree model.toModel assignment
      (assignmentOf model (varsC clause) values) literal ?_).1
    · exact hbody literal hliteral
    · intro varId hvarId
      symm
      apply assignmentOf_agrees
      simp only [varsC, List.mem_eraseDups, List.mem_append,
        List.mem_flatMap]
      exact Or.inl ⟨literal, hliteral, hvarId⟩
  rcases hfinite hbodyFinite with ⟨literal, hliteral, hliteralTrue⟩
  refine ⟨literal, hliteral, ?_⟩
  apply (evalL_eq_of_agree model.toModel assignment
    (assignmentOf model (varsC clause) values) literal ?_).2
  · exact hliteralTrue
  · intro varId hvarId
    symm
    apply assignmentOf_agrees
    simp only [varsC, List.mem_eraseDups, List.mem_append,
      List.mem_flatMap]
    exact Or.inr ⟨literal, hliteral, hvarId⟩

theorem FiniteTModel.modelsB_sound (model : FiniteTModel domainSize)
    (ontology : List FCL) (hcheck : model.modelsB ontology = true) :
    ∀ clause ∈ ontology, valid model.toModel clause := by
  simp only [FiniteTModel.modelsB, List.all_eq_true] at hcheck
  intro clause hclause
  exact model.satisfiesClauseB_sound clause (hcheck clause hclause)

#print axioms FiniteTModel.satisfiesClauseB_sound
#print axioms FiniteTModel.modelsB_sound

end ContextCalculus.CBFiniteModel
