import ContextCalculus.Hypertableau

/-!
# Skolem-pair to hypertableau existential projection

The frontend represents one existential obligation by two clauses sharing a
Skolem function: one asserts the role edge and one asserts the filler on the
same selected value.  `cb_to_ht` replaces that pair by one HT `exists_` head.

This module proves equisatisfiability for the exact production precondition:
both source halves have the same body, source variable, role, filler, and
function.  The body may mention additional variables.  The reverse direction
chooses one witness for each source value whenever any body assignment with
that source value is possible, which proves that the witness can be represented
by a unary Skolem function.
-/

namespace ContextCalculus.Hypertableau

universe u v w x

structure SkolemInterp (Domain : Type u) (Function : Type v) where
  app : Function → Domain → Domain

def HoldsBody (I : Interp Domain Concept Role) (assignment : Variable → Domain)
    (body : List (Atom Variable Concept Role)) : Prop :=
  ∀ atom ∈ body, I.satAtom assignment atom

/-- Semantics of the exact common-body role/filler source pair. -/
def ModelsSkolemPair (I : Interp Domain Concept Role)
    (functions : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (filler : Lit Concept) : Prop :=
  (∀ assignment, HoldsBody I assignment body →
    I.role role (assignment source) (functions.app function (assignment source))) ∧
  (∀ assignment, HoldsBody I assignment body →
    I.satLit filler (functions.app function (assignment source)))

def existentialProjectionClause
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (role : Role) (filler : Lit Concept) : Clause Variable Concept Role := {
  body
  head := [.exists_ role filler source]
}

theorem skolemPair_sound
    (I : Interp Domain Concept Role) (functions : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (filler : Lit Concept)
    (hpair : ModelsSkolemPair I functions body source function role filler) :
    I.modelsClause (existentialProjectionClause body source role filler) := by
  intro assignment hbody
  refine ⟨.exists_ role filler source, by simp [existentialProjectionClause], ?_⟩
  exact ⟨functions.app function (assignment source),
    hpair.1 assignment hbody, hpair.2 assignment hbody⟩

theorem skolemPair_complete [DecidableEq Function]
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (filler : Lit Concept)
    (htarget : I.modelsClause (existentialProjectionClause body source role filler)) :
    ∃ functions : SkolemInterp Domain Function,
      ModelsSkolemPair I functions body source function role filler := by
  classical
  let Trigger (value : Domain) : Prop :=
    ∃ assignment : Variable → Domain,
      assignment source = value ∧ HoldsBody I assignment body
  have witness : ∀ value, Trigger value →
      ∃ target, I.role role value target ∧ I.satLit filler target := by
    intro value htrigger
    rcases htrigger with ⟨assignment, hsource, hbody⟩
    rcases htarget assignment hbody with ⟨atom, hatom, hsat⟩
    simp only [existentialProjectionClause, List.mem_singleton] at hatom
    subst atom
    simpa [Interp.satAtom, hsource] using hsat
  let selected (value : Domain) (htrigger : Trigger value) : Domain :=
    Classical.choose (witness value htrigger)
  let functions : SkolemInterp Domain Function := {
    app := fun candidate value =>
      if candidate = function then
        if htrigger : Trigger value then selected value htrigger
        else base.app candidate value
      else base.app candidate value
  }
  refine ⟨functions, ?_, ?_⟩
  · intro assignment hbody
    have htrigger : Trigger (assignment source) :=
      ⟨assignment, rfl, hbody⟩
    have hselected := Classical.choose_spec (witness (assignment source) htrigger)
    simpa [functions, htrigger, selected] using hselected.1
  · intro assignment hbody
    have htrigger : Trigger (assignment source) :=
      ⟨assignment, rfl, hbody⟩
    have hselected := Classical.choose_spec (witness (assignment source) htrigger)
    simpa [functions, htrigger, selected] using hselected.2

/-- Witness refinement changes only the selected Skolem function.  This is the
composition invariant needed to install finitely many independently named
witness functions in one shared interpretation. -/
theorem skolemPair_complete_preserving [DecidableEq Function]
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (filler : Lit Concept)
    (htarget : I.modelsClause (existentialProjectionClause body source role filler)) :
    ∃ functions : SkolemInterp Domain Function,
      ModelsSkolemPair I functions body source function role filler ∧
      ∀ candidate, candidate ≠ function →
        functions.app candidate = base.app candidate := by
  classical
  let Trigger (value : Domain) : Prop :=
    ∃ assignment : Variable → Domain,
      assignment source = value ∧ HoldsBody I assignment body
  have witness : ∀ value, Trigger value →
      ∃ target, I.role role value target ∧ I.satLit filler target := by
    intro value htrigger
    rcases htrigger with ⟨assignment, hsource, hbody⟩
    rcases htarget assignment hbody with ⟨atom, hatom, hsat⟩
    simp only [existentialProjectionClause, List.mem_singleton] at hatom
    subst atom
    simpa [Interp.satAtom, hsource] using hsat
  let selected (value : Domain) (htrigger : Trigger value) : Domain :=
    Classical.choose (witness value htrigger)
  let functions : SkolemInterp Domain Function := {
    app := fun candidate value =>
      if candidate = function then
        if htrigger : Trigger value then selected value htrigger
        else base.app candidate value
      else base.app candidate value
  }
  refine ⟨functions, ⟨?_, ?_⟩, ?_⟩
  · intro assignment hbody
    have htrigger : Trigger (assignment source) := ⟨assignment, rfl, hbody⟩
    have hselected := Classical.choose_spec (witness (assignment source) htrigger)
    simpa [functions, htrigger, selected] using hselected.1
  · intro assignment hbody
    have htrigger : Trigger (assignment source) := ⟨assignment, rfl, hbody⟩
    have hselected := Classical.choose_spec (witness (assignment source) htrigger)
    simpa [functions, htrigger, selected] using hselected.2
  · intro candidate hne
    funext value
    simp [functions, hne]

structure SkolemPairSpec (Variable Concept Role Function : Type*) where
  body : List (Atom Variable Concept Role)
  source : Variable
  function : Function
  role : Role
  filler : Lit Concept

def SkolemPairSpec.target
    (pair : SkolemPairSpec Variable Concept Role Function) :
    Clause Variable Concept Role :=
  existentialProjectionClause pair.body pair.source pair.role pair.filler

def SkolemPairSpec.models (I : Interp Domain Concept Role)
    (functions : SkolemInterp Domain Function)
    (pair : SkolemPairSpec Variable Concept Role Function) : Prop :=
  ModelsSkolemPair I functions pair.body pair.source pair.function pair.role pair.filler

def ModelsSkolemPairs (I : Interp Domain Concept Role)
    (functions : SkolemInterp Domain Function)
    (pairs : List (SkolemPairSpec Variable Concept Role Function)) : Prop :=
  ∀ pair ∈ pairs, pair.models I functions

def skolemPairFunctions
    (pairs : List (SkolemPairSpec Variable Concept Role Function)) : List Function :=
  pairs.map (·.function)

def skolemProjectionOntology
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function)) :
    List (Clause Variable Concept Role) :=
  direct ++ pairs.map (·.target)

theorem SkolemPairSpec.models_of_app_eq
    (pair : SkolemPairSpec Variable Concept Role Function)
    (I : Interp Domain Concept Role)
    (left right : SkolemInterp Domain Function)
    (heq : left.app pair.function = right.app pair.function)
    (hmodels : pair.models I right) : pair.models I left := by
  constructor
  · intro assignment hbody
    simpa [SkolemPairSpec.models, ModelsSkolemPair, heq] using hmodels.1 assignment hbody
  · intro assignment hbody
    simpa [SkolemPairSpec.models, ModelsSkolemPair, heq] using hmodels.2 assignment hbody

theorem modelsSkolemPairs_sound
    (I : Interp Domain Concept Role) (functions : SkolemInterp Domain Function)
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (hmodels : ModelsSkolemPairs I functions pairs) :
    I.models (pairs.map (·.target)) := by
  intro clause hclause
  rcases List.mem_map.mp hclause with ⟨pair, hpair, rfl⟩
  exact skolemPair_sound I functions pair.body pair.source pair.function pair.role pair.filler
    (hmodels pair hpair)

theorem modelsSkolemPairs_complete [DecidableEq Function]
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function)
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (hunique : (skolemPairFunctions pairs).Nodup)
    (htarget : I.models (pairs.map (·.target))) :
    ∃ functions : SkolemInterp Domain Function,
      ModelsSkolemPairs I functions pairs := by
  induction pairs with
  | nil =>
      exact ⟨base, by simp [ModelsSkolemPairs]⟩
  | cons pair pairs ih =>
      simp only [skolemPairFunctions, List.map_cons, List.nodup_cons] at hunique
      have htail : I.models (pairs.map (·.target)) := by
        intro clause hclause
        exact htarget clause (by simp [hclause])
      rcases ih hunique.2 htail with ⟨tailFunctions, htailModels⟩
      have hhead : I.modelsClause pair.target :=
        htarget pair.target (by simp)
      rcases skolemPair_complete_preserving I tailFunctions pair.body pair.source
          pair.function pair.role pair.filler hhead with
        ⟨functions, hpair, hpreserved⟩
      refine ⟨functions, ?_⟩
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hcandidate
      · exact hpair
      · apply candidate.models_of_app_eq I functions tailFunctions
        · apply hpreserved
          intro heq
          apply hunique.1
          have hcandmem : candidate.function ∈ skolemPairFunctions pairs :=
            List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
          exact heq ▸ hcandmem
        · exact htailModels candidate hcandidate

/-- Whole-list semantic contract for a faithful mixture of untouched HT
clauses and exact, uniquely keyed Skolem-pair projections. -/
theorem mixedSkolemProjection_sat_iff [DecidableEq Function]
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function)
    (direct : List (Clause Variable Concept Role))
    (pairs : List (SkolemPairSpec Variable Concept Role Function))
    (hunique : (skolemPairFunctions pairs).Nodup) :
    (∃ functions : SkolemInterp Domain Function,
      I.models direct ∧ ModelsSkolemPairs I functions pairs) ↔
      I.models (skolemProjectionOntology direct pairs) := by
  constructor
  · rintro ⟨functions, hdirect, hpairs⟩
    intro clause hclause
    rcases List.mem_append.mp hclause with hclause | hclause
    · exact hdirect clause hclause
    · exact modelsSkolemPairs_sound I functions pairs hpairs clause hclause
  · intro htarget
    have hdirect : I.models direct := by
      intro clause hclause
      exact htarget clause (List.mem_append_left _ hclause)
    have hpairs : I.models (pairs.map (·.target)) := by
      intro clause hclause
      exact htarget clause (List.mem_append_right _ hclause)
    rcases modelsSkolemPairs_complete I base pairs hunique hpairs with ⟨functions, hmodels⟩
    exact ⟨functions, hdirect, hmodels⟩

/-- Exact semantic contract for replacing the common-body Skolem pair. -/
theorem skolemPair_sat_iff [DecidableEq Function]
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function)
    (body : List (Atom Variable Concept Role)) (source : Variable)
    (function : Function) (role : Role) (filler : Lit Concept) :
    (∃ functions : SkolemInterp Domain Function,
      ModelsSkolemPair I functions body source function role filler) ↔
      I.modelsClause (existentialProjectionClause body source role filler) := by
  constructor
  · rintro ⟨functions, hpair⟩
    exact skolemPair_sound I functions body source function role filler hpair
  · exact skolemPair_complete I base body source function role filler

#print axioms skolemPair_sound
#print axioms skolemPair_complete
#print axioms skolemPair_sat_iff
#print axioms modelsSkolemPairs_complete
#print axioms mixedSkolemProjection_sat_iff

end ContextCalculus.Hypertableau
