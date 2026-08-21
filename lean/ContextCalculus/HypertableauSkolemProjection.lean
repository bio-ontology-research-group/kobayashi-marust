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

end ContextCalculus.Hypertableau
