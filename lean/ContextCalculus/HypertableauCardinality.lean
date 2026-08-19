import ContextCalculus.HypertableauEqualityModel

/-!
# First-class cardinality semantics for hypertableau certificates

This module gives the semantic contract for the `card_defs` side channel used
by KM's hypertableau.  It deliberately states cardinality over arbitrary
domains, without a unique-name assumption.  Equality-aware certificates will
check these definitions in the canonical quotient model.
-/

namespace ContextCalculus.Hypertableau

universe u

/-- A predicate has at least `n` distinct witnesses. -/
def HasAtLeast (n : Nat) (predicate : Domain → Prop) : Prop :=
  ∃ witnesses : Fin n → Domain,
    Function.Injective witnesses ∧ ∀ index, predicate (witnesses index)

/-- A predicate has at most `n` witnesses.  The negative formulation matches
the tableau's `n + 1` successor merge rule and remains valid on quotient
domains. -/
def HasAtMost (n : Nat) (predicate : Domain → Prop) : Prop :=
  ¬HasAtLeast (n + 1) predicate

theorem hasAtLeast_zero (predicate : Domain → Prop) : HasAtLeast 0 predicate := by
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro left
    exact Fin.elim0 left
  · intro index
    exact Fin.elim0 index

theorem hasAtMost_iff_not_hasAtLeast_succ
    (n : Nat) (predicate : Domain → Prop) :
    HasAtMost n predicate ↔ ¬HasAtLeast (n + 1) predicate :=
  Iff.rfl

theorem not_injective_of_hasAtMost
    {Domain : Type u} {n : Nat} {predicate : Domain → Prop}
    (hbound : HasAtMost n predicate)
    (witnesses : Fin (n + 1) → Domain)
    (hpredicate : ∀ index : Fin (n + 1), predicate (witnesses index)) :
    ¬Function.Injective witnesses := by
  intro hinjective
  exact hbound ⟨witnesses, hinjective, hpredicate⟩

inductive CardinalityKind where
  | minimum
  | maximum
deriving DecidableEq, Repr

/-- The exact semantic payload represented by one Rust `CardDef`.  A positive
marker assertion activates either an at-least or at-most restriction on role
successors satisfying `filler`. -/
structure CardinalityDef (Concept Role : Type) where
  marker : Concept
  kind : CardinalityKind
  bound : Nat
  role : Role
  filler : Concept
deriving DecidableEq, Repr

def Interp.cardinalitySuccessor
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) (source target : Domain) : Prop :=
  I.role definition.role source target ∧ I.concept definition.filler target

def Interp.modelsCardinalityDef
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role) : Prop :=
  ∀ source, I.concept definition.marker source →
    match definition.kind with
    | .minimum => HasAtLeast definition.bound (I.cardinalitySuccessor definition source)
    | .maximum => HasAtMost definition.bound (I.cardinalitySuccessor definition source)

def Interp.modelsCardinalityDefs
    (I : Interp Domain Concept Role)
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∀ definition ∈ definitions, I.modelsCardinalityDef definition

theorem Interp.modelsCardinalityDefs_cons
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (definitions : List (CardinalityDef Concept Role)) :
    I.modelsCardinalityDefs (definition :: definitions) ↔
      I.modelsCardinalityDef definition ∧ I.modelsCardinalityDefs definitions := by
  simp [Interp.modelsCardinalityDefs]

theorem Interp.minimum_witnesses
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .minimum)
    (hmodels : I.modelsCardinalityDef definition)
    (source : Domain) (hmarker : I.concept definition.marker source) :
    HasAtLeast definition.bound (I.cardinalitySuccessor definition source) := by
  simpa [Interp.modelsCardinalityDef, hkind] using hmodels source hmarker

theorem Interp.maximum_forces_merge
    (I : Interp Domain Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .maximum)
    (hmodels : I.modelsCardinalityDef definition)
    (source : Domain) (hmarker : I.concept definition.marker source)
    (witnesses : Fin (definition.bound + 1) → Domain)
    (hsuccessors : ∀ index,
      I.cardinalitySuccessor definition source (witnesses index)) :
    ¬Function.Injective witnesses := by
  have hbound : HasAtMost definition.bound
      (I.cardinalitySuccessor definition source) := by
    simpa [Interp.modelsCardinalityDef, hkind] using hmodels source hmarker
  exact not_injective_of_hasAtMost hbound witnesses hsuccessors

#print axioms hasAtLeast_zero
#print axioms not_injective_of_hasAtMost
#print axioms Interp.minimum_witnesses
#print axioms Interp.maximum_forces_merge

end ContextCalculus.Hypertableau
