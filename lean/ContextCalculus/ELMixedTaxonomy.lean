import ContextCalculus.ELFlatNF1

/-!
# Semantic laws for mixed sparse-taxonomy definitions

The sparse source route admits a small layer above normalized EL clauses:
named unions, named intersections whose remaining operands are positive
existential predicates, and finite nominals with explicit witnesses. This file
states the set-theoretic laws used by its fixpoint. They are independent of the
implementation's integer graph representation.
-/

namespace ContextCalculus.MixedTaxonomy

variable {Domain : Type}

def Subset (left right : Domain → Prop) : Prop :=
  ∀ x, left x → right x

def UnionDefinition (defined : Domain → Prop)
    (alternatives : List (Domain → Prop)) : Prop :=
  ∀ x, defined x ↔ ∃ alternative ∈ alternatives, alternative x

theorem unionDefinition_subset_iff
    {defined target : Domain → Prop} {alternatives : List (Domain → Prop)}
    (definition : UnionDefinition defined alternatives) :
    Subset defined target ↔ ∀ alternative ∈ alternatives, Subset alternative target := by
  constructor
  · intro included alternative member x holds
    exact included x ((definition x).2 ⟨alternative, member, holds⟩)
  · intro included x holds
    rcases (definition x).1 holds with ⟨alternative, member, alternative_holds⟩
    exact included alternative member x alternative_holds

def IntersectionDefinition (defined : Domain → Prop)
    (operands : List (Domain → Prop)) : Prop :=
  ∀ x, defined x ↔ ∀ operand ∈ operands, operand x

theorem intersectionDefinition_forward
    {defined : Domain → Prop} {operands : List (Domain → Prop)}
    (definition : IntersectionDefinition defined operands)
    {operand : Domain → Prop} (member : operand ∈ operands) :
    Subset defined operand := by
  intro x holds
  exact (definition x).1 holds operand member

theorem intersectionDefinition_reverse
    {defined source : Domain → Prop} {operands : List (Domain → Prop)}
    (definition : IntersectionDefinition defined operands)
    (included : ∀ operand ∈ operands, Subset source operand) :
    Subset source defined := by
  intro x holds
  exact (definition x).2 fun operand member => included operand member x holds

def NominalDefinition (defined : Domain → Prop) (individuals : List Domain) : Prop :=
  ∀ x, defined x ↔ x ∈ individuals

theorem nominalDefinition_subset_iff
    {defined target : Domain → Prop} {individuals : List Domain}
    (definition : NominalDefinition defined individuals) :
    Subset defined target ↔ ∀ individual ∈ individuals, target individual := by
  constructor
  · intro included individual member
    exact included individual ((definition individual).2 member)
  · intro included x holds
    exact included x ((definition x).1 holds)

theorem witnessedNominal_has_no_new_common_super
    {defined target : Domain → Prop} {individuals : List Domain}
    (definition : NominalDefinition defined individuals)
    (witness_types : ∀ individual ∈ individuals,
      target individual ↔ defined individual) :
    Subset defined target ↔ ∀ individual ∈ individuals, defined individual := by
  rw [nominalDefinition_subset_iff definition]
  constructor
  · intro types individual member
    exact (witness_types individual member).1 (types individual member)
  · intro witnesses individual member
    exact (witness_types individual member).2 (witnesses individual member)

#print axioms unionDefinition_subset_iff
#print axioms intersectionDefinition_reverse
#print axioms nominalDefinition_subset_iff

end ContextCalculus.MixedTaxonomy
