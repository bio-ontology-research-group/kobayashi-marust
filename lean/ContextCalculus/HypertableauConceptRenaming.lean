import ContextCalculus.Hypertableau

/-!
# Concept renaming for hypertableau clauses

The production wire represents concepts by positions in a symbol table.  Proof
constructions instead use structural concept signatures.  This module proves
the semantic transport needed to connect those representations.
-/

namespace ContextCalculus.Hypertableau

def renameLit (f : SourceConcept → TargetConcept) (literal : Lit SourceConcept) :
    Lit TargetConcept := ⟨f literal.concept, literal.neg⟩

def renameAtom (f : SourceConcept → TargetConcept) :
    Atom Variable SourceConcept Role → Atom Variable TargetConcept Role
  | .concept literal node => .concept (renameLit f literal) node
  | .role role source target => .role role source target
  | .exists_ role filler node => .exists_ role (renameLit f filler) node
  | .eq left right => .eq left right

def renameClause (f : SourceConcept → TargetConcept)
    (clause : Clause Variable SourceConcept Role) :
    Clause Variable TargetConcept Role := {
  body := clause.body.map (renameAtom f)
  head := clause.head.map (renameAtom f)
}

def renameOntology (f : SourceConcept → TargetConcept)
    (ontology : List (Clause Variable SourceConcept Role)) :
    List (Clause Variable TargetConcept Role) :=
  ontology.map (renameClause f)

def pullbackConcepts (f : SourceConcept → TargetConcept)
    (J : Interp Domain TargetConcept Role) : Interp Domain SourceConcept Role where
  concept concept := J.concept (f concept)
  role := J.role

def pushforwardConcepts (g : TargetConcept → SourceConcept)
    (I : Interp Domain SourceConcept Role) : Interp Domain TargetConcept Role where
  concept concept := I.concept (g concept)
  role := I.role

theorem satLit_rename_pullback_iff
    (f : SourceConcept → TargetConcept) (J : Interp Domain TargetConcept Role)
    (literal : Lit SourceConcept) (value : Domain) :
    J.satLit (renameLit f literal) value ↔
      (pullbackConcepts f J).satLit literal value := by
  cases literal
  simp [renameLit, Interp.satLit, pullbackConcepts]

theorem satAtom_rename_pullback_iff
    (f : SourceConcept → TargetConcept) (J : Interp Domain TargetConcept Role)
    (assignment : Variable → Domain) (atom : Atom Variable SourceConcept Role) :
    J.satAtom assignment (renameAtom f atom) ↔
      (pullbackConcepts f J).satAtom assignment atom := by
  cases atom <;>
    simp [renameAtom, Interp.satAtom, satLit_rename_pullback_iff, pullbackConcepts]

theorem modelsClause_rename_pullback_iff
    (f : SourceConcept → TargetConcept) (J : Interp Domain TargetConcept Role)
    (clause : Clause Variable SourceConcept Role) :
    J.modelsClause (renameClause f clause) ↔
      (pullbackConcepts f J).modelsClause clause := by
  constructor
  · intro hmodels assignment hbody
    have hmappedBody : ∀ atom ∈ (renameClause f clause).body,
        J.satAtom assignment atom := by
      intro atom hatom
      rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
      exact (satAtom_rename_pullback_iff f J assignment sourceAtom).2
        (hbody sourceAtom hsource)
    rcases hmodels assignment hmappedBody with ⟨atom, hatom, hsat⟩
    rcases List.mem_map.mp hatom with ⟨sourceAtom, hsource, rfl⟩
    exact ⟨sourceAtom, hsource,
      (satAtom_rename_pullback_iff f J assignment sourceAtom).1 hsat⟩
  · intro hmodels assignment hbody
    have hsourceBody : ∀ atom ∈ clause.body,
        (pullbackConcepts f J).satAtom assignment atom := by
      intro atom hatom
      exact (satAtom_rename_pullback_iff f J assignment atom).1
        (hbody (renameAtom f atom) (List.mem_map.mpr ⟨atom, hatom, rfl⟩))
    rcases hmodels assignment hsourceBody with ⟨atom, hatom, hsat⟩
    exact ⟨renameAtom f atom, List.mem_map.mpr ⟨atom, hatom, rfl⟩,
      (satAtom_rename_pullback_iff f J assignment atom).2 hsat⟩

theorem models_rename_pullback_iff
    (f : SourceConcept → TargetConcept) (J : Interp Domain TargetConcept Role)
    (ontology : List (Clause Variable SourceConcept Role)) :
    J.models (renameOntology f ontology) ↔
      (pullbackConcepts f J).models ontology := by
  constructor
  · intro hmodels clause hclause
    exact (modelsClause_rename_pullback_iff f J clause).1
      (hmodels (renameClause f clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
  · intro hmodels clause hclause
    rcases List.mem_map.mp hclause with ⟨sourceClause, hsource, rfl⟩
    exact (modelsClause_rename_pullback_iff f J sourceClause).2
      (hmodels sourceClause hsource)

theorem pullback_pushforward_eq
    (f : SourceConcept → TargetConcept) (g : TargetConcept → SourceConcept)
    (hleft : ∀ concept, g (f concept) = concept)
    (I : Interp Domain SourceConcept Role) :
    pullbackConcepts f (pushforwardConcepts g I) = I := by
  cases I
  simp only [pullbackConcepts, pushforwardConcepts]
  congr
  funext concept
  rw [hleft]

theorem models_rename_pushforward_iff
    (f : SourceConcept → TargetConcept) (g : TargetConcept → SourceConcept)
    (hleft : ∀ concept, g (f concept) = concept)
    (I : Interp Domain SourceConcept Role)
    (ontology : List (Clause Variable SourceConcept Role)) :
    (pushforwardConcepts g I).models (renameOntology f ontology) ↔
      I.models ontology := by
  rw [models_rename_pullback_iff]
  rw [pullback_pushforward_eq f g hleft I]

theorem renameOntology_sat_iff_of_leftInverse
    (f : SourceConcept → TargetConcept) (g : TargetConcept → SourceConcept)
    (hleft : ∀ concept, g (f concept) = concept)
    (ontology : List (Clause Variable SourceConcept Role)) :
    (∃ I : Interp Domain SourceConcept Role, I.models ontology) ↔
      ∃ J : Interp Domain TargetConcept Role, J.models (renameOntology f ontology) := by
  constructor
  · rintro ⟨I, hmodels⟩
    exact ⟨pushforwardConcepts g I,
      (models_rename_pushforward_iff f g hleft I ontology).2 hmodels⟩
  · rintro ⟨J, hmodels⟩
    exact ⟨pullbackConcepts f J,
      (models_rename_pullback_iff f J ontology).1 hmodels⟩

#print axioms models_rename_pullback_iff
#print axioms models_rename_pushforward_iff
#print axioms renameOntology_sat_iff_of_leftInverse

end ContextCalculus.Hypertableau
