import ContextCalculus.ELCompletion

/-!
# Exact concept renaming for ELC ontologies

The executable wire stores clauses over compact numeric IDs while the
normalization proof interprets those IDs through an injective origin map. This
file proves that the two ontologies have exactly the same model theory whenever
the origin map has a left inverse.
-/

namespace ContextCalculus.ELCompletion

def mapClauseConcept (f : Concept → Target) : Clause Concept Role → Clause Target Role
  | .nf1 sub sup => .nf1 (f sub) (f sup)
  | .nf2 left right sup => .nf2 (f left) (f right) (f sup)
  | .nf3 sub role filler => .nf3 (f sub) role (f filler)
  | .nf4 role filler sup => .nf4 role (f filler) (f sup)
  | .nf5 sub => .nf5 (f sub)
  | .nf6 sub sup => .nf6 sub sup
  | .nf7 first second sup => .nf7 first second sup
  | .reflexive role => .reflexive role

def mapOntologyConcept (f : Concept → Target) (O : Ontology Concept Role) :
    Ontology Target Role :=
  O.map (mapClauseConcept f)

def pullbackInterp {top bottom : Concept}
    (f : Concept → Target)
    (J : Interp Domain Target Role (f top) (f bottom)) :
    Interp Domain Concept Role top bottom where
  concept concept := J.concept (f concept)
  role := J.role
  top_true := J.top_true
  bottom_false := J.bottom_false

def pushforwardInterp {top bottom : Concept}
    (f : Concept → Target) (g : Target → Concept)
    (hleft : Function.LeftInverse g f)
    (I : Interp Domain Concept Role top bottom) :
    Interp Domain Target Role (f top) (f bottom) where
  concept target := I.concept (g target)
  role := I.role
  top_true := by simpa [hleft top] using I.top_true
  bottom_false := by simpa [hleft bottom] using I.bottom_false

theorem satClause_mapConcept_pullback_iff {top bottom : Concept}
    (f : Concept → Target)
    (J : Interp Domain Target Role (f top) (f bottom))
    (clause : Clause Concept Role) :
    satClause J (mapClauseConcept f clause) ↔
      satClause (pullbackInterp f J) clause := by
  cases clause <;> rfl

theorem satClause_mapConcept_pushforward_iff {top bottom : Concept}
    (f : Concept → Target) (g : Target → Concept)
    (hleft : Function.LeftInverse g f)
    (I : Interp Domain Concept Role top bottom)
    (clause : Clause Concept Role) :
    satClause (pushforwardInterp f g hleft I) (mapClauseConcept f clause) ↔
      satClause I clause := by
  have hgf : ∀ concept, g (f concept) = concept := hleft
  cases clause <;> simp [mapClauseConcept, satClause, pushforwardInterp, hgf]

theorem models_mapConcept_pullback_iff {top bottom : Concept}
    (f : Concept → Target)
    (J : Interp Domain Target Role (f top) (f bottom))
    (O : Ontology Concept Role) :
    models J (mapOntologyConcept f O) ↔ models (pullbackInterp f J) O := by
  simp only [models, mapOntologyConcept, List.mem_map]
  constructor
  · intro h clause hclause
    exact (satClause_mapConcept_pullback_iff f J clause).mp
      (h (mapClauseConcept f clause) ⟨clause, hclause, rfl⟩)
  · rintro h mapped ⟨clause, hclause, rfl⟩
    exact (satClause_mapConcept_pullback_iff f J clause).mpr (h clause hclause)

theorem models_mapConcept_pushforward_iff {top bottom : Concept}
    (f : Concept → Target) (g : Target → Concept)
    (hleft : Function.LeftInverse g f)
    (I : Interp Domain Concept Role top bottom)
    (O : Ontology Concept Role) :
    models (pushforwardInterp f g hleft I) (mapOntologyConcept f O) ↔
      models I O := by
  simp only [models, mapOntologyConcept, List.mem_map]
  constructor
  · intro h clause hclause
    exact (satClause_mapConcept_pushforward_iff f g hleft I clause).mp
      (h (mapClauseConcept f clause) ⟨clause, hclause, rfl⟩)
  · rintro h mapped ⟨clause, hclause, rfl⟩
    exact (satClause_mapConcept_pushforward_iff f g hleft I clause).mpr
      (h clause hclause)

theorem entailsSub_mapConcept_iff {top bottom : Concept}
    (f : Concept → Target) (g : Target → Concept)
    (hleft : Function.LeftInverse g f)
    (O : Ontology Concept Role) (sub sup : Concept) :
    EntailsSub (top := f top) (bottom := f bottom)
        (mapOntologyConcept f O) (f sub) (f sup) ↔
      EntailsSub (top := top) (bottom := bottom) O sub sup := by
  constructor
  · intro h Domain I hmodels x hsub
    have hmapped := (models_mapConcept_pushforward_iff f g hleft I O).mpr hmodels
    have hout := h (pushforwardInterp f g hleft I) hmapped x
    have hsub' : (pushforwardInterp f g hleft I).concept (f sub) x := by
      change I.concept (g (f sub)) x
      rwa [hleft sub]
    have hsup := hout hsub'
    change I.concept (g (f sup)) x at hsup
    rwa [hleft sup] at hsup
  · intro h Domain J hmodels x hsub
    have hsource := (models_mapConcept_pullback_iff f J O).mp hmodels
    exact h (pullbackInterp f J) hsource x hsub

theorem unsatisfiable_mapConcept_iff {top bottom : Concept}
    (f : Concept → Target) (g : Target → Concept)
    (hleft : Function.LeftInverse g f)
    (O : Ontology Concept Role) :
    Unsatisfiable (top := f top) (bottom := f bottom) (mapOntologyConcept f O) ↔
      Unsatisfiable (top := top) (bottom := bottom) O := by
  constructor
  · intro h Domain _ I hmodels
    exact h (pushforwardInterp f g hleft I)
      ((models_mapConcept_pushforward_iff f g hleft I O).mpr hmodels)
  · intro h Domain _ J hmodels
    exact h (pullbackInterp f J)
      ((models_mapConcept_pullback_iff f J O).mp hmodels)

#print axioms entailsSub_mapConcept_iff
#print axioms unsatisfiable_mapConcept_iff

end ContextCalculus.ELCompletion
