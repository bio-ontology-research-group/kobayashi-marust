import ContextCalculus.CBHyperClosure

/-! Ground-context initialization must instantiate universally quantified
empty-body clauses at named individuals. This is the zero-provider case of
Hyper, using the existing checked substitution and head normalization. The
original source clauses remain in the ontology. -/
namespace ContextCalculus.CBGroundFactInstantiation
open ContextCalculus ContextCalculus.CheckerTerm ContextCalculus.CBHyperClosure
open ContextCalculus.CBFiniteModel ContextCalculus.CBProductionTrace

/-- Adding source instances preserves exactly the original models. In
particular, different individual names need not denote different objects. -/
theorem model_preservation {D : Type} (model : TModel D)
    (source : List FCL) (instances : List (FCL × List (Int × FTerm)))
    (bound : ∀ item ∈ instances, item.1 ∈ source) :
    (∀ clause ∈ source, valid model clause) ↔
    ((∀ clause ∈ source, valid model clause) ∧
      ∀ item ∈ instances, valid model (substCl item.2 item.1)) := by
  constructor
  · intro h
    exact ⟨h, fun item hi => inst_valid model (h item.1 (bound item hi)) item.2⟩
  · intro h
    exact h.1

/-- Runtime ground seeds carry ordinary Hyper evidence with no providers;
the existing checker validates their substitution and normalized conclusion. -/
theorem ground_seed_sound {D : Type} (model : TModel D)
    (assignment : Int → D) (source conclusion : FCL)
    (substitution : List (Int × FTerm))
    (candidate : hyperCandidate? [] source substitution [] = some conclusion)
    (validSource : valid model source) :
    HoldsAt model assignment conclusion := by
  exact hyperCandidate_sound model assignment [] source substitution [] conclusion
    candidate validSource (by simp)

#print axioms model_preservation
#print axioms ground_seed_sound
end ContextCalculus.CBGroundFactInstantiation
