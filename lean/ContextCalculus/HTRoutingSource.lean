import ContextCalculus.HypertableauSkolemProjection
import ContextCalculus.CertifiedRouting

/-!
# Hypertableau source adapter for certified routing

The HT worker does not consume the frontend Skolem clauses directly. Its
checked projection retains function-free clauses and replaces every exact
role/filler Skolem pair by one existential HT atom.  This module packages that
pre-projection source as a routing source and exposes the existing whole-list
equisatisfiability result in the shape needed by `SourceTranslation`.

The source retains every Skolem function key and requires them to be distinct.
Consequently independently projected existential obligations cannot silently
share witnesses. The route tag contributes no semantic premise.
-/

namespace ContextCalculus.HTRoutingSource

open ContextCalculus.Hypertableau

universe u v w x

structure Source (Variable : Type u) (Concept : Type v) (Role : Type w)
    (Function : Type x) where
  direct : List (Clause Variable Concept Role)
  pairs : List (SkolemPairSpec Variable Concept Role Function)
  functionKeysNodup : (skolemPairFunctions pairs).Nodup

def Source.target (source : Source Variable Concept Role Function) :
    List (Clause Variable Concept Role) :=
  skolemProjectionOntology source.direct source.pairs

def Source.Models (source : Source Variable Concept Role Function)
    (I : Interp Domain Concept Role) (functions : SkolemInterp Domain Function) : Prop :=
  I.models source.direct ∧ ModelsSkolemPairs I functions source.pairs

/-- The checked HT source projection is exact at the model-existence boundary.
Every frontend-source model yields a target model, and every target model can
be expanded with interpretations for all retained Skolem functions to model
the exact source. -/
theorem Source.models_iff_target [DecidableEq Function]
    (source : Source Variable Concept Role Function)
    (I : Interp Domain Concept Role) (base : SkolemInterp Domain Function) :
    (∃ functions, source.Models I functions) ↔ I.models source.target := by
  exact mixedSkolemProjection_sat_iff I base source.direct source.pairs
    source.functionKeysNodup

/-- Taxonomy entailment over the source before existential projection. -/
def Source.EntailsSub (source : Source Variable Concept Role Function)
    (sub sup : Concept) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role),
    (∃ functions, source.Models I functions) →
      ∀ value, I.concept sub value → I.concept sup value

/-- Taxonomy entailment is unchanged by the complete checked Skolem-pair
projection. This is the correctness equivalence consumed by the generic
routing translation lift. -/
theorem Source.entailsSub_iff_target [DecidableEq Function]
    (source : Source Variable Concept Role Function) (sub sup : Concept) :
    source.EntailsSub sub sup ↔
      Hypertableau.EntailsSub source.target sub sup := by
  constructor
  · intro hsource Domain I htarget value hsub
    let base : SkolemInterp Domain Function := ⟨fun _ _ => value⟩
    exact hsource Domain I
      ((source.models_iff_target I base).mpr htarget) value hsub
  · intro htarget Domain I hsource value hsub
    let base : SkolemInterp Domain Function := ⟨fun _ _ => value⟩
    exact htarget Domain I ((source.models_iff_target I base).mp hsource) value hsub

#print axioms Source.models_iff_target
#print axioms Source.entailsSub_iff_target

end ContextCalculus.HTRoutingSource
