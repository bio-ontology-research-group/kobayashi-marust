import ContextCalculus.HypertableauSkolemProjection
import ContextCalculus.HypertableauCardinalityProjection
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

/-- Exact frontend cardinality source retained before HT replaces clause
families by first-class definitions. -/
structure CardinalitySource (Concept Role : Type) where
  definitions : List (CardinalityDef Concept Role)
  pairs : List (PairedCardinality Concept Role)
  pairsCovered : ∀ pair ∈ pairs,
    pair.maximum ∈ definitions ∧ pair.minimum ∈ definitions

def CardinalitySource.Models
    (source : CardinalitySource Concept Role)
    (I : Interp Domain Concept Role) : Prop :=
  I.modelsProjectedCardinalityDefs source.definitions source.pairs

def CardinalitySource.TargetModels
    (source : CardinalitySource Concept Role)
    (I : Interp Domain Concept Role) : Prop :=
  I.modelsProjectedCardinalityTargets source.definitions source.pairs

/-- All maximum pigeonhole clauses, minimum witness expansions, and exact-pair
split/clash clauses have precisely the same models as the cardinality
definitions consumed by certified HT search. -/
theorem CardinalitySource.models_iff_target
    (source : CardinalitySource Concept Role)
    (I : Interp Domain Concept Role) :
    source.Models I ↔ source.TargetModels I := by
  exact modelsProjectedCardinalityDefs_iff_targets I source.definitions
    source.pairs source.pairsCovered

def CardinalitySource.EntailsSub
    (source : CardinalitySource Concept Role) (sub sup : Concept) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role),
    source.Models I → ∀ value, I.concept sub value → I.concept sup value

def CardinalitySource.TargetEntailsSub
    (source : CardinalitySource Concept Role) (sub sup : Concept) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role),
    source.TargetModels I →
      ∀ value, I.concept sub value → I.concept sup value

theorem CardinalitySource.entailsSub_iff_target
    (source : CardinalitySource Concept Role) (sub sup : Concept) :
    source.EntailsSub sub sup ↔ source.TargetEntailsSub sub sup := by
  constructor
  · intro hsource Domain I htarget
    exact hsource Domain I ((source.models_iff_target I).mpr htarget)
  · intro htarget Domain I hsource
    exact htarget Domain I ((source.models_iff_target I).mp hsource)

#print axioms CardinalitySource.models_iff_target
#print axioms CardinalitySource.entailsSub_iff_target

end ContextCalculus.HTRoutingSource
