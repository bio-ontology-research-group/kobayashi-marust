import ContextCalculus.HypertableauCardinalityProductionWire
import ContextCalculus.HypertableauCardinalityWire
import ContextCalculus.HypertableauRootedCardinalityFrontierWire

/-!
# State-bound cardinality frontiers

An address map alone proves only a finite blocking bound. These documents bind
that map to the exact bounded cardinality runtime state, ontology, definitions,
and variable signature from which production obtained it.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireCardinalityAddressRefinementDocument where
  version : Nat
  variable_count : Nat
  ontology : List WireClause
  definitions : List WireCardinalityDef
  runtime : WireCardinalityRuntimeFields
  frontier : WireCardinalityAddressFrontier
deriving FromJson, ToJson, Repr

structure DecodedCardinalityAddressRefinementDocument
    (wire : WireCardinalityAddressRefinementDocument) where
  ontology : List (Clause (Fin wire.variable_count)
    (Fin wire.frontier.concept_count) (Fin wire.frontier.role_count))
  definitions : List (CardinalityDef (Fin wire.frontier.concept_count)
    (Fin wire.frontier.role_count))
  definition_count : definitions.length = wire.frontier.definition_count
  runtime : CheckedCardinalityRuntimeFields wire.frontier.node_count
    wire.frontier.concept_count wire.frontier.role_count wire.variable_count definitions
  active_full : runtime.fields.activeNodes = wire.frontier.node_count
  address : DecodedCardinalityAddressFrontier wire.frontier.node_count
    wire.frontier.concept_count wire.frontier.role_count
    wire.frontier.definition_count wire.frontier.max_width

def WireCardinalityAddressRefinementDocument.decode
    (wire : WireCardinalityAddressRefinementDocument) :
    Except String (DecodedCardinalityAddressRefinementDocument wire) := do
  if wire.version != 1 then
    throw s!"unsupported cardinality refinement version {wire.version}"
  let ontology ← wire.ontology.mapM (WireClause.decode wire.variable_count
    wire.frontier.concept_count wire.frontier.role_count)
  let definitions ← wire.definitions.mapM (WireCardinalityDef.decode
    wire.frontier.concept_count wire.frontier.role_count)
  if hdefinitions : definitions.length = wire.frontier.definition_count then
    let runtime ← wire.runtime.decodeChecked wire.frontier.node_count
      wire.frontier.concept_count wire.frontier.role_count wire.variable_count
      ontology definitions
    if hactive : runtime.fields.activeNodes = wire.frontier.node_count then
      let address ← wire.frontier.decode
      return ⟨ontology, definitions, hdefinitions, runtime, hactive, address⟩
    else throw "cardinality frontier is not the full reached bounded state"
  else throw "cardinality frontier definition count differs from its runtime problem"

def WireCardinalityAddressRefinementDocument.check
    (wire : WireCardinalityAddressRefinementDocument) : Bool := wire.decode.isOk

def WireCardinalityAddressRefinementDocument.checkScheduled
    (wire : WireCardinalityAddressRefinementDocument)
    (budget maxWidth : Nat) : Bool :=
  wire.check && wire.frontier.checkScheduled budget maxWidth

def WireCardinalityAddressRefinementDocument.sameProblem
    (left right : WireCardinalityAddressRefinementDocument) : Bool :=
  left.variable_count == right.variable_count &&
    left.frontier.concept_count == right.frontier.concept_count &&
    left.frontier.role_count == right.frontier.role_count &&
    left.frontier.definition_count == right.frontier.definition_count &&
    left.frontier.max_width == right.frontier.max_width &&
    toJson left.ontology == toJson right.ontology &&
    toJson left.definitions == toJson right.definitions

structure WireRootedCardinalityAddressRefinementDocument where
  version : Nat
  variable_count : Nat
  ontology : List WireClause
  definitions : List WireCardinalityDef
  runtime : WireCardinalityRuntimeFields
  frontier : WireRootedCardinalityAddressFrontier
deriving FromJson, ToJson, Repr

structure DecodedRootedCardinalityAddressRefinementDocument
    (wire : WireRootedCardinalityAddressRefinementDocument) where
  ontology : List (Clause (Fin wire.variable_count)
    (Fin wire.frontier.concept_count) (Fin wire.frontier.role_count))
  definitions : List (CardinalityDef (Fin wire.frontier.concept_count)
    (Fin wire.frontier.role_count))
  definition_count : definitions.length = wire.frontier.definition_count
  runtime : CheckedCardinalityRuntimeFields wire.frontier.node_count
    wire.frontier.concept_count wire.frontier.role_count wire.variable_count definitions
  active_full : runtime.fields.activeNodes = wire.frontier.node_count
  address : DecodedRootedCardinalityAddressFrontier wire.frontier.node_count
    wire.frontier.root_count wire.frontier.concept_count wire.frontier.role_count
    wire.frontier.definition_count wire.frontier.max_width

def WireRootedCardinalityAddressRefinementDocument.decode
    (wire : WireRootedCardinalityAddressRefinementDocument) :
    Except String (DecodedRootedCardinalityAddressRefinementDocument wire) := do
  if wire.version != 1 then
    throw s!"unsupported rooted cardinality refinement version {wire.version}"
  let ontology ← wire.ontology.mapM (WireClause.decode wire.variable_count
    wire.frontier.concept_count wire.frontier.role_count)
  let definitions ← wire.definitions.mapM (WireCardinalityDef.decode
    wire.frontier.concept_count wire.frontier.role_count)
  if hdefinitions : definitions.length = wire.frontier.definition_count then
    let runtime ← wire.runtime.decodeChecked wire.frontier.node_count
      wire.frontier.concept_count wire.frontier.role_count wire.variable_count
      ontology definitions
    if hactive : runtime.fields.activeNodes = wire.frontier.node_count then
      let address ← wire.frontier.decode
      return ⟨ontology, definitions, hdefinitions, runtime, hactive, address⟩
    else throw "rooted cardinality frontier is not the full reached bounded state"
  else throw "rooted cardinality frontier definition count differs from its runtime problem"

def WireRootedCardinalityAddressRefinementDocument.check
    (wire : WireRootedCardinalityAddressRefinementDocument) : Bool := wire.decode.isOk

def WireRootedCardinalityAddressRefinementDocument.checkScheduled
    (wire : WireRootedCardinalityAddressRefinementDocument)
    (budget rootCount maxWidth : Nat) : Bool :=
  wire.check && wire.frontier.checkScheduled budget rootCount maxWidth

def WireRootedCardinalityAddressRefinementDocument.sameProblem
    (left right : WireRootedCardinalityAddressRefinementDocument) : Bool :=
  left.variable_count == right.variable_count &&
    left.frontier.root_count == right.frontier.root_count &&
    left.frontier.concept_count == right.frontier.concept_count &&
    left.frontier.role_count == right.frontier.role_count &&
    left.frontier.definition_count == right.frontier.definition_count &&
    left.frontier.max_width == right.frontier.max_width &&
    toJson left.ontology == toJson right.ontology &&
    toJson left.definitions == toJson right.definitions

theorem WireCardinalityAddressRefinementDocument.check_sound
    (wire : WireCardinalityAddressRefinementDocument)
    (hcheck : wire.check = true) :
    ∃ decoded, wire.decode = .ok decoded := by
  unfold WireCardinalityAddressRefinementDocument.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded => exact ⟨decoded, rfl⟩

theorem WireRootedCardinalityAddressRefinementDocument.check_sound
    (wire : WireRootedCardinalityAddressRefinementDocument)
    (hcheck : wire.check = true) :
    ∃ decoded, wire.decode = .ok decoded := by
  unfold WireRootedCardinalityAddressRefinementDocument.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded => exact ⟨decoded, rfl⟩

#print axioms WireCardinalityAddressRefinementDocument.check_sound
#print axioms WireRootedCardinalityAddressRefinementDocument.check_sound

end ContextCalculus.Hypertableau
