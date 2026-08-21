import ContextCalculus.HypertableauNativeABoxTaxonomyWire

/-!
# Complete native-ABox taxonomy matrix wire

The matrix checker requires one decision for every named concept and every
ordered named-concept pair.  It also checks that every cell carries byte-level
identical native-ABox, ontology, and variable-signature data before decoding
the cells semantically.  This prevents a matrix from combining valid answers
to different reasoning problems.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNativeABoxTaxonomyMatrix where
  version : Nat
  named : List Nat
  concepts : List WireNativeABoxTaxonomyDecision
  subsumptions : List (List WireNativeABoxTaxonomyDecision)
deriving FromJson, ToJson, Repr

def WireNativeABoxTaxonomyDecision.problemJson
    (wire : WireNativeABoxTaxonomyDecision) : Json :=
  let seed := match wire.evidence with
    | .sat certificate => certificate.seed
    | .unsat initial _ => initial
  Json.mkObj [
    ("abox", toJson seed.abox),
    ("variable_count", toJson seed.variable_count),
    ("ontology", toJson seed.ontology)]

def WireNativeABoxTaxonomyDecision.sameProblemB
    (left right : WireNativeABoxTaxonomyDecision) : Bool :=
  left.problemJson == right.problemJson

def WireNativeABoxTaxonomyDecision.matchesConceptB
    (wire : WireNativeABoxTaxonomyDecision) (concept : Nat) : Bool :=
  match wire.query with
  | .concept root candidate => root == 0 && candidate == concept
  | .subsumption .. => false

def WireNativeABoxTaxonomyDecision.matchesSubsumptionB
    (wire : WireNativeABoxTaxonomyDecision) (sub sup : Nat) : Bool :=
  match wire.query with
  | .concept .. => false
  | .subsumption root candidateSub candidateSup =>
      root == 0 && candidateSub == sub && candidateSup == sup

def WireNativeABoxTaxonomyMatrix.shapeB
    (wire : WireNativeABoxTaxonomyMatrix) : Bool :=
  wire.concepts.length == wire.named.length &&
  wire.subsumptions.length == wire.named.length &&
  wire.subsumptions.all fun row => row.length == wire.named.length

def WireNativeABoxTaxonomyMatrix.queriesB
    (wire : WireNativeABoxTaxonomyMatrix) : Bool :=
  ((wire.named.zip wire.concepts).all fun pair =>
      pair.2.matchesConceptB pair.1) &&
  (wire.named.zip wire.subsumptions).all fun subRow =>
    (wire.named.zip subRow.2).all fun supCell =>
      supCell.2.matchesSubsumptionB subRow.1 supCell.1

def WireNativeABoxTaxonomyMatrix.allCells
    (wire : WireNativeABoxTaxonomyMatrix) :
    List WireNativeABoxTaxonomyDecision :=
  wire.concepts ++ wire.subsumptions.flatten

def WireNativeABoxTaxonomyMatrix.sharedProblemB
    (wire : WireNativeABoxTaxonomyMatrix) : Bool :=
  match wire.concepts.head? with
  | none => false
  | some baseline => wire.allCells.all (baseline.sameProblemB ·)

structure DecodedNativeABoxTaxonomyMatrix where
  wire : WireNativeABoxTaxonomyMatrix
  named : List Nat
  concepts : List DecodedNativeABoxTaxonomyDecision
  subsumptions : List (List DecodedNativeABoxTaxonomyDecision)
  named_nodup : named.Nodup
  complete_shape : wire.shapeB = true
  exact_queries : wire.queriesB = true
  shared_problem : wire.sharedProblemB = true

def WireNativeABoxTaxonomyMatrix.decode
    (wire : WireNativeABoxTaxonomyMatrix) :
    Except String DecodedNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported complete native ABox taxonomy version {wire.version}"
  if hnamed : wire.named.Nodup then
    if hshape : wire.shapeB = true then
      if hqueries : wire.queriesB = true then
        if hshared : wire.sharedProblemB = true then
          let concepts ← wire.concepts.mapM WireNativeABoxTaxonomyDecision.decode
          let subsumptions ← wire.subsumptions.mapM fun row =>
            row.mapM WireNativeABoxTaxonomyDecision.decode
          return {
            wire
            named := wire.named
            concepts
            subsumptions
            named_nodup := hnamed
            complete_shape := hshape
            exact_queries := hqueries
            shared_problem := hshared
          }
        else throw "native ABox taxonomy cells describe different reasoning problems"
      else throw "native ABox taxonomy cell does not match its matrix position"
    else throw "native ABox taxonomy matrix is incomplete"
  else throw "complete native ABox taxonomy repeats a named concept"

def WireNativeABoxTaxonomyMatrix.check
    (wire : WireNativeABoxTaxonomyMatrix) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedNativeABoxTaxonomyMatrix.allDecisions
    (decoded : DecodedNativeABoxTaxonomyMatrix) :
    List DecodedNativeABoxTaxonomyDecision :=
  decoded.concepts ++ decoded.subsumptions.flatten

def DecodedNativeABoxTaxonomyMatrix.SemanticallyValid
    (decoded : DecodedNativeABoxTaxonomyMatrix) : Prop :=
  decoded.wire.shapeB = true ∧
  decoded.wire.queriesB = true ∧
  decoded.wire.sharedProblemB = true ∧
  ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid

theorem DecodedNativeABoxTaxonomyMatrix.every_cell_semantically_valid
    (decoded : DecodedNativeABoxTaxonomyMatrix) :
    ∀ decision ∈ decoded.allDecisions, decision.SemanticallyValid := by
  intro decision _
  exact decision.semantic_valid

theorem DecodedNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedNativeABoxTaxonomyMatrix) : decoded.SemanticallyValid := by
  exact ⟨decoded.complete_shape, decoded.exact_queries, decoded.shared_problem,
    decoded.every_cell_semantically_valid⟩

#print axioms DecodedNativeABoxTaxonomyMatrix.every_cell_semantically_valid
#print axioms DecodedNativeABoxTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
