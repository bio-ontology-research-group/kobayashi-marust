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
  concepts_exact : List.Forall₂
    (fun concept decoded => decoded.wireQuery = .concept 0 concept) named concepts
  subsumptions_exact : List.Forall₂
    (fun sub row => List.Forall₂
      (fun sup decoded => decoded.wireQuery = .subsumption 0 sub sup) named row)
    named subsumptions
  named_nodup : named.Nodup
  complete_shape : wire.shapeB = true
  exact_queries : wire.queriesB = true
  shared_problem : wire.sharedProblemB = true

private def decodeNativeTaxonomyDecisionAt
    (expected : WireNativeABoxTaxonomyQuery)
    (wire : WireNativeABoxTaxonomyDecision) :
    Except String { decoded : DecodedNativeABoxTaxonomyDecision //
      decoded.wireQuery = expected } := do
  if hquery : wire.query = expected then
    let decoded ← wire.decodeExact
    return ⟨decoded.val, decoded.property.trans hquery⟩
  else throw "native ABox taxonomy cell does not match its matrix position"

private def decodeNativeTaxonomyConceptsExact :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun concept decision => decision.wireQuery = .concept 0 concept)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | concept :: named, wire :: wires => do
      let decision ← decodeNativeTaxonomyDecisionAt (.concept 0 concept) wire
      let tail ← decodeNativeTaxonomyConceptsExact named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "native ABox taxonomy concept row is incomplete"

private def decodeNativeTaxonomySubsumptionRowExact (sub : Nat) :
    (named : List Nat) → (wires : List WireNativeABoxTaxonomyDecision) →
    Except String { decoded : List DecodedNativeABoxTaxonomyDecision //
      List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sup :: named, wire :: wires => do
      let decision ← decodeNativeTaxonomyDecisionAt (.subsumption 0 sub sup) wire
      let tail ← decodeNativeTaxonomySubsumptionRowExact sub named wires
      return ⟨decision.val :: tail.val, .cons decision.property tail.property⟩
  | _, _ => .error "native ABox taxonomy subsumption row is incomplete"

private def decodeNativeTaxonomyRowsExact (allNamed : List Nat) :
    (named : List Nat) → (rows : List (List WireNativeABoxTaxonomyDecision)) →
    Except String { decoded : List (List DecodedNativeABoxTaxonomyDecision) //
      List.Forall₂
        (fun sub row => List.Forall₂
          (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
          allNamed row)
        named decoded }
  | [], [] => .ok ⟨[], .nil⟩
  | sub :: named, row :: rows => do
      let decodedRow ← decodeNativeTaxonomySubsumptionRowExact sub allNamed row
      let decodedRows ← decodeNativeTaxonomyRowsExact allNamed named rows
      return ⟨decodedRow.val :: decodedRows.val,
        .cons decodedRow.property decodedRows.property⟩
  | _, _ => .error "native ABox taxonomy subsumption matrix is incomplete"

def WireNativeABoxTaxonomyMatrix.decode
    (wire : WireNativeABoxTaxonomyMatrix) :
    Except String DecodedNativeABoxTaxonomyMatrix := do
  if wire.version != 1 then
    throw s!"unsupported complete native ABox taxonomy version {wire.version}"
  if hnamed : wire.named.Nodup then
    if hshape : wire.shapeB = true then
      if hqueries : wire.queriesB = true then
        if hshared : wire.sharedProblemB = true then
          let concepts ← decodeNativeTaxonomyConceptsExact wire.named wire.concepts
          let subsumptions ← decodeNativeTaxonomyRowsExact wire.named
            wire.named wire.subsumptions
          return {
            wire
            named := wire.named
            concepts := concepts.val
            subsumptions := subsumptions.val
            concepts_exact := concepts.property
            subsumptions_exact := subsumptions.property
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

private theorem conceptAlignment_coordinates_exact
    {named : List Nat} {decisions : List DecodedNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun concept decision => decision.wireQuery = .concept 0 concept)
      named decisions) :
    List.Forall₂
      (fun concept decision =>
        decision.CoordinatesExact (.concept 0 concept))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons (DecodedNativeABoxTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem subsumptionRowAlignment_coordinates_exact
    (sub : Nat) {named : List Nat}
    {decisions : List DecodedNativeABoxTaxonomyDecision}
    (haligned : List.Forall₂
      (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
      named decisions) :
    List.Forall₂
      (fun sup decision =>
        decision.CoordinatesExact (.subsumption 0 sub sup))
      named decisions := by
  induction haligned with
  | nil => exact .nil
  | cons haligned _ ih =>
      exact .cons (DecodedNativeABoxTaxonomyDecision.coordinates_exact _ haligned) ih

private theorem subsumptionAlignment_coordinates_exact
    (allNamed : List Nat) {named : List Nat}
    {rows : List (List DecodedNativeABoxTaxonomyDecision)}
    (haligned : List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => decision.wireQuery = .subsumption 0 sub sup)
        allNamed row)
      named rows) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision =>
          decision.CoordinatesExact (.subsumption 0 sub sup))
        allNamed row)
      named rows := by
  induction haligned with
  | nil => exact .nil
  | cons hrow _ ih =>
      exact .cons (subsumptionRowAlignment_coordinates_exact _ hrow) ih

theorem DecodedNativeABoxTaxonomyMatrix.concept_coordinates_exact
    (decoded : DecodedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision =>
        decision.CoordinatesExact (.concept 0 concept))
      decoded.named decoded.concepts :=
  conceptAlignment_coordinates_exact decoded.concepts_exact

theorem DecodedNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
    (decoded : DecodedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision =>
          decision.CoordinatesExact (.subsumption 0 sub sup))
        decoded.named row)
      decoded.named decoded.subsumptions :=
  subsumptionAlignment_coordinates_exact decoded.named decoded.subsumptions_exact

theorem DecodedNativeABoxTaxonomyMatrix.semantic_valid
    (decoded : DecodedNativeABoxTaxonomyMatrix) : decoded.SemanticallyValid := by
  exact ⟨decoded.complete_shape, decoded.exact_queries, decoded.shared_problem,
    decoded.every_cell_semantically_valid⟩

#print axioms DecodedNativeABoxTaxonomyMatrix.every_cell_semantically_valid
#print axioms DecodedNativeABoxTaxonomyMatrix.concept_coordinates_exact
#print axioms DecodedNativeABoxTaxonomyMatrix.subsumption_coordinates_exact
#print axioms DecodedNativeABoxTaxonomyMatrix.semantic_valid

end ContextCalculus.Hypertableau
