import ContextCalculus.HypertableauNativeABoxTaxonomySourceWire
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomySourceWire

/-!
# Exact source-taxonomy publication

This module combines two guarantees that were previously exposed separately:
every decoded decision retains its exact matrix coordinates, and its published
Boolean is true exactly when the source-level query is entailed.  The capstones
below cover direct, mixed, and bundled source projections, with and without
cardinality.
-/

namespace ContextCalculus.Hypertableau

def ExactTaxonomyCell (expected : WireNativeABoxTaxonomyQuery)
    (positive : Decision → Bool) (entailed : Decision → Prop)
    (coordinates : WireNativeABoxTaxonomyQuery → Decision → Prop)
    (decision : Decision) : Prop :=
  coordinates expected decision ∧ (positive decision = true ↔ entailed decision)

private theorem exactCells_of_coordinates
    (query : Index → WireNativeABoxTaxonomyQuery)
    (positive : Decision → Bool) (entailed : Decision → Prop)
    (coordinates : WireNativeABoxTaxonomyQuery → Decision → Prop)
    (polarity : ∀ decision, positive decision = true ↔ entailed decision)
    {indices : List Index} {decisions : List Decision}
    (hcoordinates : List.Forall₂
      (fun index decision => coordinates (query index) decision)
      indices decisions) :
    List.Forall₂
      (fun index decision => ExactTaxonomyCell (query index)
        positive entailed coordinates decision)
      indices decisions := by
  induction hcoordinates with
  | nil => exact .nil
  | cons hcoordinate _ ih => exact .cons ⟨hcoordinate, polarity _⟩ ih

private theorem exactRows_of_coordinates
    (query : Row → Column → WireNativeABoxTaxonomyQuery)
    (positive : Decision → Bool) (entailed : Decision → Prop)
    (coordinates : WireNativeABoxTaxonomyQuery → Decision → Prop)
    (polarity : ∀ decision, positive decision = true ↔ entailed decision)
    (columns : List Column) {rows : List Row}
    {decisions : List (List Decision)}
    (hcoordinates : List.Forall₂
      (fun row cells => List.Forall₂
        (fun column decision => coordinates (query row column) decision)
        columns cells)
      rows decisions) :
    List.Forall₂
      (fun row cells => List.Forall₂
        (fun column decision => ExactTaxonomyCell (query row column)
          positive entailed coordinates decision)
        columns cells)
      rows decisions := by
  induction hcoordinates with
  | nil => exact .nil
  | cons hrow _ ih =>
      exact .cons (exactCells_of_coordinates (query := query _)
        positive entailed coordinates polarity hrow) ih

theorem DecodedDirectNativeABoxTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedDirectNativeABoxTaxonomyDecision.positive
        DecodedDirectNativeABoxTaxonomyDecision.QueryEntailed
        DecodedDirectNativeABoxTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedDirectNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedDirectNativeABoxTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedDirectNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedDirectNativeABoxTaxonomyDecision.positive
          DecodedDirectNativeABoxTaxonomyDecision.QueryEntailed
          DecodedDirectNativeABoxTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedDirectNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

theorem DecodedMixedNativeABoxTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedMixedNativeABoxTaxonomyDecision.positive
        DecodedMixedNativeABoxTaxonomyDecision.QueryEntailed
        DecodedMixedNativeABoxTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedMixedNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedMixedNativeABoxTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedMixedNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedMixedNativeABoxTaxonomyDecision.positive
          DecodedMixedNativeABoxTaxonomyDecision.QueryEntailed
          DecodedMixedNativeABoxTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedMixedNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

theorem DecodedBundleNativeABoxTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedBundleNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedBundleNativeABoxTaxonomyDecision.positive
        DecodedBundleNativeABoxTaxonomyDecision.QueryEntailed
        DecodedBundleNativeABoxTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedBundleNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedBundleNativeABoxTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedBundleNativeABoxTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedBundleNativeABoxTaxonomyDecision.positive
          DecodedBundleNativeABoxTaxonomyDecision.QueryEntailed
          DecodedBundleNativeABoxTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedBundleNativeABoxTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

theorem DecodedDirectNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive
        DecodedDirectNativeABoxCardinalityTaxonomyDecision.QueryEntailed
        DecodedDirectNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedDirectNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedDirectNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive
          DecodedDirectNativeABoxCardinalityTaxonomyDecision.QueryEntailed
          DecodedDirectNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedDirectNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

theorem DecodedMixedNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive
        DecodedMixedNativeABoxCardinalityTaxonomyDecision.QueryEntailed
        DecodedMixedNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedMixedNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedMixedNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive
          DecodedMixedNativeABoxCardinalityTaxonomyDecision.QueryEntailed
          DecodedMixedNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedMixedNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

theorem DecodedBundleNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun concept decision => ExactTaxonomyCell (.concept 0 concept)
        DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive
        DecodedBundleNativeABoxCardinalityTaxonomyDecision.QueryEntailed
        DecodedBundleNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
      decoded.matrix.named decoded.concepts :=
  exactCells_of_coordinates (fun concept => .concept 0 concept) _ _ _
    DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.concept_coordinates_exact

theorem DecodedBundleNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly
    (decoded : DecodedBundleNativeABoxCardinalityTaxonomyMatrix) :
    List.Forall₂
      (fun sub row => List.Forall₂
        (fun sup decision => ExactTaxonomyCell (.subsumption 0 sub sup)
          DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive
          DecodedBundleNativeABoxCardinalityTaxonomyDecision.QueryEntailed
          DecodedBundleNativeABoxCardinalityTaxonomyDecision.CoordinatesExact decision)
        decoded.matrix.named row)
      decoded.matrix.named decoded.subsumptions :=
  exactRows_of_coordinates (fun sub sup => .subsumption 0 sub sup) _ _ _
    DecodedBundleNativeABoxCardinalityTaxonomyDecision.positive_eq_true_iff
    decoded.matrix.named decoded.subsumption_coordinates_exact

#print axioms DecodedDirectNativeABoxTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedDirectNativeABoxTaxonomyMatrix.subsumptions_published_exactly
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedMixedNativeABoxTaxonomyMatrix.subsumptions_published_exactly
#print axioms DecodedBundleNativeABoxTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedBundleNativeABoxTaxonomyMatrix.subsumptions_published_exactly
#print axioms DecodedDirectNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedDirectNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedMixedNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly
#print axioms DecodedBundleNativeABoxCardinalityTaxonomyMatrix.concepts_published_exactly
#print axioms DecodedBundleNativeABoxCardinalityTaxonomyMatrix.subsumptions_published_exactly

end ContextCalculus.Hypertableau
