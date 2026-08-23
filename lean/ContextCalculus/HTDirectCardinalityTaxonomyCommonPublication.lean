import ContextCalculus.HypertableauSourceBoundCardinalityWire
import ContextCalculus.HypertableauExactCardinalityTaxonomyWire
import ContextCalculus.HTDirectCardinalityCommonSourceWire

/-!
# Direct cardinality taxonomy publications over the common source

This boundary binds the complete exact-cardinality matrix to the checked
direct projection.  It compares the normalized source, all finite dimensions,
directional definitions, and exact complementary-pair provenance.  Every
decoded matrix cell is then checked against the one normalized target.
-/

namespace ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire

theorem modelsCardinalityDefsExact_congr_toFinset
    [DecidableEq Concept] [DecidableEq Role]
    (I : Interp Domain Concept Role)
    {left right : List (CardinalityDef Concept Role)}
    (hdefinitions : left.toFinset = right.toFinset) :
    I.modelsCardinalityDefsExact left ↔ I.modelsCardinalityDefsExact right := by
  constructor
  · intro hleft definition hright
    apply hleft definition
    have : definition ∈ right.toFinset := by simpa using hright
    rw [← hdefinitions] at this
    simpa using this
  · intro hright definition hleft
    apply hright definition
    have : definition ∈ left.toFinset := by simpa using hleft
    rw [hdefinitions] at this
    simpa using this

theorem entailsWithExact_congr_toFinset
    [DecidableEq Concept] [DecidableEq Role]
    {left right : List (CardinalityDef Concept Role)}
    (hdefinitions : left.toFinset = right.toFinset) :
    EntailsSubWithExactCardinality ontology definitions left sub sup ↔
      EntailsSubWithExactCardinality ontology definitions right sub sup := by
  constructor
  · intro hleft Domain I hontology hdefs hright
    exact hleft Domain I hontology hdefs
      ((modelsCardinalityDefsExact_congr_toFinset I hdefinitions).2 hright)
  · intro hright Domain I hontology hdefs hleft
    exact hright Domain I hontology hdefs
      ((modelsCardinalityDefsExact_congr_toFinset I hdefinitions).1 hleft)

theorem unsatisfiableWithExact_congr_toFinset
    [DecidableEq Concept] [DecidableEq Role]
    {left right : List (CardinalityDef Concept Role)}
    (hdefinitions : left.toFinset = right.toFinset) :
    UnsatisfiableConceptWithExactCardinality ontology definitions left concept ↔
      UnsatisfiableConceptWithExactCardinality ontology definitions right concept := by
  constructor
  · intro hleft Domain I hontology hdefs hright
    exact hleft Domain I hontology hdefs
      ((modelsCardinalityDefsExact_congr_toFinset I hdefinitions).2 hright)
  · intro hright Domain I hontology hdefs hleft
    exact hright Domain I hontology hdefs
      ((modelsCardinalityDefsExact_congr_toFinset I hdefinitions).1 hleft)

theorem entailsWithExact_mapModelEquivalent_iff
    {source target : List (Hypertableau.Clause (Fin variableCount)
      (Fin concepts) (Fin roles))}
    (equivalent : ModelEquivalent source target)
    (definitions exactDefinitions : List (CardinalityDef Nat Nat))
    (sub sup : Nat) :
    EntailsSubWithExactCardinality (mapOntology source) definitions exactDefinitions sub sup ↔
      EntailsSubWithExactCardinality (mapOntology target) definitions exactDefinitions sub sup := by
  constructor
  · intro hsource Domain I htarget hdefinitions hexact value hsub
    letI : Nonempty Domain := ⟨value⟩
    have htargetFin : (finInterp I).models target := by
      intro clause hclause
      exact (modelsClause_map_finInterp I clause).2
        (htarget (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hsourceFin := (equivalent Domain (finInterp I)).mpr htargetFin
    have hsourceNat : I.models (mapOntology source) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨original, horiginal, rfl⟩
      exact (modelsClause_map_finInterp I original).1 (hsourceFin original horiginal)
    exact hsource Domain I hsourceNat hdefinitions hexact value hsub
  · intro htarget Domain I hsource hdefinitions hexact value hsub
    letI : Nonempty Domain := ⟨value⟩
    have hsourceFin : (finInterp I).models source := by
      intro clause hclause
      exact (modelsClause_map_finInterp I clause).2
        (hsource (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have htargetFin := (equivalent Domain (finInterp I)).mp hsourceFin
    have htargetNat : I.models (mapOntology target) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨original, horiginal, rfl⟩
      exact (modelsClause_map_finInterp I original).1 (htargetFin original horiginal)
    exact htarget Domain I htargetNat hdefinitions hexact value hsub

theorem unsatisfiableWithExact_mapModelEquivalent_iff
    {source target : List (Hypertableau.Clause (Fin variableCount)
      (Fin concepts) (Fin roles))}
    (equivalent : ModelEquivalent source target)
    (definitions exactDefinitions : List (CardinalityDef Nat Nat))
    (concept : Nat) :
    UnsatisfiableConceptWithExactCardinality (mapOntology source)
        definitions exactDefinitions concept ↔
      UnsatisfiableConceptWithExactCardinality (mapOntology target)
        definitions exactDefinitions concept := by
  constructor
  · intro hsource Domain I htarget hdefinitions hexact value hconcept
    letI : Nonempty Domain := ⟨value⟩
    have htargetFin : (finInterp I).models target := by
      intro clause hclause
      exact (modelsClause_map_finInterp I clause).2
        (htarget (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have hsourceFin := (equivalent Domain (finInterp I)).mpr htargetFin
    have hsourceNat : I.models (mapOntology source) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨original, horiginal, rfl⟩
      exact (modelsClause_map_finInterp I original).1 (hsourceFin original horiginal)
    exact hsource Domain I hsourceNat hdefinitions hexact value hconcept
  · intro htarget Domain I hsource hdefinitions hexact value hconcept
    letI : Nonempty Domain := ⟨value⟩
    have hsourceFin : (finInterp I).models source := by
      intro clause hclause
      exact (modelsClause_map_finInterp I clause).2
        (hsource (mapClause clause) (List.mem_map.mpr ⟨clause, hclause, rfl⟩))
    have htargetFin := (equivalent Domain (finInterp I)).mp hsourceFin
    have htargetNat : I.models (mapOntology target) := by
      intro clause hclause
      rcases List.mem_map.mp hclause with ⟨original, horiginal, rfl⟩
      exact (modelsClause_map_finInterp I original).1 (htargetFin original horiginal)
    exact htarget Domain I htargetNat hdefinitions hexact value hconcept

def projectionDefinitionWire
    (definition : WireProjectionCardinalityDef) : WireCardinalityDef where
  marker := definition.marker
  minimum := definition.min
  bound := definition.n
  role := definition.role
  filler := definition.filler

def cardinalityDefinitionKey
    (definition : WireCardinalityDef) : Nat × Bool × Nat × Nat × Nat :=
  (definition.marker, definition.minimum, definition.bound,
    definition.role, definition.filler)

def projectionExactMaximumIndices
    (definitions : List WireProjectionCardinalityDef) : List Nat :=
  definitions.zipIdx.filterMap fun (definition, index) =>
    if definition.exact && !definition.min then some index else none

def projectionExactMinimumIndices
    (definitions : List WireProjectionCardinalityDef) : List Nat :=
  definitions.zipIdx.filterMap fun (definition, index) =>
    if definition.exact && definition.min then some index else none

def normalizedSourceClauses
    (wire : WireNormalizedCardinalityTaxonomyCertificate) : List WireClause :=
  wire.normalization.map (·.source)

structure WireDirectCardinalityTaxonomyPublication where
  version : Nat
  common : WireDirectCardinalityCommonSource
  document : WireSourceBoundCardinalityTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireDirectCardinalityTaxonomyPublication.sourceBoundB
    (wire : WireDirectCardinalityTaxonomyPublication) : Bool :=
  decide (
    wire.common.projection.variable_count = wire.document.source.certificate.variable_count ∧
    wire.common.projection.concepts.length = wire.document.source.certificate.concept_count ∧
    wire.common.projection.roles.length = wire.document.source.certificate.role_count ∧
    wire.common.projection.target = normalizedSourceClauses wire.document.source ∧
    wire.document.source.certificate.definitions.map cardinalityDefinitionKey =
      wire.common.projection.definitions.map
        (cardinalityDefinitionKey ∘ projectionDefinitionWire) ∧
    wire.document.source.certificate.exact_maximums =
      projectionExactMaximumIndices wire.common.projection.definitions ∧
    wire.document.source.certificate.exact_definitions =
      projectionExactMinimumIndices wire.common.projection.definitions)

def conceptEntryBoundTo
    (entry : ExactCardinalityConceptEntry)
    (target : DecodedNormalizedCardinalityTaxonomyCertificate)
    (exact : DecodedExactCardinalityTaxonomyCertificate) : Prop :=
  entry.cell.natOntology = mapOntology target.target.ontology ∧
    entry.cell.natDefinitions = target.target.definitions.map mapCardinalityDef ∧
    entry.cell.natExactDefinitions.toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset

instance {entry : ExactCardinalityConceptEntry}
    {target : DecodedNormalizedCardinalityTaxonomyCertificate}
    {exact : DecodedExactCardinalityTaxonomyCertificate} :
    Decidable (conceptEntryBoundTo entry target exact) := by
  unfold conceptEntryBoundTo
  infer_instance

def subsumptionEntryBoundTo
    (entry : ExactCardinalitySubsumptionEntry)
    (target : DecodedNormalizedCardinalityTaxonomyCertificate)
    (exact : DecodedExactCardinalityTaxonomyCertificate) : Prop :=
  entry.cell.natOntology = mapOntology target.target.ontology ∧
    entry.cell.natDefinitions = target.target.definitions.map mapCardinalityDef ∧
    entry.cell.natExactDefinitions.toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset

instance {entry : ExactCardinalitySubsumptionEntry}
    {target : DecodedNormalizedCardinalityTaxonomyCertificate}
    {exact : DecodedExactCardinalityTaxonomyCertificate} :
    Decidable (subsumptionEntryBoundTo entry target exact) := by
  unfold subsumptionEntryBoundTo
  infer_instance

structure DecodedDirectCardinalityTaxonomyPublication where
  common : DecodedDirectCardinalityCommonSource
  taxonomy : DecodedNormalizedCardinalityTaxonomyCertificate
  exact : DecodedExactCardinalityTaxonomyCertificate
  variableCount : common.projection.variableCount = taxonomy.target.variableCount
  conceptCount : common.projection.concepts.length = taxonomy.target.conceptCount
  roleCount : common.projection.roles.length = taxonomy.target.roleCount
  sourceExact : mapOntology common.projection.target =
    mapOntology taxonomy.normalization.source
  definitionsExact : common.natDefinitions =
    taxonomy.target.definitions.map mapCardinalityDef
  pairedExact : (pairedExactDefinitions common.projection.semanticPairs |>
    List.map mapCardinalityDef).toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset
  conceptCellsBound : exact.covered.concepts.Forall fun entry =>
    conceptEntryBoundTo entry taxonomy exact
  subsumptionCellsBound : exact.covered.subsumptions.Forall fun entry =>
    subsumptionEntryBoundTo entry taxonomy exact

def WireDirectCardinalityTaxonomyPublication.decode
    (wire : WireDirectCardinalityTaxonomyPublication) :
    Except String DecodedDirectCardinalityTaxonomyPublication := do
  if _hversion : wire.version = 1 then
    if _hdocument : wire.document.check = true then
      if _hbound : wire.sourceBoundB = true then do
        let common ← wire.common.decode
        let taxonomy ← wire.document.source.decode
        let exact ← wire.document.source.certificate.decodeExact
        if hv : common.projection.variableCount = taxonomy.target.variableCount then
          if hc : common.projection.concepts.length = taxonomy.target.conceptCount then
            if hr : common.projection.roles.length = taxonomy.target.roleCount then
              if hs : mapOntology common.projection.target =
                  mapOntology taxonomy.normalization.source then
                if hd : common.natDefinitions =
                    taxonomy.target.definitions.map mapCardinalityDef then
                  if hp : (pairedExactDefinitions common.projection.semanticPairs |>
                      List.map mapCardinalityDef).toFinset =
                      (exact.exactDefinitions.map mapCardinalityDef).toFinset then
                    if hconcepts : exact.covered.concepts.Forall fun entry =>
                        conceptEntryBoundTo entry taxonomy exact then
                      if hsubsumptions : exact.covered.subsumptions.Forall fun entry =>
                          subsumptionEntryBoundTo entry taxonomy exact then
                        return {
                          common
                          taxonomy
                          exact
                          variableCount := hv
                          conceptCount := hc
                          roleCount := hr
                          sourceExact := hs
                          definitionsExact := hd
                          pairedExact := hp
                          conceptCellsBound := hconcepts
                          subsumptionCellsBound := hsubsumptions
                        }
                      else throw "an exact cardinality subsumption cell describes a different target"
                    else throw "an exact cardinality concept cell describes a different target"
                  else throw "taxonomy exact definitions differ from complementary-pair provenance"
                else throw "taxonomy directional definitions differ from the direct projection"
              else throw "direct cardinality target differs from normalized publication source"
            else throw "direct cardinality role dimension differs from publication"
          else throw "direct cardinality concept dimension differs from publication"
        else throw "direct cardinality variable dimension differs from publication"
      else .error "direct cardinality source and publication are not bound"
    else .error "source-bound cardinality taxonomy publication rejected"
  else .error s!"unsupported direct cardinality publication version {wire.version}"

def WireDirectCardinalityTaxonomyPublication.check
    (wire : WireDirectCardinalityTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectCardinalityTaxonomyPublication.subsumption_answer_iff_common
    (decoded : DecodedDirectCardinalityTaxonomyPublication)
    (entry : ExactCardinalitySubsumptionEntry)
    (hentry : entry ∈ decoded.exact.covered.subsumptions)
    (sub sup : Fin decoded.common.projection.concepts.length)
    (hsub : entry.sub = sub.val) (hsup : entry.sup = sup.val) :
    entry.natDecision.answer = true ↔ decoded.common.CommonEntails sub sup := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.subsumptionCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetSub : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount sub
  let targetSup : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount sup
  have hnormalized :
      EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val ↔
        EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := by
    exact (entailsWithExact_mapModelEquivalent_iff
      decoded.taxonomy.normalization.equivalent
      (decoded.taxonomy.target.definitions.map mapCardinalityDef)
      (decoded.exact.exactDefinitions.map mapCardinalityDef)
      targetSub.val targetSup.val).symm
  calc
    entry.natDecision.answer = true
        ↔ EntailsSubWithExactCardinality entry.cell.natOntology
            entry.cell.natDefinitions entry.cell.natExactDefinitions
            entry.sub entry.sup := entry.natDecision.answer_eq_true_iff
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := by
        rw [hontology, hdefinitions, hsub, hsup]
        simpa [targetSub, targetSup] using
          (entailsWithExact_congr_toFinset
            (ontology := mapOntology decoded.taxonomy.target.ontology)
            (definitions := decoded.taxonomy.target.definitions.map mapCardinalityDef)
            (sub := sub.val) (sup := sup.val) hexact)
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := hnormalized
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.target)
          decoded.common.natDefinitions
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          sub.val sup.val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetSub, targetSup]
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.target)
          decoded.common.natDefinitions
          ((pairedExactDefinitions decoded.common.projection.semanticPairs).map
            mapCardinalityDef) sub.val sup.val := by
        exact (entailsWithExact_congr_toFinset decoded.pairedExact.symm)
    _ ↔ EntailsSubWithExactCardinality decoded.common.projection.target
          decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) sub sup :=
        (entailsWithExact_mapOntology_iff decoded.common.projection.target
          decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) sub sup).symm
    _ ↔ decoded.common.TargetEntails sub sup :=
      decoded.common.exact_entails_iff_target sub sup
    _ ↔ decoded.common.CommonEntails sub sup :=
      (decoded.common.entails_target_iff sub sup).symm

theorem DecodedDirectCardinalityTaxonomyPublication.concept_answer_iff_common
    (decoded : DecodedDirectCardinalityTaxonomyPublication)
    (entry : ExactCardinalityConceptEntry)
    (hentry : entry ∈ decoded.exact.covered.concepts)
    (concept : Fin decoded.common.projection.concepts.length)
    (hconcept : entry.coordinate = concept.val) :
    entry.natDecision.answer = true ↔
      decoded.common.CommonUnsatisfiable concept := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.conceptCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetConcept : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount concept
  have hnormalized :
      UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val ↔
        UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := by
    exact (unsatisfiableWithExact_mapModelEquivalent_iff
      decoded.taxonomy.normalization.equivalent
      (decoded.taxonomy.target.definitions.map mapCardinalityDef)
      (decoded.exact.exactDefinitions.map mapCardinalityDef)
      targetConcept.val).symm
  calc
    entry.natDecision.answer = true
        ↔ UnsatisfiableConceptWithExactCardinality entry.cell.natOntology
            entry.cell.natDefinitions entry.cell.natExactDefinitions
            entry.coordinate := entry.natDecision.answer_eq_true_iff
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := by
        rw [hontology, hdefinitions, hconcept]
        simpa [targetConcept] using
          (unsatisfiableWithExact_congr_toFinset
            (ontology := mapOntology decoded.taxonomy.target.ontology)
            (definitions := decoded.taxonomy.target.definitions.map mapCardinalityDef)
            (concept := concept.val) hexact)
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := hnormalized
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.target)
          decoded.common.natDefinitions
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          concept.val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetConcept]
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.target)
          decoded.common.natDefinitions
          ((pairedExactDefinitions decoded.common.projection.semanticPairs).map
            mapCardinalityDef) concept.val := by
        exact (unsatisfiableWithExact_congr_toFinset decoded.pairedExact.symm)
    _ ↔ UnsatisfiableConceptWithExactCardinality
          decoded.common.projection.target decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) concept :=
        (unsatisfiableWithExact_mapOntology_iff decoded.common.projection.target
          decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) concept).symm
    _ ↔ decoded.common.TargetUnsatisfiable concept :=
      decoded.common.exact_unsatisfiable_iff_target concept
    _ ↔ decoded.common.CommonUnsatisfiable concept :=
      (decoded.common.unsatisfiable_target_iff concept).symm

def DecodedDirectCardinalityTaxonomyPublication.CommonSemantics
    (decoded : DecodedDirectCardinalityTaxonomyPublication) : Prop :=
  (∀ concept : Fin decoded.common.projection.concepts.length,
      concept.val ∈ decoded.exact.namedNats →
      ∃ entry : ExactCardinalityConceptEntry,
        entry ∈ decoded.exact.covered.concepts ∧
        entry.coordinate = concept.val ∧
        (entry.natDecision.answer = true ↔
          decoded.common.CommonUnsatisfiable concept)) ∧
  (∀ sub sup : Fin decoded.common.projection.concepts.length,
      sub.val ∈ decoded.exact.namedNats →
      sup.val ∈ decoded.exact.namedNats →
      ∃ entry : ExactCardinalitySubsumptionEntry,
        entry ∈ decoded.exact.covered.subsumptions ∧
        entry.sub = sub.val ∧ entry.sup = sup.val ∧
        (entry.natDecision.answer = true ↔
          decoded.common.CommonEntails sub sup))

theorem DecodedDirectCardinalityTaxonomyPublication.common_semantics
    (decoded : DecodedDirectCardinalityTaxonomyPublication) :
    decoded.CommonSemantics := by
  constructor
  · intro concept hnamed
    rcases decoded.exact.covered.conceptCovered concept.val hnamed with
      ⟨entry, hentry, hcoordinate⟩
    exact ⟨entry, hentry, hcoordinate,
      decoded.concept_answer_iff_common entry hentry concept hcoordinate⟩
  · intro sub sup hsub hsup
    rcases decoded.exact.covered.subsumptionCovered sub.val hsub sup.val hsup with
      ⟨entry, hentry, hsubCoordinate, hsupCoordinate⟩
    exact ⟨entry, hentry, hsubCoordinate, hsupCoordinate,
      decoded.subsumption_answer_iff_common entry hentry sub sup
        hsubCoordinate hsupCoordinate⟩

theorem WireDirectCardinalityTaxonomyPublication.check_sound
    (wire : WireDirectCardinalityTaxonomyPublication)
    (decoded : DecodedDirectCardinalityTaxonomyPublication)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true) :
    decoded.CommonSemantics := decoded.common_semantics

#print axioms DecodedDirectCardinalityTaxonomyPublication.common_semantics
#print axioms WireDirectCardinalityTaxonomyPublication.check_sound

end ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication
