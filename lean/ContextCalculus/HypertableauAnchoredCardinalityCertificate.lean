import ContextCalculus.HypertableauAnchoredCardinality
import ContextCalculus.HypertableauAnchoredEqualityCertificate
import ContextCalculus.HypertableauRegularCardinalityCertificate

/-! # Executable anchored equality and cardinality certificates -/

namespace ContextCalculus.Hypertableau
namespace AnchoredForestDomain

structure FiniteAnchoredCardinalityEqCertificate
    (eqNodeCount regularNodeCount conceptCount roleCount variableCount : Nat) where
  anchored : FiniteAnchoredEqCertificate
    eqNodeCount regularNodeCount conceptCount roleCount variableCount
  slots : List (Fin regularNodeCount × Fin roleCount × Fin regularNodeCount × Nat)
  definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))

def FiniteAnchoredCardinalityEqCertificate.slotAllowed
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) :
    Fin regularNodeCount → Fin roleCount → Fin regularNodeCount → Nat → Prop :=
  fun source role target slot => (source, role, target, slot) ∈ certificate.slots

def FiniteAnchoredCardinalityEqCertificate.regularCardinality
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) :
    FiniteRegularCardinalityCertificate
      regularNodeCount conceptCount roleCount variableCount where
  base := certificate.anchored.regular
  slots := certificate.slots
  definitions := certificate.definitions

def FiniteAnchoredCardinalityEqCertificate.anchorSafeB
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (witness : Fin arity → Fin regularNodeCount) : Bool :=
  (List.finRange arity).all fun left =>
    (List.finRange arity).all fun right =>
      decide (left = right) ||
        !(decide (NominalAnchor certificate.anchored.nominalRoot (witness left))) ||
        decide (witness left ≠ witness right)

theorem FiniteAnchoredCardinalityEqCertificate.anchorSafeB_sound
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (witness : Fin arity → Fin regularNodeCount)
    (hcheck : certificate.anchorSafeB witness = true) :
    AnchorSafeWitnesses (NominalAnchor certificate.anchored.nominalRoot) witness := by
  simp only [FiniteAnchoredCardinalityEqCertificate.anchorSafeB,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcheck
  intro left right hanchor hequal
  rcases hcheck left (List.mem_finRange left) right (List.mem_finRange right) with
    (hsame | hnotAnchor) | hdifferent
  · exact hsame
  · have hfalse : decide
        (NominalAnchor certificate.anchored.nominalRoot (witness left)) = false := by
      simpa using hnotAnchor
    exact False.elim ((decide_eq_false_iff_not.mp hfalse) hanchor)
  · exact False.elim (hdifferent hequal)

def FiniteAnchoredCardinalityEqCertificate.checkMinimum
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  (List.finRange regularNodeCount).all fun source =>
    !(decide ((source, .pos definition.marker) ∈ certificate.anchored.regular.labels)) ||
      (allAssignments regularNodeCount definition.bound).any fun witness =>
        ((List.finRange definition.bound).all fun index =>
          decide ((definition.role, certificate.anchored.regular.redirect source,
            witness index) ∈ certificate.anchored.regular.edges) &&
          decide ((source, definition.role, witness index, index.1) ∈
            certificate.slots) &&
          decide ((witness index, .pos definition.filler) ∈
            certificate.anchored.regular.labels)) &&
        certificate.anchorSafeB witness

theorem FiniteAnchoredCardinalityEqCertificate.checkMinimum_sound
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hcheck : certificate.checkMinimum definition = true) : ∀ node,
    certificate.anchored.regular.state.label node (.pos definition.marker) →
    ∃ witness : Fin definition.bound → Fin regularNodeCount,
      (∀ index, certificate.anchored.regular.state.edge definition.role
        (certificate.anchored.regular.redirect node) (witness index)) ∧
      (∀ index, certificate.slotAllowed node definition.role
        (witness index) index.1) ∧
      (∀ index, certificate.anchored.regular.state.label (witness index)
        (.pos definition.filler)) ∧
      AnchorSafeWitnesses (NominalAnchor certificate.anchored.nominalRoot) witness := by
  intro node hmarker
  simp only [FiniteAnchoredCardinalityEqCertificate.checkMinimum] at hcheck
  have hsource := (List.all_eq_true.mp hcheck) node (List.mem_finRange node)
  have hmarkerB : decide
      ((node, .pos definition.marker) ∈ certificate.anchored.regular.labels) = true :=
    decide_eq_true hmarker
  rw [hmarkerB] at hsource
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hsource
  rcases hsource with ⟨witness, _, hcandidate⟩
  simp only [Bool.and_eq_true] at hcandidate
  rcases hcandidate with ⟨hwitness, hsafe⟩
  refine ⟨witness, ?_, ?_, ?_, certificate.anchorSafeB_sound witness hsafe⟩
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [FiniteAnchoredCardinalityEqCertificate.slotAllowed] using h.1.2
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

def FiniteAnchoredCardinalityEqCertificate.check
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.anchored.check &&
  (List.finRange regularNodeCount).all (fun source =>
    certificate.anchored.regular.edges.all fun edge =>
      !(decide (edge.2.1 = certificate.anchored.regular.redirect source)) ||
        decide ((source, edge.1, edge.2.2, 0) ∈ certificate.slots)) &&
  certificate.definitions.all fun definition =>
    match definition.kind with
    | .minimum => certificate.checkMinimum definition
    | .maximum => certificate.regularCardinality.checkDefinition definition

def FiniteAnchoredCardinalityEqCertificate.Valid
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount) : Prop :=
  certificate.anchored.check = true ∧
  (∀ source role target,
    certificate.anchored.regular.state.edge role
      (certificate.anchored.regular.redirect source) target →
      certificate.slotAllowed source role target 0) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .minimum → ∀ node,
    certificate.anchored.regular.state.label node (.pos definition.marker) →
    ∃ witness : Fin definition.bound → Fin regularNodeCount,
      (∀ index, certificate.anchored.regular.state.edge definition.role
        (certificate.anchored.regular.redirect node) (witness index)) ∧
      (∀ index, certificate.slotAllowed node definition.role
        (witness index) index.1) ∧
      (∀ index, certificate.anchored.regular.state.label (witness index)
        (.pos definition.filler)) ∧
      AnchorSafeWitnesses (NominalAnchor certificate.anchored.nominalRoot) witness) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .maximum → ∀ node,
    certificate.anchored.regular.state.label node (.pos definition.marker) →
    HasAtMost definition.bound
      (UnravellingAuthorizedKey certificate.anchored.regular.state
        certificate.anchored.regular.redirect certificate.slotAllowed node
        definition.role)) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .maximum →
      certificate.anchored.regular.rules.SyntacticallySimple definition.role)

theorem FiniteAnchoredCardinalityEqCertificate.check_sound
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) : certificate.Valid := by
  simp only [FiniteAnchoredCardinalityEqCertificate.check, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨hanchored, hzero⟩, hdefinitions⟩
  refine ⟨hanchored, ?_, ?_, ?_, ?_⟩
  · intro source role target hedge
    have h := hzero source (List.mem_finRange source)
      (role, certificate.anchored.regular.redirect source, target) hedge
    simpa [FiniteAnchoredCardinalityEqCertificate.slotAllowed] using h
  · intro definition hdefinition hkind
    have h := hdefinitions definition hdefinition
    simp only [hkind] at h
    exact certificate.checkMinimum_sound definition h
  · intro definition hdefinition hkind
    have h := hdefinitions definition hdefinition
    simp only [hkind] at h
    exact certificate.regularCardinality.checkDefinition_maximum_sound definition h hkind
  · intro definition hdefinition hkind
    have h := hdefinitions definition hdefinition
    simp only [hkind] at h
    exact certificate.regularCardinality.checkDefinition_maximum_simple definition h hkind

theorem FiniteAnchoredCardinalityEqCertificate.check_models
    [NeZero regularNodeCount]
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    let interpretation := AnchoredForestDomain.interpretation
      certificate.anchored.regular.state certificate.anchored.regular.redirect
      certificate.slotAllowed (NominalAnchor certificate.anchored.nominalRoot)
      certificate.anchored.regular.rules certificate.anchored.nominalRoot
    interpretation.models certificate.anchored.equality.base.ontology ∧
      interpretation.modelsCardinalityDefs certificate.definitions := by
  have hvalid := certificate.check_sound hcheck
  have hanchored := certificate.anchored.check_sound hvalid.1
  have hanchoredParts :
      anchoredRegularCheck certificate.anchored.regular
          certificate.anchored.nominalRoot = true ∧
        finitePremisesB (regularSatCertificate certificate.anchored.regular)
          certificate.anchored.regular.redirect certificate.anchored.nominalRoot = true := by
    simpa [anchoredCheck, Bool.and_eq_true] using hanchored.2.2.2
  have hpremises := finitePremisesB_sound
    (regularSatCertificate certificate.anchored.regular)
    certificate.anchored.regular.redirect certificate.anchored.nominalRoot
    hanchoredParts.2
  rw [regularSatCertificate_state] at hpremises
  let interpretation := AnchoredForestDomain.interpretation
    certificate.anchored.regular.state certificate.anchored.regular.redirect
    certificate.slotAllowed (NominalAnchor certificate.anchored.nominalRoot)
    certificate.anchored.regular.rules certificate.anchored.nominalRoot
  have hontology : interpretation.models certificate.anchored.regular.ontology :=
    anchoredCheck_models_with_slots certificate.anchored.regular
      certificate.anchored.nominalRoot certificate.slotAllowed hanchored.2.2.2
      hvalid.2.1
  have hcardinality : interpretation.modelsCardinalityDefs certificate.definitions :=
    interpretation_modelsCardinalityDefs certificate.anchored.regular.state
      certificate.anchored.regular.redirect certificate.slotAllowed
      (NominalAnchor certificate.anchored.nominalRoot)
      certificate.anchored.regular.rules certificate.anchored.nominalRoot
      hpremises.1 hpremises.2.1 certificate.definitions hvalid.2.2.1
      hvalid.2.2.2.1 hvalid.2.2.2.2
  exact ⟨hanchored.1 ▸ hontology, hcardinality⟩

theorem FiniteAnchoredCardinalityEqCertificate.check_sat_source_label
    [NeZero regularNodeCount]
    (certificate : FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) (source : Fin eqNodeCount)
    (lit : Lit (Fin conceptCount))
    (hlabel : certificate.anchored.equality.base.state.label source lit) :
    let value := AnchoredForestDomain.root certificate.anchored.regular.state
      certificate.anchored.regular.redirect certificate.slotAllowed
      (NominalAnchor certificate.anchored.nominalRoot)
      (certificate.anchored.classMap source)
    (interpretation certificate.anchored.regular.state
      certificate.anchored.regular.redirect certificate.slotAllowed
      (NominalAnchor certificate.anchored.nominalRoot)
      certificate.anchored.regular.rules
      certificate.anchored.nominalRoot).satLit lit value := by
  have hvalid := certificate.check_sound hcheck
  have hanchored := certificate.anchored.check_sound hvalid.1
  have himage := hanchored.2.2.1
  have hregularLabel : certificate.anchored.regular.state.label
      (certificate.anchored.classMap source) lit :=
    (himage.1 (certificate.anchored.classMap source) lit).2
      ⟨source, List.mem_finRange source, rfl, hlabel⟩
  have hanchoredParts :
      anchoredRegularCheck certificate.anchored.regular
          certificate.anchored.nominalRoot = true ∧
        finitePremisesB (regularSatCertificate certificate.anchored.regular)
          certificate.anchored.regular.redirect certificate.anchored.nominalRoot = true := by
    simpa [anchoredCheck, Bool.and_eq_true] using hanchored.2.2.2
  have hpremises := finitePremisesB_sound
    (regularSatCertificate certificate.anchored.regular)
    certificate.anchored.regular.redirect certificate.anchored.nominalRoot
    hanchoredParts.2
  rw [regularSatCertificate_state] at hpremises
  exact interpretation_sat_label certificate.anchored.regular.state
    certificate.anchored.regular.redirect certificate.slotAllowed
    (NominalAnchor certificate.anchored.nominalRoot)
    certificate.anchored.regular.rules certificate.anchored.nominalRoot
    hpremises.1 hpremises.2.1
    (AnchoredForestDomain.root certificate.anchored.regular.state
      certificate.anchored.regular.redirect certificate.slotAllowed
      (NominalAnchor certificate.anchored.nominalRoot)
      (certificate.anchored.classMap source)) lit hregularLabel

private def noNominals : Fin 1 → Option (Fin 1) := fun _ => none
private def oneNominal : Fin 1 → Option (Fin 1) := fun _ => some 0
private def repeatedWitness : Fin 2 → Fin 1 := fun _ => 0

private def emptyEquality : FiniteEqCertificate 1 1 1 1 where
  base := { ontology := [], labels := [], edges := [], obligations := [] }
  equalities := []
  representative := id
  representativePath := fun _ => []

private def emptyRegular : FiniteRegularCertificate 1 1 1 1 where
  labels := []
  edges := []
  obligations := []
  redirect := id
  cover := []
  subRoles := []
  inverseRoles := []
  chains := []
  reflexiveRoles := []
  roleClauses := []
  residual := []

private def anchoredFixture
    (nominalRoot : Fin 1 → Option (Fin 1)) :
    FiniteAnchoredEqCertificate 1 1 1 1 1 where
  equality := emptyEquality
  regular := emptyRegular
  classMap := id
  nominalRoot := nominalRoot

private def anchorSafetyFixture
    (nominalRoot : Fin 1 → Option (Fin 1)) :
    FiniteAnchoredCardinalityEqCertificate 1 1 1 1 1 where
  anchored := anchoredFixture nominalRoot
  slots := []
  definitions := []

example : (anchorSafetyFixture noNominals).anchorSafeB repeatedWitness = true := by
  native_decide

example : (anchorSafetyFixture oneNominal).anchorSafeB repeatedWitness = false := by
  native_decide

#print axioms FiniteAnchoredCardinalityEqCertificate.anchorSafeB_sound
#print axioms FiniteAnchoredCardinalityEqCertificate.checkMinimum_sound
#print axioms FiniteAnchoredCardinalityEqCertificate.check_sound
#print axioms FiniteAnchoredCardinalityEqCertificate.check_models
#print axioms FiniteAnchoredCardinalityEqCertificate.check_sat_source_label

end AnchoredForestDomain
end ContextCalculus.Hypertableau
