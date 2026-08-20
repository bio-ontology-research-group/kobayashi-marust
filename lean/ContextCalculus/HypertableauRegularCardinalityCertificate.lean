import ContextCalculus.HypertableauRegularCertificate

/-!
# Cardinality extension of regular HT certificates

Slots are explicit untrusted tuples. Minimum definitions require one authorized
slot per witness index; maximum definitions bound every authorized
`(target,slot)` key. Number-restricted roles must pass the executable syntactic
simple-role criterion, which proves regular closure adds no successors.
-/

namespace ContextCalculus.Hypertableau

structure FiniteRegularCardinalityCertificate
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteRegularCertificate nodeCount conceptCount roleCount variableCount
  slots : List (Fin nodeCount × Fin roleCount × Fin nodeCount × Nat)
  definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))

def FiniteRegularCardinalityCertificate.slotAllowed
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount) :
    Fin nodeCount → Fin roleCount → Fin nodeCount → Nat → Prop :=
  fun source role target slot =>
    (source, role, target, slot) ∈ certificate.slots

def FiniteRegularCardinalityCertificate.Valid
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount) : Prop :=
  certificate.base.Valid ∧
  (∀ source role target,
    certificate.base.state.edge role (certificate.base.redirect source) target →
      certificate.slotAllowed source role target 0) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .minimum → ∀ node,
    certificate.base.state.label node (.pos definition.marker) →
    ∃ witness : Fin definition.bound → Fin nodeCount,
      (∀ index, certificate.base.state.edge definition.role
        (certificate.base.redirect node) (witness index)) ∧
      (∀ index, certificate.slotAllowed node definition.role
        (witness index) index.1) ∧
      (∀ index, certificate.base.state.label (witness index)
        (.pos definition.filler))) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .maximum → ∀ node,
    certificate.base.state.label node (.pos definition.marker) →
    HasAtMost definition.bound
      (UnravellingAuthorizedKey certificate.base.state
        certificate.base.redirect certificate.slotAllowed node definition.role)) ∧
  (∀ definition ∈ certificate.definitions,
    definition.kind = .maximum →
      certificate.base.rules.SyntacticallySimple definition.role)

theorem FiniteRegularCardinalityCertificate.models
    [NeZero nodeCount]
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.Valid) :
    let interpretation := certificate.base.state.regularUnravelling
      certificate.base.redirect certificate.slotAllowed 0 certificate.base.rules
    interpretation.models certificate.base.ontology ∧
      interpretation.modelsCardinalityDefs certificate.definitions := by
  let interpretation := certificate.base.state.regularUnravelling
    certificate.base.redirect certificate.slotAllowed 0 certificate.base.rules
  have hontology : interpretation.models certificate.base.ontology := by
    apply regularUnravelling_models_partition_of_cover certificate.base.state
      certificate.base.redirect certificate.slotAllowed 0 certificate.base.rules
      certificate.base.coverRelation certificate.base.roleClauses
      certificate.base.residual
    · exact hvalid.1.1
    · exact hvalid.1.2.1
    · exact hvalid.1.2.2.1
    · exact hvalid.1.2.2.2.1
    · exact hvalid.1.2.2.2.2.1
    · exact hvalid.1.2.2.2.2.2.1
    · exact hvalid.2.1
    · exact certificate.base.coverClosed_covers hvalid.1.2.2.2.2.2.2.1
    · exact hvalid.1.2.2.2.2.2.2.2
  have hdirect := certificate.base.state.unravelling_modelsCardinalityDefs
    certificate.base.redirect certificate.slotAllowed 0 hvalid.1.2.2.2.1
    certificate.definitions hvalid.2.2.1 hvalid.2.2.2.1
  have hcardinality : interpretation.modelsCardinalityDefs
      certificate.definitions := by
    apply certificate.base.state.regularUnravelling_modelsCardinalityDefs_of_direct
      certificate.base.redirect certificate.slotAllowed 0 certificate.base.rules
      certificate.definitions hdirect
    intro definition hdefinition hmaximum
    exact certificate.base.rules.simpleExact_of_syntacticallySimple
      certificate.base.state certificate.base.redirect certificate.slotAllowed 0
      definition.role (hvalid.2.2.2.2 definition hdefinition hmaximum)
  exact ⟨hontology, hcardinality⟩

#print axioms FiniteRegularCardinalityCertificate.models

end ContextCalculus.Hypertableau
