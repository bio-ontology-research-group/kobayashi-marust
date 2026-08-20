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

def FiniteRegularCardinalityCertificate.slotAuthorizedB
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (source : Fin nodeCount) (role : Fin roleCount)
    (entry : Fin nodeCount × Fin roleCount × Fin nodeCount × Nat) : Bool :=
  decide (entry.1 = source) && decide (entry.2.1 = role) &&
    decide ((role, certificate.base.redirect source, entry.2.2.1) ∈
      certificate.base.edges)

def FiniteRegularCardinalityCertificate.slotKeyInjectiveB
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (selection : Fin arity → Fin certificate.slots.length) : Bool :=
  (List.finRange arity).all fun left =>
    (List.finRange arity).all fun right =>
      decide (left = right) ||
        decide ((certificate.slots.get (selection left)).2.2 ≠
          (certificate.slots.get (selection right)).2.2)

theorem FiniteRegularCardinalityCertificate.slotKeyInjectiveB_eq_true
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (selection : Fin arity → Fin certificate.slots.length) :
    certificate.slotKeyInjectiveB selection = true ↔
      Function.Injective (fun index =>
        (certificate.slots.get (selection index)).2.2) := by
  simp only [FiniteRegularCardinalityCertificate.slotKeyInjectiveB,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h left right hequal
    rcases h left (List.mem_finRange left) right (List.mem_finRange right) with
      hsame | hdifferent
    · exact hsame
    · exact False.elim (hdifferent hequal)
  · intro hinjective left _ right _
    by_cases hsame : left = right
    · exact Or.inl hsame
    · exact Or.inr fun hequal => hsame (hinjective hequal)

def FiniteRegularCardinalityCertificate.checkDefinition
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount)) : Bool :=
  match definition.kind with
  | .minimum =>
      (List.finRange nodeCount).all fun source =>
        !(decide ((source, .pos definition.marker) ∈ certificate.base.labels)) ||
          (allAssignments nodeCount definition.bound).any fun witness =>
            (List.finRange definition.bound).all fun index =>
              decide ((definition.role, certificate.base.redirect source,
                witness index) ∈ certificate.base.edges) &&
              decide ((source, definition.role, witness index, index.1) ∈
                certificate.slots) &&
              decide ((witness index, .pos definition.filler) ∈
                certificate.base.labels)
  | .maximum =>
      certificate.base.syntacticallySimpleB definition.role &&
      (List.finRange nodeCount).all fun source =>
        !(decide ((source, .pos definition.marker) ∈ certificate.base.labels)) ||
          (allAssignments certificate.slots.length (definition.bound + 1)).all
            fun selection =>
              !((List.finRange (definition.bound + 1)).all fun index =>
                certificate.slotAuthorizedB source definition.role
                  (certificate.slots.get (selection index))) ||
              !certificate.slotKeyInjectiveB selection

def FiniteRegularCardinalityCertificate.check
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.base.check &&
  (List.finRange nodeCount).all (fun source =>
    certificate.base.edges.all fun edge =>
      !(decide (edge.2.1 = certificate.base.redirect source)) ||
        decide ((source, edge.1, edge.2.2, 0) ∈ certificate.slots)) &&
  certificate.definitions.all certificate.checkDefinition

theorem FiniteRegularCardinalityCertificate.checkDefinition_minimum_sound
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hcheck : certificate.checkDefinition definition = true)
    (hkind : definition.kind = .minimum) : ∀ node,
    certificate.base.state.label node (.pos definition.marker) →
    ∃ witness : Fin definition.bound → Fin nodeCount,
      (∀ index, certificate.base.state.edge definition.role
        (certificate.base.redirect node) (witness index)) ∧
      (∀ index, certificate.slotAllowed node definition.role
        (witness index) index.1) ∧
      (∀ index, certificate.base.state.label (witness index)
        (.pos definition.filler)) := by
  intro node hmarker
  simp only [FiniteRegularCardinalityCertificate.checkDefinition, hkind] at hcheck
  have hsource := (List.all_eq_true.mp hcheck) node (List.mem_finRange node)
  have hmarkerB : decide
      ((node, .pos definition.marker) ∈ certificate.base.labels) = true := by
    exact decide_eq_true hmarker
  rw [hmarkerB] at hsource
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hsource
  rcases hsource with ⟨witness, _, hwitness⟩
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  · intro index
    have h := (List.all_eq_true.mp hwitness) index (List.mem_finRange index)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2

theorem FiniteRegularCardinalityCertificate.checkDefinition_maximum_simple
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hcheck : certificate.checkDefinition definition = true)
    (hkind : definition.kind = .maximum) :
    certificate.base.rules.SyntacticallySimple definition.role := by
  simp only [FiniteRegularCardinalityCertificate.checkDefinition, hkind,
    Bool.and_eq_true] at hcheck
  exact certificate.base.syntacticallySimpleB_sound definition.role hcheck.1

theorem FiniteRegularCardinalityCertificate.checkDefinition_maximum_sound
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (definition : CardinalityDef (Fin conceptCount) (Fin roleCount))
    (hcheck : certificate.checkDefinition definition = true)
    (hkind : definition.kind = .maximum) : ∀ node,
    certificate.base.state.label node (.pos definition.marker) →
    HasAtMost definition.bound
      (UnravellingAuthorizedKey certificate.base.state
        certificate.base.redirect certificate.slotAllowed node definition.role) := by
  intro node hmarker
  simp only [FiniteRegularCardinalityCertificate.checkDefinition, hkind,
    Bool.and_eq_true] at hcheck
  have hsource := (List.all_eq_true.mp hcheck.2) node (List.mem_finRange node)
  have hmarkerB : decide
      ((node, .pos definition.marker) ∈ certificate.base.labels) = true := by
    exact decide_eq_true hmarker
  rw [hmarkerB] at hsource
  simp only [Bool.not_true, Bool.false_or] at hsource
  intro hatLeast
  rcases hatLeast with ⟨witness, hinjective, hauthorized⟩
  have hslotMem (index : Fin (definition.bound + 1)) :
      (node, definition.role, (witness index).1, (witness index).2) ∈
        certificate.slots := (hauthorized index).2
  choose selection hselection using fun index => List.get_of_mem (hslotMem index)
  have hselectionCheck := (List.all_eq_true.mp hsource) selection
    (mem_allAssignments certificate.slots.length (definition.bound + 1) selection)
  have hauthorizedB :
      (List.finRange (definition.bound + 1)).all (fun index =>
        certificate.slotAuthorizedB node definition.role
          (certificate.slots.get (selection index))) = true := by
    simp only [List.all_eq_true]
    intro index _
    have hentry := hselection index
    have hedge := (hauthorized index).1
    rw [hentry]
    simpa [FiniteRegularCardinalityCertificate.slotAuthorizedB,
      FiniteRegularCertificate.state] using hedge
  have hkeyInjective : Function.Injective (fun index =>
      (certificate.slots.get (selection index)).2.2) := by
    intro left right hequal
    apply hinjective
    change (certificate.slots.get (selection left)).2.2 =
      (certificate.slots.get (selection right)).2.2 at hequal
    rw [hselection left, hselection right] at hequal
    exact hequal
  have hkeyB : certificate.slotKeyInjectiveB selection = true :=
    (certificate.slotKeyInjectiveB_eq_true selection).mpr hkeyInjective
  rw [hauthorizedB, hkeyB] at hselectionCheck
  contradiction

theorem FiniteRegularCardinalityCertificate.check_sound
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) : certificate.Valid := by
  simp only [FiniteRegularCardinalityCertificate.check, Bool.and_eq_true,
    List.all_eq_true] at hcheck
  rcases hcheck with ⟨⟨hbase, hzero⟩, hdefinitions⟩
  refine ⟨certificate.base.check_sound hbase, ?_, ?_, ?_, ?_⟩
  · intro source role target hedge
    have h := hzero source (List.mem_finRange source)
      (role, certificate.base.redirect source, target) hedge
    simpa [FiniteRegularCardinalityCertificate.slotAllowed] using h
  · intro definition hdefinition hkind
    exact certificate.checkDefinition_minimum_sound definition
      (hdefinitions definition hdefinition) hkind
  · intro definition hdefinition hkind
    exact certificate.checkDefinition_maximum_sound definition
      (hdefinitions definition hdefinition) hkind
  · intro definition hdefinition hkind
    exact certificate.checkDefinition_maximum_simple definition
      (hdefinitions definition hdefinition) hkind

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

theorem FiniteRegularCardinalityCertificate.check_models
    [NeZero nodeCount]
    (certificate : FiniteRegularCardinalityCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : certificate.check = true) :
    let interpretation := certificate.base.state.regularUnravelling
      certificate.base.redirect certificate.slotAllowed 0 certificate.base.rules
    interpretation.models certificate.base.ontology ∧
      interpretation.modelsCardinalityDefs certificate.definitions :=
  certificate.models (certificate.check_sound hcheck)

private def cardinalityBase : FiniteRegularCertificate 1 2 1 1 where
  labels := [(0, .pos 0), (0, .pos 1)]
  edges := [(0, 0, 0)]
  obligations := []
  redirect := id
  cover := [(0, 0, 0)]
  subRoles := []
  inverseRoles := []
  chains := []
  reflexiveRoles := []
  roleClauses := []
  residual := []

private def minimumOne : CardinalityDef (Fin 2) (Fin 1) where
  marker := 0
  kind := .minimum
  bound := 1
  role := 0
  filler := 1

private def maximumOne : CardinalityDef (Fin 2) (Fin 1) where
  marker := 0
  kind := .maximum
  bound := 1
  role := 0
  filler := 1

private def maximumZero : CardinalityDef (Fin 2) (Fin 1) where
  marker := 0
  kind := .maximum
  bound := 0
  role := 0
  filler := 1

private def cardinalityGood : FiniteRegularCardinalityCertificate 1 2 1 1 where
  base := cardinalityBase
  slots := [(0, 0, 0, 0)]
  definitions := [minimumOne, maximumOne]

private def cardinalityBadMaximum :
    FiniteRegularCardinalityCertificate 1 2 1 1 where
  base := cardinalityBase
  slots := [(0, 0, 0, 0)]
  definitions := [maximumZero]

example : cardinalityGood.check = true := by native_decide
example : cardinalityBadMaximum.check = false := by native_decide

#print axioms FiniteRegularCardinalityCertificate.models
#print axioms FiniteRegularCardinalityCertificate.slotKeyInjectiveB_eq_true
#print axioms FiniteRegularCardinalityCertificate.checkDefinition_minimum_sound
#print axioms FiniteRegularCardinalityCertificate.checkDefinition_maximum_sound
#print axioms FiniteRegularCardinalityCertificate.check_sound
#print axioms FiniteRegularCardinalityCertificate.check_models

end ContextCalculus.Hypertableau
