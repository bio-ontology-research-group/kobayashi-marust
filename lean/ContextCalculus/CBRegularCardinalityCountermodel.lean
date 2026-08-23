import ContextCalculus.CBRegularNominalCountermodel
import ContextCalculus.HypertableauAnchoredCardinalityCertificate
import ContextCalculus.HypertableauCardinalityProjection

/-!
# Cardinality-aware regular CB countermodels

CB's normalized `func` and `atMost` clauses are unconditional. HT's executable
cardinality definitions are marker guarded. This bridge records and checks the
missing semantic obligations explicitly: every selected marker denotes the
whole domain, and the filler selected for functionality also denotes the whole
domain. Under those obligations, checked maximum definitions imply exactly the
CB functionality and qualified-at-most source clauses.
-/

namespace ContextCalculus.CBRegularCardinalityCountermodel

open ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau

inductive SafeClause (Concept Role Individual : Type) where
  | core (clause : CBRegularNominalCountermodel.SafeClause Concept Role Individual)
  | func (role : Role) (marker filler : Concept)
  | atMost (bound : Nat) (role : Role) (filler marker : Concept)
deriving DecidableEq, Repr

def SafeClause.toOClause : SafeClause Concept Role Individual →
    OClause Concept Role Individual
  | .core clause => clause.toOClause
  | .func role _ _ => .func role
  | .atMost bound role filler _ => .atMost bound role filler

def SafeClause.definition? : SafeClause Concept Role Individual →
    Option (CardinalityDef Concept Role)
  | .core _ => none
  | .func role marker filler => some {
      marker, kind := .maximum, bound := 1, role, filler }
  | .atMost bound role filler marker => some {
      marker, kind := .maximum, bound, role, filler }

structure SafeSource (Concept Role Individual : Type) where
  clauses : List (SafeClause Concept Role Individual)
  chains : List (ContextCalculus.CBRegularRoleCountermodel.BinaryChain Role)

def SafeSource.core (source : SafeSource Concept Role Individual) :
    CBRegularNominalCountermodel.SafeSource Concept Role Individual where
  clauses := source.clauses.filterMap fun clause => match clause with
    | .core core => some core
    | .func _ _ _ | .atMost _ _ _ _ => none
  chains := source.chains

def SafeSource.definitions (source : SafeSource Concept Role Individual) :
    List (CardinalityDef Concept Role) :=
  source.clauses.filterMap SafeClause.definition?

def SafeSource.toSource (source : SafeSource Concept Role Individual) :
    SourceOntology Concept Role Individual where
  clauses := source.clauses.map SafeClause.toOClause
  chains := source.chains.map
    ContextCalculus.CBRegularRoleCountermodel.BinaryChain.toRoleChain

def universalConceptClause (nodeVar : Variable) (concept : Concept) :
    Hypertableau.Clause Variable Concept Role where
  body := []
  head := [.concept (.pos concept) nodeVar]

def SafeClause.activationClauses (nodeVar : Variable) :
    SafeClause Concept Role Individual →
      List (Hypertableau.Clause Variable Concept Role)
  | .core _ => []
  | .func _ marker filler =>
      [universalConceptClause nodeVar marker,
       universalConceptClause nodeVar filler]
  | .atMost _ _ _ marker => [universalConceptClause nodeVar marker]

def SafeSource.activationClauses (source : SafeSource Concept Role Individual)
    (nodeVar : Variable) : List (Hypertableau.Clause Variable Concept Role) :=
  source.clauses.flatMap (SafeClause.activationClauses nodeVar)

theorem concept_everywhere_of_models_universal
    (interpretation : Hypertableau.Interp D Concept Role)
    (nodeVar : Variable) (concept : Concept)
    (hmodels : interpretation.modelsClause
      (universalConceptClause (Role := Role) nodeVar concept)) :
    ∀ value, interpretation.concept concept value := by
  intro value
  rcases hmodels (fun _ => value) (by simp [universalConceptClause]) with
    ⟨atom, hmem, hsat⟩
  simp only [universalConceptClause, List.mem_singleton] at hmem
  subst atom
  simpa [Hypertableau.Interp.satAtom, Hypertableau.Interp.satLit, Lit.pos]
    using hsat

theorem atMost_of_maximum_definition
    (interpretation : Hypertableau.Interp D Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .maximum)
    (hmodels : interpretation.modelsCardinalityDef definition)
    (hmarker : ∀ value, interpretation.concept definition.marker value)
    (source : D) (values : Fin (definition.bound + 1) → D)
    (hsuccessors : ∀ index,
      interpretation.role definition.role source (values index) ∧
      interpretation.concept definition.filler (values index)) :
    ∃ left right, left ≠ right ∧ values left = values right := by
  have hnotInjective := interpretation.maximum_forces_merge definition hkind
    hmodels source (hmarker source) values hsuccessors
  rcases Function.not_injective_iff.mp hnotInjective with
    ⟨left, right, hequal, hne⟩
  exact ⟨left, right, hne, hequal⟩

theorem functional_of_maximum_one
    (interpretation : Hypertableau.Interp D Concept Role)
    (definition : CardinalityDef Concept Role)
    (hkind : definition.kind = .maximum)
    (hbound : definition.bound = 1)
    (hmodels : interpretation.modelsCardinalityDef definition)
    (hmarker : ∀ value, interpretation.concept definition.marker value)
    (hfiller : ∀ value, interpretation.concept definition.filler value) :
    ∀ source first second,
      interpretation.role definition.role source first →
      interpretation.role definition.role source second → first = second := by
  intro source first second hfirst hsecond
  let values : Fin 2 → D := fun index => if index = 0 then first else second
  have hmaximum : HasAtMost 1
      (interpretation.cardinalitySuccessor definition source) := by
    have := hmodels source (hmarker source)
    simpa [Interp.modelsCardinalityDef, hkind, hbound] using this
  have hsuccessors : ∀ index,
      interpretation.role definition.role source (values index) ∧
      interpretation.concept definition.filler (values index) := by
    intro index
    constructor
    · fin_cases index
      · simpa [values] using hfirst
      · simpa [values] using hsecond
    · exact hfiller (values index)
  have hnotInjective : ¬Function.Injective values :=
    not_injective_of_hasAtMost hmaximum values hsuccessors
  obtain ⟨left, right, hequal, hne⟩ :=
    Function.not_injective_iff.mp hnotInjective
  fin_cases left <;> fin_cases right
  · exact (hne rfl).elim
  · simpa [values] using hequal
  · simpa [values] using hequal.symm
  · exact (hne rfl).elim

theorem models_source_of_models_core_and_cardinality
    (interpretation : Hypertableau.Interp D Concept Role)
    (name : Individual → D)
    (source : SafeSource Concept Role Individual)
    (hcore : CBRoleChainEncoding.models
      (ContextCalculus.CBRegularRoleCountermodel.restrictHT interpretation name)
      source.core.toSource)
    (hdefinitions : interpretation.modelsCardinalityDefs source.definitions)
    (hmarkers : ∀ clause ∈ source.clauses, ∀ marker,
      (clause.definition?).map (fun definition => definition.marker) = some marker →
      ∀ value, interpretation.concept marker value)
    (hfunctionFillers : ∀ role marker filler,
      SafeClause.func role marker filler ∈ source.clauses →
      ∀ value, interpretation.concept filler value) :
    CBRoleChainEncoding.models
      (ContextCalculus.CBRegularRoleCountermodel.restrictHT interpretation name)
      source.toSource := by
  constructor
  · intro clause hclause
    simp only [SafeSource.toSource, List.mem_map] at hclause
    rcases hclause with ⟨sourceClause, hmem, rfl⟩
    cases sourceClause with
    | core coreClause =>
        apply hcore.1 coreClause.toOClause
        simp only [CBRegularNominalCountermodel.SafeSource.toSource,
          SafeSource.core, List.mem_map,
          List.mem_filterMap]
        exact ⟨coreClause, ⟨SafeClause.core coreClause, hmem, rfl⟩, rfl⟩
    | func role marker filler =>
        let definition : CardinalityDef Concept Role := {
          marker, kind := .maximum, bound := 1, role, filler }
        have hdefinition : definition ∈ source.definitions := by
          simp only [SafeSource.definitions, List.mem_filterMap]
          exact ⟨SafeClause.func role marker filler, hmem, rfl⟩
        have hmodels := hdefinitions definition hdefinition
        have hmarker : ∀ value, interpretation.concept marker value :=
          hmarkers (.func role marker filler) hmem marker (by rfl)
        have hfiller := hfunctionFillers role marker filler hmem
        simpa [SafeClause.toOClause, Eqv.satO,
          ContextCalculus.CBRegularRoleCountermodel.restrictHT, definition] using
          functional_of_maximum_one interpretation definition rfl rfl hmodels
            hmarker hfiller
    | atMost bound role filler marker =>
        let definition : CardinalityDef Concept Role := {
          marker, kind := .maximum, bound, role, filler }
        have hdefinition : definition ∈ source.definitions := by
          simp only [SafeSource.definitions, List.mem_filterMap]
          exact ⟨SafeClause.atMost bound role filler marker, hmem, rfl⟩
        have hmodels := hdefinitions definition hdefinition
        have hmarker : ∀ value, interpretation.concept marker value :=
          hmarkers (.atMost bound role filler marker) hmem marker (by rfl)
        intro element values hvalues
        exact atMost_of_maximum_definition interpretation definition rfl hmodels
          hmarker element values (by
            intro index
            simpa [definition,
              ContextCalculus.CBRegularRoleCountermodel.restrictHT] using hvalues index)
  · intro chain hchain
    apply hcore.2 chain
    have hchain' : chain ∈ source.chains.map
        ContextCalculus.CBRegularRoleCountermodel.BinaryChain.toRoleChain := by
      simpa only [SafeSource.toSource] using hchain
    simpa only [SafeSource.core,
      CBRegularNominalCountermodel.SafeSource.toSource] using hchain'

/-- Exact anchored-cardinality evidence yields a regular CB countermodel for
ALC, the equality-free RBox, nominals, global functionality, and global
qualified at-most clauses. -/
theorem checked_regular_cardinality_countermodel
    [NeZero eqNodeCount] [NeZero regularNodeCount]
    (certificate : AnchoredForestDomain.FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (sourceVar middle target : Fin variableCount)
    (hsourceTarget : sourceVar ≠ target)
    (hmiddleSource : middle ≠ sourceVar) (hmiddleTarget : middle ≠ target)
    (safe : SafeSource (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (individualRoot : Fin individualCount → Fin regularNodeCount)
    (sub sup : Fin conceptCount)
    (hroleClauses : certificate.anchored.regular.roleClauses =
      CBRegularRoleCountermodel.roleClauses sourceVar middle target safe.core.base)
    (hresidual : certificate.anchored.regular.residual =
      CBRegularRoleCountermodel.residual sourceVar target safe.core.base.clauses ++
        safe.activationClauses sourceVar)
    (hdefinitions : certificate.definitions = safe.definitions)
    (hnominalRoots : ∀ nominal,
      CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
        safe.core.clauses →
      certificate.anchored.nominalRoot nominal.concept =
        some (individualRoot nominal.individual))
    (hsub : certificate.anchored.equality.base.state.label 0 (.pos sub))
    (hnotSup : certificate.anchored.equality.base.state.label 0 (.negated sup))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBRoleChainEncoding.encode safe.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let slotAllowed := certificate.slotAllowed
  let anchor := AnchoredForestDomain.NominalAnchor certificate.anchored.nominalRoot
  let htModel := AnchoredForestDomain.interpretation
    certificate.anchored.regular.state certificate.anchored.regular.redirect
    slotAllowed anchor certificate.anchored.regular.rules
    certificate.anchored.nominalRoot
  let name : Fin individualCount →
      AnchoredForestDomain certificate.anchored.regular.state
        certificate.anchored.regular.redirect slotAllowed anchor := fun individual =>
    AnchoredForestDomain.root certificate.anchored.regular.state
      certificate.anchored.regular.redirect slotAllowed anchor
      (individualRoot individual)
  have hcheckedModels := certificate.check_models hcheck
  have hmodels : htModel.models certificate.anchored.equality.base.ontology := by
    simpa [htModel, slotAllowed, anchor] using hcheckedModels.1
  have hdefinitionModels : htModel.modelsCardinalityDefs safe.definitions := by
    simpa [htModel, slotAllowed, anchor, hdefinitions] using hcheckedModels.2
  have hroles : htModel.models
      ((CBRegularRoleCountermodel.roleClauses sourceVar middle target
        safe.core.base).map
        (NormalizedRoleClause.toClause (Concept := Fin conceptCount))) := by
    intro clause hclause
    apply hmodels clause
    rw [← (certificate.anchored.check_sound
      (certificate.check_sound hcheck).1).1]
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    left
    simpa [hroleClauses] using hclause
  have hresidualModels : htModel.models
      (CBRegularRoleCountermodel.residual sourceVar target
        safe.core.base.clauses ++ safe.activationClauses sourceVar) := by
    intro clause hclause
    apply hmodels clause
    rw [← (certificate.anchored.check_sound
      (certificate.check_sound hcheck).1).1]
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    right
    simpa [hresidual] using hclause
  have hbaseResidual : htModel.models
      (CBRegularRoleCountermodel.residual sourceVar target
        safe.core.base.clauses) := by
    intro clause hclause
    exact hresidualModels clause (List.mem_append_left _ hclause)
  have hbase : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT htModel name)
      safe.core.base.toSource :=
    CBRegularRoleCountermodel.models_source_of_models_ht htModel name
      sourceVar middle target hsourceTarget hmiddleSource hmiddleTarget
      safe.core.base hbaseResidual hroles
  have hnominal : ∀ nominal,
      CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
        safe.core.clauses → ∀ value,
      htModel.concept nominal.concept value ↔ value = name nominal.individual := by
    intro nominal hmem value
    simpa [htModel, name, slotAllowed, anchor] using
      AnchoredForestDomain.concept_nominal_iff
        certificate.anchored.regular.state certificate.anchored.regular.redirect
        slotAllowed anchor certificate.anchored.nominalRoot nominal.concept
        (individualRoot nominal.individual) (hnominalRoots nominal hmem) value
  have hcore : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT htModel name) safe.core.toSource :=
    CBRegularNominalCountermodel.models_source_of_models_base_and_nominals
      htModel name safe.core hbase hnominal
  have hactivation : htModel.models (safe.activationClauses sourceVar) := by
    intro clause hclause
    exact hresidualModels clause (List.mem_append_right _ hclause)
  have hmarkers : ∀ clause ∈ safe.clauses, ∀ marker,
      (clause.definition?).map (fun definition => definition.marker) = some marker →
      ∀ value, htModel.concept marker value := by
    intro clause hmem marker hmarker
    cases clause with
    | core coreClause => simp [SafeClause.definition?] at hmarker
    | func role selected filler =>
        simp only [SafeClause.definition?, Option.map_some, Option.some.injEq] at hmarker
        subst marker
        apply concept_everywhere_of_models_universal htModel sourceVar selected
        apply hactivation
        simp only [SafeSource.activationClauses, List.mem_flatMap]
        exact ⟨SafeClause.func role selected filler, hmem, by simp [SafeClause.activationClauses]⟩
    | atMost bound role filler selected =>
        simp only [SafeClause.definition?, Option.map_some, Option.some.injEq] at hmarker
        subst marker
        apply concept_everywhere_of_models_universal htModel sourceVar selected
        apply hactivation
        simp only [SafeSource.activationClauses, List.mem_flatMap]
        exact ⟨SafeClause.atMost bound role filler selected, hmem,
          by simp [SafeClause.activationClauses]⟩
  have hfunctionFillers : ∀ role marker filler,
      SafeClause.func role marker filler ∈ safe.clauses →
      ∀ value, htModel.concept filler value := by
    intro role marker filler hmem
    apply concept_everywhere_of_models_universal htModel sourceVar filler
    apply hactivation
    simp only [SafeSource.activationClauses, List.mem_flatMap]
    exact ⟨SafeClause.func role marker filler, hmem,
      by simp [SafeClause.activationClauses]⟩
  have hsourceModels : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT htModel name) safe.toSource :=
    models_source_of_models_core_and_cardinality htModel name safe hcore
      hdefinitionModels hmarkers hfunctionFillers
  let element := AnchoredForestDomain.root certificate.anchored.regular.state
    certificate.anchored.regular.redirect slotAllowed anchor
    (certificate.anchored.classMap 0)
  let model := CBRoleChainEncoding.extendModel safe.toSource
    (CBRegularRoleCountermodel.restrictHT htModel name) hsourceModels element
  refine ⟨_, model, element,
    CBRoleChainEncoding.models_extend safe.toSource
      (CBRegularRoleCountermodel.restrictHT htModel name) hsourceModels element,
    ?_, ?_⟩
  · have hsatisfied := certificate.check_sat_source_label hcheck 0 (.pos sub) hsub
    simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      CBRegularRoleCountermodel.restrictHT, htModel, element,
      Hypertableau.Interp.satLit, Lit.pos, slotAllowed, anchor] using hsatisfied
  · have hsatisfied := certificate.check_sat_source_label hcheck 0 (.negated sup) hnotSup
    simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      CBRegularRoleCountermodel.restrictHT, htModel, element,
      Hypertableau.Interp.satLit, Lit.negated, slotAllowed, anchor] using hsatisfied

#print axioms atMost_of_maximum_definition
#print axioms functional_of_maximum_one
#print axioms models_source_of_models_core_and_cardinality
#print axioms checked_regular_cardinality_countermodel

end ContextCalculus.CBRegularCardinalityCountermodel
