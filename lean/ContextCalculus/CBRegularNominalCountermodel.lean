import ContextCalculus.CBRegularRoleCountermodel
import ContextCalculus.HypertableauAnchoredEqualityCertificate

/-!
# Nominal-aware regular CB countermodels

This layer adds source nominals to the equality-free regular role fragment.
The base clauses retain their production order and the nominal clauses follow
them.  Each source individual is interpreted by the canonical anchored root
selected for its nominal concept.  The anchored unravelling theorem then makes
that concept a genuine singleton, which is exactly the source semantics of
`OClause.nom`.
-/

namespace ContextCalculus.CBRegularNominalCountermodel

open ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBRegularRoleCountermodel
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau
open ContextCalculus.Hypertableau.AnchoredForestDomain

structure NominalClause (Concept Individual : Type) where
  concept : Concept
  individual : Individual
deriving DecidableEq, Repr

def NominalClause.toOClause (nominal : NominalClause Concept Individual) :
    OClause Concept Role Individual :=
  .nom nominal.concept nominal.individual

inductive SafeClause (Concept Role Individual : Type) where
  | base (clause : CBRegularRoleCountermodel.SafeClause Concept Role)
  | nominal (clause : NominalClause Concept Individual)
deriving DecidableEq, Repr

def SafeClause.toOClause : SafeClause Concept Role Individual →
    OClause Concept Role Individual
  | .base clause => clause.toOClause
  | .nominal clause => clause.toOClause

structure SafeSource (Concept Role Individual : Type) where
  clauses : List (SafeClause Concept Role Individual)
  chains : List (CBRegularRoleCountermodel.BinaryChain Role)

def SafeSource.base (source : SafeSource Concept Role Individual) :
    CBRegularRoleCountermodel.SafeSource Concept Role Individual where
  clauses := source.clauses.filterMap fun clause => match clause with
    | .base base => some base
    | .nominal _ => none
  chains := source.chains

def SafeSource.toSource (source : SafeSource Concept Role Individual) :
    CBRoleChainEncoding.SourceOntology Concept Role Individual where
  clauses := source.clauses.map SafeClause.toOClause
  chains := source.chains.map CBRegularRoleCountermodel.BinaryChain.toRoleChain

theorem models_source_of_models_base_and_nominals
    (interpretation : Hypertableau.Interp D Concept Role)
    (name : Individual → D)
    (source : SafeSource Concept Role Individual)
    (hbase : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT interpretation name)
      source.base.toSource)
    (hnominal : ∀ nominal, SafeClause.nominal nominal ∈ source.clauses → ∀ value,
      interpretation.concept nominal.concept value ↔
        value = name nominal.individual) :
    CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT interpretation name)
      source.toSource := by
  constructor
  · intro clause hclause
    simp only [SafeSource.toSource, List.mem_map] at hclause
    rcases hclause with ⟨sourceClause, hmem, rfl⟩
    cases sourceClause with
    | base baseClause =>
        apply hbase.1 baseClause.toOClause
        simp only [CBRegularRoleCountermodel.SafeSource.toSource, SafeSource.base,
          List.mem_map, List.mem_filterMap]
        exact ⟨baseClause, ⟨SafeClause.base baseClause, hmem, rfl⟩, rfl⟩
    | nominal nominal =>
        simpa [SafeClause.toOClause, NominalClause.toOClause, Eqv.satO,
          CBRegularRoleCountermodel.restrictHT] using
          hnominal nominal hmem
  · intro chain hchain
    apply hbase.2 chain
    have hchain' : chain ∈
        source.chains.map CBRegularRoleCountermodel.BinaryChain.toRoleChain := by
      simpa only [SafeSource.toSource] using hchain
    simpa only [SafeSource.base,
      CBRegularRoleCountermodel.SafeSource.toSource] using hchain'

/-- A checked anchored regular certificate gives a CB countermodel for the
base role fragment plus append-only nominal clauses.  The certificate's exact
HT ontology remains the base residual/RBox translation; nominal semantics is
provided by its checked canonical-root map. -/
theorem checked_regular_nominal_countermodel
    [NeZero eqNodeCount] [NeZero regularNodeCount]
    (certificate : FiniteAnchoredEqCertificate
      eqNodeCount regularNodeCount conceptCount roleCount variableCount)
    (sourceVar middle target : Fin variableCount)
    (hsourceTarget : sourceVar ≠ target)
    (hmiddleSource : middle ≠ sourceVar) (hmiddleTarget : middle ≠ target)
    (safe : SafeSource (Fin conceptCount) (Fin roleCount) (Fin individualCount))
    (individualRoot : Fin individualCount → Fin regularNodeCount)
    (sub sup : Fin conceptCount)
    (hroleClauses : certificate.regular.roleClauses =
      CBRegularRoleCountermodel.roleClauses sourceVar middle target safe.base)
    (hresidual : certificate.regular.residual =
      CBRegularRoleCountermodel.residual sourceVar target safe.base.clauses)
    (hnominalRoots : ∀ nominal,
      SafeClause.nominal nominal ∈ safe.clauses →
      certificate.nominalRoot nominal.concept =
        some (individualRoot nominal.individual))
    (hsub : certificate.equality.base.state.label 0 (.pos sub))
    (hnotSup : certificate.equality.base.state.label 0 (.negated sup))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBRoleChainEncoding.encode safe.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let slotAllowed : Fin regularNodeCount → Fin roleCount →
      Fin regularNodeCount → Nat → Prop := fun _ _ _ _ => True
  let anchor := NominalAnchor certificate.nominalRoot
  let htModel := AnchoredForestDomain.interpretation certificate.regular.state
    certificate.regular.redirect slotAllowed anchor certificate.regular.rules
    certificate.nominalRoot
  let name : Fin individualCount →
      AnchoredForestDomain certificate.regular.state certificate.regular.redirect
        slotAllowed anchor := fun individual =>
    AnchoredForestDomain.root certificate.regular.state
      certificate.regular.redirect slotAllowed anchor (individualRoot individual)
  have hmodels : htModel.models certificate.equality.base.ontology := by
    simpa [htModel, slotAllowed, anchor] using certificate.check_models hcheck
  have hroles : htModel.models
      ((CBRegularRoleCountermodel.roleClauses sourceVar middle target safe.base).map
        (NormalizedRoleClause.toClause (Concept := Fin conceptCount))) := by
    intro clause hclause
    apply hmodels clause
    rw [← (certificate.check_sound hcheck).1]
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    left
    simpa [hroleClauses] using hclause
  have hresidualModels : htModel.models
      (CBRegularRoleCountermodel.residual sourceVar target safe.base.clauses) := by
    intro clause hclause
    apply hmodels clause
    rw [← (certificate.check_sound hcheck).1]
    simp only [FiniteRegularCertificate.ontology, List.mem_append]
    right
    simpa [hresidual] using hclause
  have hbase : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT htModel name) safe.base.toSource :=
    CBRegularRoleCountermodel.models_source_of_models_ht htModel name
      sourceVar middle target hsourceTarget hmiddleSource hmiddleTarget safe.base
      hresidualModels hroles
  have hnominal : ∀ nominal,
      SafeClause.nominal nominal ∈ safe.clauses → ∀ value,
      htModel.concept nominal.concept value ↔ value = name nominal.individual := by
    intro nominal hmem value
    simpa [htModel, name, slotAllowed, anchor] using
      concept_nominal_iff certificate.regular.state certificate.regular.redirect
        slotAllowed anchor certificate.nominalRoot nominal.concept
        (individualRoot nominal.individual) (hnominalRoots nominal hmem) value
  have hsourceModels : CBRoleChainEncoding.models
      (CBRegularRoleCountermodel.restrictHT htModel name) safe.toSource :=
    models_source_of_models_base_and_nominals htModel name safe hbase hnominal
  let element := AnchoredForestDomain.root certificate.regular.state
    certificate.regular.redirect slotAllowed anchor (certificate.classMap 0)
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

#print axioms models_source_of_models_base_and_nominals
#print axioms checked_regular_nominal_countermodel

end ContextCalculus.CBRegularNominalCountermodel
