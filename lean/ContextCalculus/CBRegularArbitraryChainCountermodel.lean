import ContextCalculus.CBRegularFreshCardinalityCountermodel
import ContextCalculus.CBSourceSignatureRenaming
import ContextCalculus.CBRoleChainBinaryDerivation

/-! # Fresh-signature regular CB countermodels with arbitrary role chains -/

namespace ContextCalculus.CBRegularArbitraryChainCountermodel

open ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau

abbrev SafeClause := CBRegularFreshCardinalityCountermodel.SafeClause

structure SafeSource (Concept Role Individual : Type) where
  clauses : List (SafeClause Concept Role Individual)
  chains : List (RoleChain Role)

def SafeSource.toSource (source : SafeSource Concept Role Individual) :
    SourceOntology Concept Role Individual where
  clauses := source.clauses.map
    CBRegularFreshCardinalityCountermodel.SafeClause.toOClause
  chains := source.chains

def mapRoleClause (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) :
    CBRegularRoleCountermodel.SafeClause SourceConcept SourceRole →
      CBRegularRoleCountermodel.SafeClause TargetConcept TargetRole
  | .gci body head => .gci (body.map conceptMap) (head.map conceptMap)
  | .exR source role filler =>
      .exR (conceptMap source) (roleMap role) (conceptMap filler)
  | .allR source role filler =>
      .allR (conceptMap source) (roleMap role) (conceptMap filler)
  | .exL role filler conclusion =>
      .exL (roleMap role) (conceptMap filler) (conceptMap conclusion)
  | .subR premise conclusion => .subR (roleMap premise) (roleMap conclusion)
  | .inv role inverse => .inv (roleMap role) (roleMap inverse)

def mapNominalClause (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) :
    CBRegularNominalCountermodel.SafeClause SourceConcept SourceRole Individual →
      CBRegularNominalCountermodel.SafeClause TargetConcept TargetRole Individual
  | .base clause => .base (mapRoleClause conceptMap roleMap clause)
  | .nominal nominal => .nominal {
      concept := conceptMap nominal.concept
      individual := nominal.individual }

def SafeClause.toTarget (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) (top : TargetConcept) :
    SafeClause SourceConcept SourceRole Individual →
      CBRegularCardinalityCountermodel.SafeClause
        TargetConcept TargetRole Individual
  | .core clause => .core (mapNominalClause conceptMap roleMap clause)
  | .func role => .func (roleMap role) top top
  | .atMost bound role filler =>
      .atMost bound (roleMap role) (conceptMap filler) top

def SafeSource.toTarget
    (source : SafeSource SourceConcept SourceRole Individual)
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) (top : TargetConcept)
    (binaryChains : List (CBRegularRoleCountermodel.BinaryChain TargetRole)) :
    CBRegularCardinalityCountermodel.SafeSource
      TargetConcept TargetRole Individual where
  clauses := source.clauses.map
    (SafeClause.toTarget conceptMap roleMap top)
  chains := binaryChains

theorem mapRoleClause_toOClause
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (clause : CBRegularRoleCountermodel.SafeClause SourceConcept SourceRole) :
    CBRegularRoleCountermodel.SafeClause.toOClause
        (Individual := Individual) (mapRoleClause conceptMap roleMap clause) =
      CBSourceSignatureRenaming.mapClause conceptMap roleMap
        (CBRegularRoleCountermodel.SafeClause.toOClause
          (Individual := Individual) clause) := by
  cases clause <;> rfl

theorem mapNominalClause_toOClause
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole)
    (clause : CBRegularNominalCountermodel.SafeClause
      SourceConcept SourceRole Individual) :
    (mapNominalClause conceptMap roleMap clause).toOClause =
      CBSourceSignatureRenaming.mapClause conceptMap roleMap clause.toOClause := by
  cases clause with
  | base clause =>
      exact mapRoleClause_toOClause (Individual := Individual)
        conceptMap roleMap clause
  | nominal nominal => rfl

theorem toTargetClause_toOClause
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) (top : TargetConcept)
    (clause : SafeClause SourceConcept SourceRole Individual) :
    (clause.toTarget conceptMap roleMap top).toOClause =
      CBSourceSignatureRenaming.mapClause conceptMap roleMap clause.toOClause := by
  cases clause with
  | core clause => exact mapNominalClause_toOClause conceptMap roleMap clause
  | func role => rfl
  | atMost bound role filler => rfl

theorem target_clauses_exact
    (source : SafeSource SourceConcept SourceRole Individual)
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) (top : TargetConcept)
    (binaryChains : List (CBRegularRoleCountermodel.BinaryChain TargetRole)) :
    (source.toTarget conceptMap roleMap top binaryChains).toSource.clauses =
      source.toSource.clauses.map
        (CBSourceSignatureRenaming.mapClause conceptMap roleMap) := by
  simp only [CBRegularCardinalityCountermodel.SafeSource.toSource,
    SafeSource.toTarget, SafeSource.toSource, List.map_map]
  induction source.clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.map_cons, Function.comp_apply,
        toTargetClause_toOClause, ih]

theorem models_source_of_target
    (source : SafeSource SourceConcept SourceRole Individual)
    (conceptMap : SourceConcept → TargetConcept)
    (roleMap : SourceRole → TargetRole) (top : TargetConcept)
    (binaryChains : List (CBRegularRoleCountermodel.BinaryChain TargetRole))
    (derivations : ∀ chain, chain ∈ source.chains →
      CBRoleChainBinaryDerivation.Derivation roleMap binaryChains
        chain.body (roleMap chain.sup))
    (target : Eqv.Interp D TargetConcept TargetRole Individual)
    (hmodels : CBRoleChainEncoding.models target
      (source.toTarget conceptMap roleMap top binaryChains).toSource) :
    CBRoleChainEncoding.models
      (CBSourceSignatureRenaming.pullback conceptMap roleMap target)
      source.toSource := by
  constructor
  · intro clause hclause
    simp only [SafeSource.toSource, List.mem_map] at hclause
    rcases hclause with ⟨safeClause, hsafeClause, rfl⟩
    apply (CBSourceSignatureRenaming.sat_mapClause_iff
      conceptMap roleMap target safeClause.toOClause).1
    apply hmodels.1
    rw [target_clauses_exact source conceptMap roleMap top binaryChains]
    exact List.mem_map.mpr ⟨safeClause.toOClause,
      List.mem_map.mpr ⟨safeClause, hsafeClause, rfl⟩, rfl⟩
  · intro chain hchain
    apply CBRoleChainBinaryDerivation.satChain_of_derivation roleMap binaryChains
      chain (derivations chain hchain) target.r
    intro binary hbinary
    exact hmodels.2 binary.toRoleChain (by
      simp only [CBRegularCardinalityCountermodel.SafeSource.toSource,
        SafeSource.toTarget, List.mem_map]
      exact ⟨binary, hbinary, rfl⟩)

/-- Pull a target model using fresh concepts, fresh roles, and checked binary
chain derivations back to the exact arbitrary-chain source signature. -/
theorem countermodel_of_target_countermodel
    (source : SafeSource (Fin sourceConceptCount) (Fin sourceRoleCount)
      (Fin individualCount))
    (conceptMap : Fin sourceConceptCount → Fin targetConceptCount)
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (top : Fin targetConceptCount)
    (binaryChains : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount)))
    (derivations : ∀ chain, chain ∈ source.chains →
      CBRoleChainBinaryDerivation.Derivation roleMap binaryChains
        chain.body (roleMap chain.sup))
    (sub sup : Fin sourceConceptCount)
    (D : Type) (targetModel : TModel D) (element : D)
    (htarget : ∀ clause ∈ CBRoleChainEncoding.encode
      (source.toTarget conceptMap roleMap top binaryChains).toSource,
      valid targetModel clause)
    (hsub : targetModel.conc (conceptMap sub).val element)
    (hsup : ¬targetModel.conc (conceptMap sup).val element) :
    ∃ model : TModel D,
      (∀ clause ∈ CBRoleChainEncoding.encode source.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let targetInterpretation := CBRoleChainEncoding.restrictModel
    (conceptCount := targetConceptCount) (roleCount := targetRoleCount)
    (individualCount := individualCount) targetModel
  have htargetModels : CBRoleChainEncoding.models targetInterpretation
      (source.toTarget conceptMap roleMap top binaryChains).toSource :=
    CBRoleChainEncoding.models_restrict _ targetModel htarget
  let sourceInterpretation :=
    CBSourceSignatureRenaming.pullback conceptMap roleMap targetInterpretation
  have hsource : CBRoleChainEncoding.models sourceInterpretation source.toSource :=
    models_source_of_target source conceptMap roleMap top binaryChains
      derivations targetInterpretation htargetModels
  let model := CBRoleChainEncoding.extendModel source.toSource sourceInterpretation
    hsource element
  refine ⟨model, CBRoleChainEncoding.models_extend source.toSource
    sourceInterpretation hsource element, ?_, ?_⟩
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      sourceInterpretation, CBSourceSignatureRenaming.pullback,
      targetInterpretation, CBRoleChainEncoding.restrictModel,
      CBEqEncoding.restrictModel] using hsub
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      sourceInterpretation, CBSourceSignatureRenaming.pullback,
      targetInterpretation, CBRoleChainEncoding.restrictModel,
      CBEqEncoding.restrictModel] using hsup

/-- An anchored regular certificate over enlarged concept and role signatures,
together with checked binary derivations for every arbitrary source chain,
produces a countermodel over the exact source signature. -/
theorem checked_arbitrary_chain_countermodel
    [NeZero eqNodeCount] [NeZero regularNodeCount]
    (certificate : AnchoredForestDomain.FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount targetConceptCount targetRoleCount variableCount)
    (sourceVar middle target : Fin variableCount)
    (hsourceTarget : sourceVar ≠ target)
    (hmiddleSource : middle ≠ sourceVar) (hmiddleTarget : middle ≠ target)
    (source : SafeSource (Fin sourceConceptCount) (Fin sourceRoleCount)
      (Fin individualCount))
    (conceptMap : Fin sourceConceptCount → Fin targetConceptCount)
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (top : Fin targetConceptCount)
    (binaryChains : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount)))
    (derivations : ∀ chain, chain ∈ source.chains →
      CBRoleChainBinaryDerivation.Derivation roleMap binaryChains
        chain.body (roleMap chain.sup))
    (individualRoot : Fin individualCount → Fin regularNodeCount)
    (sub sup : Fin sourceConceptCount)
    (hroleClauses : certificate.anchored.regular.roleClauses =
      CBRegularRoleCountermodel.roleClauses sourceVar middle target
        (source.toTarget conceptMap roleMap top binaryChains).core.base)
    (hresidual : certificate.anchored.regular.residual =
      CBRegularRoleCountermodel.residual sourceVar target
          (source.toTarget conceptMap roleMap top binaryChains).core.base.clauses ++
        (source.toTarget conceptMap roleMap top binaryChains).activationClauses
          sourceVar)
    (hdefinitions : certificate.definitions =
      (source.toTarget conceptMap roleMap top binaryChains).definitions)
    (hnominalRoots : ∀ nominal,
      CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
        (source.toTarget conceptMap roleMap top binaryChains).core.clauses →
      certificate.anchored.nominalRoot nominal.concept =
        some (individualRoot nominal.individual))
    (hsub : certificate.anchored.equality.base.state.label 0
      (.pos (conceptMap sub)))
    (hnotSup : certificate.anchored.equality.base.state.label 0
      (.negated (conceptMap sup)))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBRoleChainEncoding.encode source.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  rcases CBRegularCardinalityCountermodel.checked_regular_cardinality_countermodel
      certificate sourceVar middle target hsourceTarget hmiddleSource
      hmiddleTarget (source.toTarget conceptMap roleMap top binaryChains)
      individualRoot (conceptMap sub) (conceptMap sup) hroleClauses hresidual
      hdefinitions hnominalRoots hsub hnotSup hcheck with
    ⟨D, targetModel, element, htarget, htargetSub, htargetNotSup⟩
  rcases countermodel_of_target_countermodel source conceptMap roleMap top
      binaryChains derivations sub sup D targetModel element htarget htargetSub
      htargetNotSup with ⟨model, hsource, hsourceSub, hsourceNotSup⟩
  exact ⟨D, model, element, hsource, hsourceSub, hsourceNotSup⟩

#print axioms target_clauses_exact
#print axioms models_source_of_target
#print axioms countermodel_of_target_countermodel
#print axioms checked_arbitrary_chain_countermodel

end ContextCalculus.CBRegularArbitraryChainCountermodel
