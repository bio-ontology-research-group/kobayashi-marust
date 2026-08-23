import ContextCalculus.CBRegularCardinalityCountermodel
import ContextCalculus.CBSourceConceptRenaming

/-!
# Fresh-signature cardinality-aware regular CB countermodels

The same-signature cardinality bridge is sound but cannot always select a
source concept that denotes top. This module embeds source concepts into a
larger target signature and reserves a target-only concept as the universal
marker and functionality filler. The resulting target model is pulled back
through the exact source-concept renaming before CB functions are installed.
-/

namespace ContextCalculus.CBRegularFreshCardinalityCountermodel

open ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau

inductive SafeClause (Concept Role Individual : Type) where
  | core (clause : CBRegularNominalCountermodel.SafeClause Concept Role Individual)
  | func (role : Role)
  | atMost (bound : Nat) (role : Role) (filler : Concept)
deriving DecidableEq, Repr

def SafeClause.toOClause : SafeClause Concept Role Individual →
    OClause Concept Role Individual
  | .core clause => clause.toOClause
  | .func role => .func role
  | .atMost bound role filler => .atMost bound role filler

structure SafeSource (Concept Role Individual : Type) where
  clauses : List (SafeClause Concept Role Individual)
  chains : List (CBRegularRoleCountermodel.BinaryChain Role)

def SafeSource.toSource (source : SafeSource Concept Role Individual) :
    SourceOntology Concept Role Individual where
  clauses := source.clauses.map SafeClause.toOClause
  chains := source.chains.map CBRegularRoleCountermodel.BinaryChain.toRoleChain

def mapRoleClause (f : SourceConcept → TargetConcept) :
    CBRegularRoleCountermodel.SafeClause SourceConcept Role →
      CBRegularRoleCountermodel.SafeClause TargetConcept Role
  | .gci body head => .gci (body.map f) (head.map f)
  | .exR source role filler => .exR (f source) role (f filler)
  | .allR source role filler => .allR (f source) role (f filler)
  | .exL role filler conclusion => .exL role (f filler) (f conclusion)
  | .subR premise conclusion => .subR premise conclusion
  | .inv role inverse => .inv role inverse

def mapNominalClause (f : SourceConcept → TargetConcept) :
    CBRegularNominalCountermodel.SafeClause SourceConcept Role Individual →
      CBRegularNominalCountermodel.SafeClause TargetConcept Role Individual
  | .base clause => .base (mapRoleClause f clause)
  | .nominal nominal => .nominal {
      concept := f nominal.concept, individual := nominal.individual }

def SafeClause.toTarget (f : SourceConcept → TargetConcept) (top : TargetConcept) :
    SafeClause SourceConcept Role Individual →
      CBRegularCardinalityCountermodel.SafeClause TargetConcept Role Individual
  | .core clause => .core (mapNominalClause f clause)
  | .func role => .func role top top
  | .atMost bound role filler => .atMost bound role (f filler) top

def SafeSource.toTarget (source : SafeSource SourceConcept Role Individual)
    (f : SourceConcept → TargetConcept) (top : TargetConcept) :
    CBRegularCardinalityCountermodel.SafeSource TargetConcept Role Individual where
  clauses := source.clauses.map (SafeClause.toTarget f top)
  chains := source.chains

theorem mapRoleClause_toOClause
    (f : SourceConcept → TargetConcept)
    (clause : CBRegularRoleCountermodel.SafeClause SourceConcept Role) :
    (CBRegularRoleCountermodel.SafeClause.toOClause
        (Individual := Individual) (mapRoleClause f clause)) =
      CBSourceConceptRenaming.mapClause f
        (CBRegularRoleCountermodel.SafeClause.toOClause
          (Individual := Individual) clause) := by
  cases clause <;> rfl

theorem mapNominalClause_toOClause
    (f : SourceConcept → TargetConcept)
    (clause : CBRegularNominalCountermodel.SafeClause SourceConcept Role Individual) :
    (mapNominalClause f clause).toOClause =
      CBSourceConceptRenaming.mapClause f clause.toOClause := by
  cases clause with
  | base clause => exact mapRoleClause_toOClause (Individual := Individual) f clause
  | nominal nominal => rfl

theorem toTargetClause_toOClause
    (f : SourceConcept → TargetConcept) (top : TargetConcept)
    (clause : SafeClause SourceConcept Role Individual) :
    (clause.toTarget f top).toOClause =
      CBSourceConceptRenaming.mapClause f clause.toOClause := by
  cases clause with
  | core clause => exact mapNominalClause_toOClause f clause
  | func role => rfl
  | atMost bound role filler => rfl

theorem toTarget_toSource
    (source : SafeSource SourceConcept Role Individual)
    (f : SourceConcept → TargetConcept) (top : TargetConcept) :
    (source.toTarget f top).toSource =
      CBSourceConceptRenaming.mapSource f source.toSource := by
  cases source with
  | mk clauses chains =>
      simp only [CBRegularCardinalityCountermodel.SafeSource.toSource,
        SafeSource.toTarget, SafeSource.toSource, CBSourceConceptRenaming.mapSource,
        List.map_map]
      congr 1
      induction clauses with
      | nil => rfl
      | cons clause clauses ih =>
          simp only [List.map_cons, Function.comp_apply,
            toTargetClause_toOClause, ih]

/-- Pull a checked target-signature countermodel back to the exact source
signature. The target-only top concept disappears at this boundary. -/
theorem countermodel_of_target_countermodel
    (source : SafeSource (Fin sourceConceptCount) (Fin roleCount)
      (Fin individualCount))
    (f : Fin sourceConceptCount → Fin targetConceptCount)
    (top : Fin targetConceptCount)
    (sub sup : Fin sourceConceptCount)
    (D : Type) (targetModel : TModel D) (element : D)
    (htarget : ∀ clause ∈
      CBRoleChainEncoding.encode (source.toTarget f top).toSource,
      valid targetModel clause)
    (hsub : targetModel.conc (f sub).val element)
    (hsup : ¬targetModel.conc (f sup).val element) :
    ∃ model : TModel D,
      (∀ clause ∈ CBRoleChainEncoding.encode source.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  let targetInterpretation := CBRoleChainEncoding.restrictModel
    (conceptCount := targetConceptCount) (roleCount := roleCount)
    (individualCount := individualCount) targetModel
  have htargetSource : CBRoleChainEncoding.models targetInterpretation
      (source.toTarget f top).toSource :=
    CBRoleChainEncoding.models_restrict (source.toTarget f top).toSource
      targetModel htarget
  have hmapped : CBRoleChainEncoding.models targetInterpretation
      (CBSourceConceptRenaming.mapSource f source.toSource) := by
    simpa [toTarget_toSource source f top] using htargetSource
  let sourceInterpretation := CBSourceConceptRenaming.pullback f targetInterpretation
  have hsource : CBRoleChainEncoding.models sourceInterpretation source.toSource :=
    (CBSourceConceptRenaming.models_mapSource_iff f targetInterpretation
      source.toSource).1 hmapped
  let model := CBRoleChainEncoding.extendModel source.toSource sourceInterpretation
    hsource element
  refine ⟨model,
    CBRoleChainEncoding.models_extend source.toSource sourceInterpretation
      hsource element, ?_, ?_⟩
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      sourceInterpretation, CBSourceConceptRenaming.pullback,
      targetInterpretation, CBRoleChainEncoding.restrictModel,
      CBEqEncoding.restrictModel] using hsub
  · simpa [model, CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      sourceInterpretation, CBSourceConceptRenaming.pullback,
      targetInterpretation, CBRoleChainEncoding.restrictModel,
      CBEqEncoding.restrictModel] using hsup

/-- A checked regular cardinality certificate over a larger concept signature
produces a countermodel over the exact source signature. The certificate may
therefore reserve concepts which are absent from the source ontology. -/
theorem checked_fresh_cardinality_countermodel
    [NeZero eqNodeCount] [NeZero regularNodeCount]
    (certificate : AnchoredForestDomain.FiniteAnchoredCardinalityEqCertificate
      eqNodeCount regularNodeCount targetConceptCount roleCount variableCount)
    (sourceVar middle target : Fin variableCount)
    (hsourceTarget : sourceVar ≠ target)
    (hmiddleSource : middle ≠ sourceVar) (hmiddleTarget : middle ≠ target)
    (source : SafeSource (Fin sourceConceptCount) (Fin roleCount)
      (Fin individualCount))
    (f : Fin sourceConceptCount → Fin targetConceptCount)
    (top : Fin targetConceptCount)
    (individualRoot : Fin individualCount → Fin regularNodeCount)
    (sub sup : Fin sourceConceptCount)
    (hroleClauses : certificate.anchored.regular.roleClauses =
      CBRegularRoleCountermodel.roleClauses sourceVar middle target
        (source.toTarget f top).core.base)
    (hresidual : certificate.anchored.regular.residual =
      CBRegularRoleCountermodel.residual sourceVar target
          (source.toTarget f top).core.base.clauses ++
        (source.toTarget f top).activationClauses sourceVar)
    (hdefinitions : certificate.definitions =
      (source.toTarget f top).definitions)
    (hnominalRoots : ∀ nominal,
      CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
        (source.toTarget f top).core.clauses →
      certificate.anchored.nominalRoot nominal.concept =
        some (individualRoot nominal.individual))
    (hsub : certificate.anchored.equality.base.state.label 0 (.pos (f sub)))
    (hnotSup : certificate.anchored.equality.base.state.label 0 (.negated (f sup)))
    (hcheck : certificate.check = true) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ CBRoleChainEncoding.encode source.toSource,
        valid model clause) ∧
      model.conc sub.val element ∧ ¬model.conc sup.val element := by
  rcases CBRegularCardinalityCountermodel.checked_regular_cardinality_countermodel
      certificate sourceVar middle target hsourceTarget hmiddleSource
      hmiddleTarget (source.toTarget f top) individualRoot (f sub) (f sup)
      hroleClauses hresidual hdefinitions hnominalRoots hsub hnotSup hcheck with
    ⟨D, targetModel, element, htarget, htargetSub, htargetNotSup⟩
  rcases countermodel_of_target_countermodel source f top sub sup D targetModel
      element htarget htargetSub htargetNotSup with
    ⟨model, hsource, hsourceSub, hsourceNotSup⟩
  exact ⟨D, model, element, hsource, hsourceSub, hsourceNotSup⟩

#print axioms toTarget_toSource
#print axioms countermodel_of_target_countermodel
#print axioms checked_fresh_cardinality_countermodel

end ContextCalculus.CBRegularFreshCardinalityCountermodel
