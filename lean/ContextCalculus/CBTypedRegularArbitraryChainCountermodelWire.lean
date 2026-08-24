import ContextCalculus.CBSourceWire
import ContextCalculus.CBRegularArbitraryChainCountermodelWire

/-!
# Typed-source regular CB countermodels

The regular countermodel uses canonical Skolem ids, while the production
ontology may use any checked injective allocation.  This wrapper checks the
regular certificate against the canonical typed encoding and then transports
the resulting model through the source binding's proved allocation.
-/

namespace ContextCalculus.CBTypedRegularArbitraryChainCountermodelWire

open ContextCalculus ContextCalculus.CheckerTerm ContextCalculus.Eqv
open ContextCalculus.CBSourceWire ContextCalculus.CBRoleChainEncoding
open ContextCalculus.CBRegularArbitraryChainCountermodelWire

abbrev WireTypedRegularArbitraryChainCountermodel :=
  WireRegularArbitraryChainCountermodel

structure DecodedTypedRegularArbitraryChainCountermodel
    (source : DecodedSourceBinding) (subRaw supRaw : Nat) where
  regular : DecodedRegularArbitraryChainCountermodel source.bounds
    (CBRoleChainEncoding.encode source.source) subRaw supRaw

def WireRegularArbitraryChainCountermodel.decodeTyped
    (source : DecodedSourceBinding) (subRaw supRaw : Nat)
    (wire : WireRegularArbitraryChainCountermodel) : Except String
      (DecodedTypedRegularArbitraryChainCountermodel source subRaw supRaw) := do
  let regular ← wire.decode source.bounds
    (CBRoleChainEncoding.encode source.source) subRaw supRaw
  return { regular }

theorem DecodedTypedRegularArbitraryChainCountermodel.refutesProduction
    (decoded : DecodedTypedRegularArbitraryChainCountermodel source subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ source.ontology, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  obtain ⟨D, canonical, element, hcanonical, hsub, hsup⟩ :=
    decoded.regular.refutes
  let interpretation := CBRoleChainEncoding.restrictModel
    (conceptCount := source.bounds.concepts)
    (roleCount := source.bounds.roles)
    (individualCount := source.bounds.individuals) canonical
  have hsource : CBRoleChainEncoding.models interpretation source.source :=
    CBRoleChainEncoding.models_restrict source.source canonical hcanonical
  let production := source.productionModel interpretation hsource element
  have hsubBound : subRaw < source.bounds.concepts := by
    rw [← decoded.regular.sub_exact]
    exact decoded.regular.sub.isLt
  have hsupBound : supRaw < source.bounds.concepts := by
    rw [← decoded.regular.sup_exact]
    exact decoded.regular.sup.isLt
  refine ⟨D, production, element,
    source.models_production interpretation hsource element, ?_, ?_⟩
  · simpa [production, DecodedSourceBinding.productionModel,
      CBFunctionRenaming.pushforwardModel, interpretation,
      CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      CBRoleChainEncoding.restrictModel, CBEqEncoding.restrictModel,
      hsubBound] using hsub
  · simpa [production, DecodedSourceBinding.productionModel,
      CBFunctionRenaming.pushforwardModel, interpretation,
      CBRoleChainEncoding.extendModel, CBEqEncoding.extendModel,
      CBRoleChainEncoding.restrictModel, CBEqEncoding.restrictModel,
      hsupBound] using hsup

#print axioms DecodedTypedRegularArbitraryChainCountermodel.refutesProduction

end ContextCalculus.CBTypedRegularArbitraryChainCountermodelWire
