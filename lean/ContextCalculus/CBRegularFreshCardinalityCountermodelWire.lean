import ContextCalculus.CBRegularFreshCardinalityCountermodel
import ContextCalculus.CBRegularNominalCountermodelWire
import ContextCalculus.HypertableauAnchoredCardinalityWire

/-! # Exact wire evidence for fresh-signature regular CB countermodels -/

namespace ContextCalculus.CBRegularFreshCardinalityCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau
open ContextCalculus.Hypertableau.AnchoredForestDomain

inductive WireSafeClause where
  | core (clause : CBRegularNominalCountermodelWire.WireSafeClause)
  | func (role : Nat)
  | atMost (bound role filler : Nat)
  | guardedAtMost (marker bound role filler : Nat)
  | atLeast (marker bound role filler : Nat)
deriving FromJson, ToJson

structure WireRegularFreshCardinalityCountermodel where
  version : Nat
  clauses : List WireSafeClause
  chains : List CBRegularRoleCountermodelWire.WireBinaryChain
  individual_roots : List Nat
  anchored : WireAnchoredCardinalityEqCertificate
deriving FromJson, ToJson

def WireSafeClause.decode (conceptCount roleCount individualCount : Nat) :
    WireSafeClause → Except String
      (CBRegularFreshCardinalityCountermodel.SafeClause
        (Fin conceptCount) (Fin roleCount) (Fin individualCount))
  | .core clause => do
      return .core (← CBRegularNominalCountermodelWire.WireSafeClause.decode
        conceptCount roleCount individualCount clause)
  | .func role => do
      return .func (← checkedFin "fresh-cardinality functional role" roleCount role)
  | .atMost bound role filler => do
      return .atMost bound
        (← checkedFin "fresh-cardinality maximum role" roleCount role)
        (← checkedFin "fresh-cardinality maximum filler" conceptCount filler)
  | .guardedAtMost marker bound role filler => do
      return .guardedAtMost
        (← checkedFin "fresh-cardinality guarded maximum marker" conceptCount marker)
        bound
        (← checkedFin "fresh-cardinality guarded maximum role" roleCount role)
        (← checkedFin "fresh-cardinality guarded maximum filler" conceptCount filler)
  | .atLeast marker bound role filler => do
      return .atLeast
        (← checkedFin "fresh-cardinality minimum marker" conceptCount marker)
        bound
        (← checkedFin "fresh-cardinality minimum role" roleCount role)
        (← checkedFin "fresh-cardinality minimum filler" conceptCount filler)

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

structure DecodedRegularFreshCardinalityCountermodel
    (bounds : Bounds) (productionSource : List FCL) (subRaw supRaw : Nat) where
  source : CBRegularFreshCardinalityCountermodel.SafeSource
    (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals)
  source_exact : CBRoleChainEncoding.encode source.toSource = productionSource
  anchored : DecodedAnchoredCardinalityEqCertificateAt
    (bounds.concepts + 1) bounds.roles 3
  eq_positive : 0 < anchored.eqNodeCount
  individualRoot : Fin bounds.individuals → Fin anchored.regularNodeCount
  role_clauses_exact : anchored.certificate.anchored.regular.roleClauses =
    CBRegularRoleCountermodel.roleClauses (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (source.toTarget Fin.succ (0 : Fin (bounds.concepts + 1))).core.base
  residual_exact : anchored.certificate.anchored.regular.residual =
    CBRegularRoleCountermodel.residual (0 : Fin 3) (2 : Fin 3)
        (source.toTarget Fin.succ (0 : Fin (bounds.concepts + 1))).core.base.clauses ++
      (source.toTarget Fin.succ
        (0 : Fin (bounds.concepts + 1))).activationClauses (0 : Fin 3)
  definitions_exact : anchored.certificate.definitions =
    (source.toTarget Fin.succ (0 : Fin (bounds.concepts + 1))).definitions
  nominal_roots_exact : ∀ nominal,
    CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
      (source.toTarget Fin.succ
        (0 : Fin (bounds.concepts + 1))).core.clauses →
    anchored.certificate.anchored.nominalRoot nominal.concept =
      some (individualRoot nominal.individual)
  sub : Fin bounds.concepts
  sup : Fin bounds.concepts
  sub_exact : sub.val = subRaw
  sup_exact : sup.val = supRaw
  root_sub : (⟨0, eq_positive⟩, .pos (Fin.succ sub)) ∈
    anchored.certificate.anchored.equality.base.labels
  root_not_sup : (⟨0, eq_positive⟩, .negated (Fin.succ sup)) ∈
    anchored.certificate.anchored.equality.base.labels
  accepted : anchored.certificate.check = true

def WireRegularFreshCardinalityCountermodel.decode
    (bounds : Bounds) (productionSource : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularFreshCardinalityCountermodel) : Except String
      (DecodedRegularFreshCardinalityCountermodel bounds productionSource
        subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported fresh-cardinality CB countermodel version {wire.version}"
  let clauses ← wire.clauses.mapM
    (WireSafeClause.decode bounds.concepts bounds.roles bounds.individuals)
  let chains ← wire.chains.mapM
    (CBRegularRoleCountermodelWire.WireBinaryChain.decode bounds.roles)
  let source : CBRegularFreshCardinalityCountermodel.SafeSource
      (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals) :=
    { clauses, chains }
  if hsource : CBRoleChainEncoding.encode source.toSource = productionSource then
    let anchored ← wire.anchored.decodeAt (bounds.concepts + 1) bounds.roles 3
    if heq : 0 < anchored.eqNodeCount then
      let individualRoot ← decodeClassMap bounds.individuals
        anchored.regularNodeCount wire.individual_roots
      let targetSafe := source.toTarget Fin.succ
        (0 : Fin (bounds.concepts + 1))
      if hroles : anchored.certificate.anchored.regular.roleClauses =
          CBRegularRoleCountermodel.roleClauses
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) targetSafe.core.base then
        if hresidual : anchored.certificate.anchored.regular.residual =
            CBRegularRoleCountermodel.residual
                (0 : Fin 3) (2 : Fin 3) targetSafe.core.base.clauses ++
              targetSafe.activationClauses (0 : Fin 3) then
          if hdefinitions : anchored.certificate.definitions =
              targetSafe.definitions then
            if hnominals : CBRegularNominalCountermodelWire.nominalRootsB
                targetSafe.core.clauses
                anchored.certificate.anchored.nominalRoot individualRoot = true then
              let sub ← checkedFinExact "fresh-cardinality subclass"
                bounds.concepts subRaw
              let sup ← checkedFinExact "fresh-cardinality superclass"
                bounds.concepts supRaw
              if hsub : (⟨0, heq⟩, .pos (Fin.succ sub.val)) ∈
                  anchored.certificate.anchored.equality.base.labels then
                if hsup : (⟨0, heq⟩, .negated (Fin.succ sup.val)) ∈
                    anchored.certificate.anchored.equality.base.labels then
                  if hcheck : anchored.certificate.check = true then
                    return {
                      source, source_exact := hsource, anchored,
                      eq_positive := heq, individualRoot,
                      role_clauses_exact := hroles,
                      residual_exact := hresidual,
                      definitions_exact := hdefinitions,
                      nominal_roots_exact :=
                        CBRegularNominalCountermodelWire.nominalRootsB_sound hnominals,
                      sub := sub.val, sup := sup.val,
                      sub_exact := sub.property, sup_exact := sup.property,
                      root_sub := hsub, root_not_sup := hsup, accepted := hcheck }
                  else throw "fresh-cardinality anchored certificate was rejected"
                else throw "fresh-cardinality countermodel omits the negative query literal"
              else throw "fresh-cardinality countermodel omits the positive query literal"
            else throw "fresh-cardinality individual roots differ from nominal anchors"
          else throw "fresh-cardinality definitions differ from the exact target projection"
        else throw "fresh-cardinality residual differs from the exact target projection"
      else throw "fresh-cardinality role clauses differ from the exact target RBox"
    else throw "fresh-cardinality equality state requires at least one node"
  else throw "fresh-cardinality encoding differs from the exact CB source ontology"

theorem DecodedRegularFreshCardinalityCountermodel.refutes
    (decoded : DecodedRegularFreshCardinalityCountermodel
      bounds productionSource subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ productionSource, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.anchored.eqNodeCount :=
    ⟨Nat.ne_of_gt decoded.eq_positive⟩
  letI : NeZero decoded.anchored.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.anchored.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    CBRegularFreshCardinalityCountermodel.checked_fresh_cardinality_countermodel
      decoded.anchored.certificate (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (by decide) (by decide) (by decide) decoded.source Fin.succ
      (0 : Fin (bounds.concepts + 1)) decoded.individualRoot decoded.sub decoded.sup
      decoded.role_clauses_exact decoded.residual_exact decoded.definitions_exact
      decoded.nominal_roots_exact
      (by simpa [FiniteEqCertificate.state] using decoded.root_sub)
      (by simpa [FiniteEqCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, decoded.sub_exact ▸ hsub,
    decoded.sup_exact ▸ hsup⟩
  simpa [decoded.source_exact] using hsource

#print axioms DecodedRegularFreshCardinalityCountermodel.refutes

end ContextCalculus.CBRegularFreshCardinalityCountermodelWire
