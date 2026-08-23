import ContextCalculus.CBRegularCardinalityCountermodel
import ContextCalculus.CBRegularNominalCountermodelWire
import ContextCalculus.HypertableauAnchoredCardinalityWire

/-! # Exact wire evidence for cardinality-aware regular CB countermodels -/

namespace ContextCalculus.CBRegularCardinalityCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau
open ContextCalculus.Hypertableau.AnchoredForestDomain

inductive WireSafeClause where
  | core (clause : CBRegularNominalCountermodelWire.WireSafeClause)
  | func (role marker filler : Nat)
  | atMost (bound role filler marker : Nat)
deriving FromJson, ToJson

structure WireRegularCardinalityCountermodel where
  version : Nat
  clauses : List WireSafeClause
  chains : List CBRegularRoleCountermodelWire.WireBinaryChain
  individual_roots : List Nat
  anchored : WireAnchoredCardinalityEqCertificate
deriving FromJson, ToJson

def WireSafeClause.decode (conceptCount roleCount individualCount : Nat) :
    WireSafeClause → Except String
      (CBRegularCardinalityCountermodel.SafeClause
        (Fin conceptCount) (Fin roleCount) (Fin individualCount))
  | .core clause => do
      return .core (← CBRegularNominalCountermodelWire.WireSafeClause.decode
        conceptCount roleCount individualCount clause)
  | .func role marker filler => do
      return .func
        (← checkedFin "regular-cardinality functional role" roleCount role)
        (← checkedFin "regular-cardinality functional marker" conceptCount marker)
        (← checkedFin "regular-cardinality functional filler" conceptCount filler)
  | .atMost bound role filler marker => do
      return .atMost bound
        (← checkedFin "regular-cardinality maximum role" roleCount role)
        (← checkedFin "regular-cardinality maximum filler" conceptCount filler)
        (← checkedFin "regular-cardinality maximum marker" conceptCount marker)

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

structure DecodedRegularCardinalityCountermodel
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat) where
  safe : CBRegularCardinalityCountermodel.SafeSource
    (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals)
  source_exact : CBRoleChainEncoding.encode safe.toSource = source
  anchored : DecodedAnchoredCardinalityEqCertificateAt bounds.concepts bounds.roles 3
  eq_positive : 0 < anchored.eqNodeCount
  individualRoot : Fin bounds.individuals → Fin anchored.regularNodeCount
  role_clauses_exact : anchored.certificate.anchored.regular.roleClauses =
    CBRegularRoleCountermodel.roleClauses
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe.core.base
  residual_exact : anchored.certificate.anchored.regular.residual =
    CBRegularRoleCountermodel.residual
      (0 : Fin 3) (2 : Fin 3) safe.core.base.clauses ++
      safe.activationClauses (0 : Fin 3)
  definitions_exact : anchored.certificate.definitions = safe.definitions
  nominal_roots_exact : ∀ nominal,
    CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
      safe.core.clauses →
    anchored.certificate.anchored.nominalRoot nominal.concept =
      some (individualRoot nominal.individual)
  sub : Fin bounds.concepts
  sup : Fin bounds.concepts
  sub_exact : sub.val = subRaw
  sup_exact : sup.val = supRaw
  root_sub : (⟨0, eq_positive⟩, .pos sub) ∈
    anchored.certificate.anchored.equality.base.labels
  root_not_sup : (⟨0, eq_positive⟩, .negated sup) ∈
    anchored.certificate.anchored.equality.base.labels
  accepted : anchored.certificate.check = true

def WireRegularCardinalityCountermodel.decode
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularCardinalityCountermodel) : Except String
      (DecodedRegularCardinalityCountermodel bounds source subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported regular-cardinality CB countermodel version {wire.version}"
  let clauses ← wire.clauses.mapM
    (WireSafeClause.decode bounds.concepts bounds.roles bounds.individuals)
  let chains ← wire.chains.mapM
    (CBRegularRoleCountermodelWire.WireBinaryChain.decode bounds.roles)
  let safe : CBRegularCardinalityCountermodel.SafeSource
      (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals) :=
    { clauses, chains }
  if hsource : CBRoleChainEncoding.encode safe.toSource = source then
    let anchored ← wire.anchored.decodeAt bounds.concepts bounds.roles 3
    if heq : 0 < anchored.eqNodeCount then
      let individualRoot ← decodeClassMap bounds.individuals
        anchored.regularNodeCount wire.individual_roots
      if hroles : anchored.certificate.anchored.regular.roleClauses =
          CBRegularRoleCountermodel.roleClauses
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe.core.base then
        if hresidual : anchored.certificate.anchored.regular.residual =
            CBRegularRoleCountermodel.residual
              (0 : Fin 3) (2 : Fin 3) safe.core.base.clauses ++
              safe.activationClauses (0 : Fin 3) then
          if hdefinitions : anchored.certificate.definitions = safe.definitions then
            if hnominals : CBRegularNominalCountermodelWire.nominalRootsB
                safe.core.clauses anchored.certificate.anchored.nominalRoot
                  individualRoot = true then
              let sub ← checkedFinExact "regular-cardinality subclass"
                bounds.concepts subRaw
              let sup ← checkedFinExact "regular-cardinality superclass"
                bounds.concepts supRaw
              if hsub : (⟨0, heq⟩, .pos sub.val) ∈
                  anchored.certificate.anchored.equality.base.labels then
                if hsup : (⟨0, heq⟩, .negated sup.val) ∈
                    anchored.certificate.anchored.equality.base.labels then
                  if hcheck : anchored.certificate.check = true then
                    return {
                      safe, source_exact := hsource, anchored, eq_positive := heq,
                      individualRoot, role_clauses_exact := hroles,
                      residual_exact := hresidual, definitions_exact := hdefinitions,
                      nominal_roots_exact :=
                        CBRegularNominalCountermodelWire.nominalRootsB_sound hnominals,
                      sub := sub.val, sup := sup.val,
                      sub_exact := sub.property, sup_exact := sup.property,
                      root_sub := hsub, root_not_sup := hsup, accepted := hcheck }
                  else throw "regular-cardinality anchored certificate was rejected"
                else throw "regular-cardinality countermodel omits the negative query literal"
              else throw "regular-cardinality countermodel omits the positive query literal"
            else throw "regular-cardinality individual roots differ from nominal anchors"
          else throw "regular-cardinality definitions differ from the exact source projection"
        else throw "regular-cardinality residual differs from the exact source projection"
      else throw "regular-cardinality role clauses differ from the exact source RBox"
    else throw "regular-cardinality equality state requires at least one node"
  else throw "regular-cardinality encoding differs from the exact CB source ontology"

theorem DecodedRegularCardinalityCountermodel.refutes
    (decoded : DecodedRegularCardinalityCountermodel bounds source subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ source, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.anchored.eqNodeCount :=
    ⟨Nat.ne_of_gt decoded.eq_positive⟩
  letI : NeZero decoded.anchored.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.anchored.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    CBRegularCardinalityCountermodel.checked_regular_cardinality_countermodel
      decoded.anchored.certificate (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (by decide) (by decide) (by decide) decoded.safe decoded.individualRoot
      decoded.sub decoded.sup decoded.role_clauses_exact decoded.residual_exact
      decoded.definitions_exact decoded.nominal_roots_exact
      (by simpa [FiniteEqCertificate.state] using decoded.root_sub)
      (by simpa [FiniteEqCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, decoded.sub_exact ▸ hsub,
    decoded.sup_exact ▸ hsup⟩
  simpa [decoded.source_exact] using hsource

#print axioms DecodedRegularCardinalityCountermodel.refutes

end ContextCalculus.CBRegularCardinalityCountermodelWire
