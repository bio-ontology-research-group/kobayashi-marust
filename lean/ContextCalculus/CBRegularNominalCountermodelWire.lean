import ContextCalculus.CBRegularNominalCountermodel
import ContextCalculus.CBRegularRoleCountermodelWire
import ContextCalculus.HypertableauAnchoredEqualityWire

/-! # Exact wire evidence for nominal-aware regular CB countermodels -/

namespace ContextCalculus.CBRegularNominalCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.CBRegularRoleCountermodelWire
open ContextCalculus.Hypertableau
open ContextCalculus.Hypertableau.AnchoredForestDomain

structure WireNominalClause where
  concept : Nat
  individual : Nat
deriving FromJson, ToJson

inductive WireSafeClause where
  | base (clause : CBRegularRoleCountermodelWire.WireSafeClause)
  | nominal (clause : WireNominalClause)
deriving FromJson, ToJson

structure WireRegularNominalCountermodel where
  version : Nat
  clauses : List CBRegularNominalCountermodelWire.WireSafeClause
  chains : List WireBinaryChain
  individual_roots : List Nat
  anchored : WireAnchoredEqCertificate
deriving FromJson, ToJson

def WireNominalClause.decode (conceptCount individualCount : Nat)
    (wire : WireNominalClause) :
    Except String (CBRegularNominalCountermodel.NominalClause
      (Fin conceptCount) (Fin individualCount)) := do
  return {
    concept := ← checkedFin "regular-nominal concept" conceptCount wire.concept
    individual := ← checkedFin "regular-nominal individual" individualCount
      wire.individual }

def WireSafeClause.decode (conceptCount roleCount individualCount : Nat) :
    CBRegularNominalCountermodelWire.WireSafeClause → Except String
      (CBRegularNominalCountermodel.SafeClause
        (Fin conceptCount) (Fin roleCount) (Fin individualCount))
  | .base clause => do
      return .base (← CBRegularRoleCountermodelWire.WireSafeClause.decode
        conceptCount roleCount clause)
  | .nominal clause => do
      return .nominal (← clause.decode conceptCount individualCount)

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

def nominalRootsB
    [DecidableEq Node]
    (clauses : List (CBRegularNominalCountermodel.SafeClause Concept Role Individual))
    (nominalRoot : Concept → Option Node) (individualRoot : Individual → Node) : Bool :=
  clauses.all fun clause => match clause with
  | .base _ => true
  | .nominal nominal => decide
      (nominalRoot nominal.concept = some (individualRoot nominal.individual))

theorem nominalRootsB_sound
    [DecidableEq Node]
    (hcheck : nominalRootsB (Node := Node) clauses nominalRoot individualRoot = true) :
    ∀ nominal, CBRegularNominalCountermodel.SafeClause.nominal nominal ∈ clauses →
      nominalRoot nominal.concept = some (individualRoot nominal.individual) := by
  intro nominal hmem
  have h := List.all_eq_true.mp hcheck
    (CBRegularNominalCountermodel.SafeClause.nominal nominal) hmem
  simpa [nominalRootsB] using h

structure DecodedRegularNominalCountermodel
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat) where
  safe : CBRegularNominalCountermodel.SafeSource
    (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals)
  source_exact : CBRoleChainEncoding.encode safe.toSource = source
  anchored : DecodedAnchoredEqAt bounds.concepts bounds.roles 3
  eq_positive : 0 < anchored.eqNodeCount
  individualRoot : Fin bounds.individuals → Fin anchored.regularNodeCount
  role_clauses_exact : anchored.certificate.regular.roleClauses =
    CBRegularRoleCountermodel.roleClauses
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe.base
  residual_exact : anchored.certificate.regular.residual =
    CBRegularRoleCountermodel.residual
      (0 : Fin 3) (2 : Fin 3) safe.base.clauses
  nominal_roots_exact : ∀ nominal,
    CBRegularNominalCountermodel.SafeClause.nominal nominal ∈ safe.clauses →
    anchored.certificate.nominalRoot nominal.concept =
      some (individualRoot nominal.individual)
  sub : Fin bounds.concepts
  sup : Fin bounds.concepts
  sub_exact : sub.val = subRaw
  sup_exact : sup.val = supRaw
  root_sub : (⟨0, eq_positive⟩, .pos sub) ∈
    anchored.certificate.equality.base.labels
  root_not_sup : (⟨0, eq_positive⟩, .negated sup) ∈
    anchored.certificate.equality.base.labels
  accepted : anchored.certificate.check = true

def WireRegularNominalCountermodel.decode
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularNominalCountermodel) :
    Except String (DecodedRegularNominalCountermodel bounds source subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported regular-nominal CB countermodel version {wire.version}"
  let clauses ← wire.clauses.mapM
    (CBRegularNominalCountermodelWire.WireSafeClause.decode
      bounds.concepts bounds.roles bounds.individuals)
  let chains ← wire.chains.mapM (WireBinaryChain.decode bounds.roles)
  let safe : CBRegularNominalCountermodel.SafeSource
      (Fin bounds.concepts) (Fin bounds.roles)
      (Fin bounds.individuals) := { clauses, chains }
  if hsource : CBRoleChainEncoding.encode safe.toSource = source then
    let anchored ← wire.anchored.decodeAt bounds.concepts bounds.roles 3
    if heq : 0 < anchored.eqNodeCount then
      let individualRoot ← decodeClassMap bounds.individuals
        anchored.regularNodeCount wire.individual_roots
      if hroles : anchored.certificate.regular.roleClauses =
          CBRegularRoleCountermodel.roleClauses
            (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe.base then
        if hresidual : anchored.certificate.regular.residual =
            CBRegularRoleCountermodel.residual
              (0 : Fin 3) (2 : Fin 3) safe.base.clauses then
          if hnominals : nominalRootsB safe.clauses
              anchored.certificate.nominalRoot individualRoot = true then
            let sub ← checkedFinExact "regular-nominal subclass" bounds.concepts subRaw
            let sup ← checkedFinExact "regular-nominal superclass" bounds.concepts supRaw
            if hsub : (⟨0, heq⟩, .pos sub.val) ∈
                anchored.certificate.equality.base.labels then
              if hsup : (⟨0, heq⟩, .negated sup.val) ∈
                  anchored.certificate.equality.base.labels then
                if hcheck : anchored.certificate.check = true then
                  return {
                    safe, source_exact := hsource, anchored, eq_positive := heq,
                    individualRoot, role_clauses_exact := hroles,
                    residual_exact := hresidual,
                    nominal_roots_exact := nominalRootsB_sound hnominals,
                    sub := sub.val, sup := sup.val, sub_exact := sub.property,
                    sup_exact := sup.property, root_sub := hsub,
                    root_not_sup := hsup, accepted := hcheck }
                else throw "regular-nominal anchored certificate was rejected"
              else throw "regular-nominal countermodel omits the negative query literal"
            else throw "regular-nominal countermodel omits the positive query literal"
          else throw "regular-nominal individual roots differ from the nominal anchors"
        else throw "regular-nominal residual differs from the exact base translation"
      else throw "regular-nominal role clauses differ from the exact base RBox"
    else throw "regular-nominal equality state requires at least one node"
  else throw "regular-nominal encoding differs from the exact CB source ontology"

theorem DecodedRegularNominalCountermodel.refutes
    (decoded : DecodedRegularNominalCountermodel bounds source subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ source, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.anchored.eqNodeCount :=
    ⟨Nat.ne_of_gt decoded.eq_positive⟩
  letI : NeZero decoded.anchored.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.anchored.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    CBRegularNominalCountermodel.checked_regular_nominal_countermodel
      decoded.anchored.certificate
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      decoded.safe decoded.individualRoot decoded.sub decoded.sup
      decoded.role_clauses_exact decoded.residual_exact decoded.nominal_roots_exact
      (by simpa [FiniteEqCertificate.state] using decoded.root_sub)
      (by simpa [FiniteEqCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, decoded.sub_exact ▸ hsub,
    decoded.sup_exact ▸ hsup⟩
  simpa [decoded.source_exact] using hsource

#print axioms DecodedRegularNominalCountermodel.refutes

end ContextCalculus.CBRegularNominalCountermodelWire
