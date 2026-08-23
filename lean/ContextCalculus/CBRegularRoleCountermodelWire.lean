import ContextCalculus.CBRegularRoleCountermodel
import ContextCalculus.CBTermDerivationWire
import ContextCalculus.HypertableauRegularWire

/-! Bounds-checked wire for equality-free ALC plus RBox CB countermodels. -/

namespace ContextCalculus.CBRegularRoleCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBRegularRoleCountermodel
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.CBTermWire
open ContextCalculus.Hypertableau

inductive WireSafeClause where
  | gci (body head : List Nat)
  | exR (source role filler : Nat)
  | allR (source role filler : Nat)
  | exL (role filler conclusion : Nat)
  | subR (premise conclusion : Nat)
  | inv (role inverse : Nat)
deriving FromJson, ToJson

structure WireBinaryChain where
  first : Nat
  second : Nat
  conclusion : Nat
deriving FromJson, ToJson

structure WireRegularRoleCountermodel where
  version : Nat
  clauses : List WireSafeClause
  chains : List WireBinaryChain
  regular : WireRegularCertificate
deriving FromJson, ToJson

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

def WireSafeClause.decode (conceptCount roleCount : Nat) : WireSafeClause →
    Except String (SafeClause (Fin conceptCount) (Fin roleCount))
  | .gci body head => do
      return .gci
        (← body.mapM (checkedFin "regular-role body concept" conceptCount))
        (← head.mapM (checkedFin "regular-role head concept" conceptCount))
  | .exR source role filler => do
      return .exR
        (← checkedFin "regular-role existential source" conceptCount source)
        (← checkedFin "regular-role existential role" roleCount role)
        (← checkedFin "regular-role existential filler" conceptCount filler)
  | .allR source role filler => do
      return .allR
        (← checkedFin "regular-role universal source" conceptCount source)
        (← checkedFin "regular-role universal role" roleCount role)
        (← checkedFin "regular-role universal filler" conceptCount filler)
  | .exL role filler conclusion => do
      return .exL
        (← checkedFin "regular-role existential-left role" roleCount role)
        (← checkedFin "regular-role existential-left filler" conceptCount filler)
        (← checkedFin "regular-role existential-left conclusion" conceptCount conclusion)
  | .subR premise conclusion => do
      return .subR
        (← checkedFin "regular-role subrole premise" roleCount premise)
        (← checkedFin "regular-role subrole conclusion" roleCount conclusion)
  | .inv role inverse => do
      return .inv
        (← checkedFin "regular-role inverse premise" roleCount role)
        (← checkedFin "regular-role inverse conclusion" roleCount inverse)

def WireBinaryChain.decode (roleCount : Nat) (wire : WireBinaryChain) :
    Except String (BinaryChain (Fin roleCount)) := do
  return {
    first := ← checkedFin "regular binary-chain first role" roleCount wire.first
    second := ← checkedFin "regular binary-chain second role" roleCount wire.second
    conclusion := ← checkedFin "regular binary-chain conclusion" roleCount wire.conclusion }

structure DecodedRegularRoleCountermodel
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat) where
  safe : SafeSource (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals)
  source_exact : CBRoleChainEncoding.encode safe.toSource = source
  regular : DecodedRegularCertificateAt bounds.concepts bounds.roles 3
  role_clauses_exact : regular.certificate.roleClauses =
    roleClauses (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe
  residual_exact : regular.certificate.residual =
    residual (0 : Fin 3) (2 : Fin 3) safe.clauses
  sub : Fin bounds.concepts
  sup : Fin bounds.concepts
  sub_exact : sub.val = subRaw
  sup_exact : sup.val = supRaw
  root_sub : (⟨0, regular.positive⟩, .pos sub) ∈ regular.certificate.labels
  root_not_sup : (⟨0, regular.positive⟩, .negated sup) ∈ regular.certificate.labels
  accepted : regular.certificate.check = true

def WireRegularRoleCountermodel.decode
    (bounds : Bounds) (source : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularRoleCountermodel) :
    Except String (DecodedRegularRoleCountermodel bounds source subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported regular-role CB countermodel version {wire.version}"
  let clauses ← wire.clauses.mapM (WireSafeClause.decode bounds.concepts bounds.roles)
  let chains ← wire.chains.mapM (WireBinaryChain.decode bounds.roles)
  let safe : SafeSource (Fin bounds.concepts) (Fin bounds.roles)
      (Fin bounds.individuals) := { clauses, chains }
  if hsource : CBRoleChainEncoding.encode safe.toSource = source then
    let regular ← wire.regular.decodeAt bounds.concepts bounds.roles 3
    if hroles : regular.certificate.roleClauses =
        roleClauses (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) safe then
      if hresidual : regular.certificate.residual =
          residual (0 : Fin 3) (2 : Fin 3) safe.clauses then
        let sub ← checkedFinExact "regular-role subclass" bounds.concepts subRaw
        let sup ← checkedFinExact "regular-role superclass" bounds.concepts supRaw
        if hsub : (⟨0, regular.positive⟩, .pos sub.val) ∈
            regular.certificate.labels then
          if hsup : (⟨0, regular.positive⟩, .negated sup.val) ∈
              regular.certificate.labels then
            if hcheck : regular.certificate.check = true then
              return {
                safe
                source_exact := hsource
                regular
                role_clauses_exact := hroles
                residual_exact := hresidual
                sub := sub.val
                sup := sup.val
                sub_exact := sub.property
                sup_exact := sup.property
                root_sub := hsub
                root_not_sup := hsup
                accepted := hcheck }
            else throw "regular-role CB countermodel certificate was rejected"
          else throw "regular-role CB countermodel omits the negative query literal"
        else throw "regular-role CB countermodel omits the positive query literal"
      else throw "regular residual clauses differ from the exact safe-source translation"
    else throw "regular role clauses differ from the exact safe-source RBox"
  else throw "regular-role encoding differs from the exact CB source ontology"

theorem DecodedRegularRoleCountermodel.refutes
    (decoded : DecodedRegularRoleCountermodel bounds source subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ source, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.regular.nodeCount :=
    ⟨Nat.ne_of_gt decoded.regular.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    checked_regular_role_countermodel decoded.regular.certificate
      (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) (by decide) (by decide) (by decide)
      decoded.safe decoded.sub decoded.sup decoded.role_clauses_exact
      decoded.residual_exact
      (by simpa [FiniteRegularCertificate.state] using decoded.root_sub)
      (by simpa [FiniteRegularCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, ?_, ?_⟩
  · simpa [decoded.source_exact] using hsource
  · exact decoded.sub_exact ▸ hsub
  · exact decoded.sup_exact ▸ hsup

#print axioms DecodedRegularRoleCountermodel.refutes

end ContextCalculus.CBRegularRoleCountermodelWire
