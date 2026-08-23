import ContextCalculus.CBRegularArbitraryChainCountermodel
import ContextCalculus.CBRegularFreshCardinalityCountermodelWire
import ContextCalculus.CBRoleChainBinaryDerivationWire

/-! # Exact wire for regular CB countermodels with arbitrary role chains -/

namespace ContextCalculus.CBRegularArbitraryChainCountermodelWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding
open ContextCalculus.Hypertableau
open ContextCalculus.Hypertableau.AnchoredForestDomain

structure WireRoleChain where
  body : List Nat
  sup : Nat
deriving FromJson, ToJson

structure WireRegularArbitraryChainCountermodel where
  version : Nat
  clauses : List
    CBRegularFreshCardinalityCountermodelWire.WireSafeClause
  chains : List WireRoleChain
  target_role_count : Nat
  binary_chains : List CBRegularRoleCountermodelWire.WireBinaryChain
  chain_derivations : List CBRoleChainBinaryDerivationWire.WireDerivation
  individual_roots : List Nat
  anchored : WireAnchoredCardinalityEqCertificate
deriving FromJson, ToJson

private def checkedFin (kind : String) (bound value : Nat) :
    Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

private def checkedFinExact (kind : String) (bound value : Nat) :
    Except String { index : Fin bound // index.val = value } :=
  if h : value < bound then .ok ⟨⟨value, h⟩, rfl⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

def WireRoleChain.decode (roleCount : Nat) (wire : WireRoleChain) :
    Except String (RoleChain (Fin roleCount)) := do
  return {
    body := ← wire.body.mapM (checkedFin "arbitrary-chain body role" roleCount)
    sup := ← checkedFin "arbitrary-chain super-role" roleCount wire.sup }

structure DecodedRegularArbitraryChainCountermodel
    (bounds : Bounds) (productionSource : List FCL) (subRaw supRaw : Nat) where
  source : CBRegularArbitraryChainCountermodel.SafeSource
    (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals)
  source_exact : CBRoleChainEncoding.encode source.toSource = productionSource
  targetRoleCount : Nat
  role_le : bounds.roles ≤ targetRoleCount
  binaryChains : List
    (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount))
  derivations : ∀ chain, chain ∈ source.chains →
    CBRoleChainBinaryDerivation.Derivation (Fin.castLE role_le) binaryChains
      chain.body (Fin.castLE role_le chain.sup)
  anchored : DecodedAnchoredCardinalityEqCertificateAt
    (bounds.concepts + 1) targetRoleCount 3
  eq_positive : 0 < anchored.eqNodeCount
  individualRoot : Fin bounds.individuals → Fin anchored.regularNodeCount
  role_clauses_exact : anchored.certificate.anchored.regular.roleClauses =
    CBRegularRoleCountermodel.roleClauses (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (source.toTarget Fin.succ (Fin.castLE role_le)
        (0 : Fin (bounds.concepts + 1)) binaryChains).core.base
  residual_exact : anchored.certificate.anchored.regular.residual =
    CBRegularRoleCountermodel.residual (0 : Fin 3) (2 : Fin 3)
        (source.toTarget Fin.succ (Fin.castLE role_le)
          (0 : Fin (bounds.concepts + 1)) binaryChains).core.base.clauses ++
      (source.toTarget Fin.succ (Fin.castLE role_le)
        (0 : Fin (bounds.concepts + 1)) binaryChains).activationClauses
          (0 : Fin 3)
  definitions_exact : anchored.certificate.definitions =
    (source.toTarget Fin.succ (Fin.castLE role_le)
      (0 : Fin (bounds.concepts + 1)) binaryChains).definitions
  nominal_roots_exact : ∀ nominal,
    CBRegularNominalCountermodel.SafeClause.nominal nominal ∈
      (source.toTarget Fin.succ (Fin.castLE role_le)
        (0 : Fin (bounds.concepts + 1)) binaryChains).core.clauses →
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

def WireRegularArbitraryChainCountermodel.decode
    (bounds : Bounds) (productionSource : List FCL) (subRaw supRaw : Nat)
    (wire : WireRegularArbitraryChainCountermodel) : Except String
      (DecodedRegularArbitraryChainCountermodel bounds productionSource
        subRaw supRaw) := do
  if wire.version != 1 then
    throw s!"unsupported arbitrary-chain CB countermodel version {wire.version}"
  let clauses ← wire.clauses.mapM
    (CBRegularFreshCardinalityCountermodelWire.WireSafeClause.decode
      bounds.concepts bounds.roles bounds.individuals)
  let chains ← wire.chains.mapM (WireRoleChain.decode bounds.roles)
  let source : CBRegularArbitraryChainCountermodel.SafeSource
      (Fin bounds.concepts) (Fin bounds.roles) (Fin bounds.individuals) :=
    { clauses, chains }
  if hsource : CBRoleChainEncoding.encode source.toSource = productionSource then
    if hroleLe : bounds.roles ≤ wire.target_role_count then
      let roleMap : Fin bounds.roles → Fin wire.target_role_count :=
        Fin.castLE hroleLe
      let binaryChains ← wire.binary_chains.mapM
        (CBRegularRoleCountermodelWire.WireBinaryChain.decode
          wire.target_role_count)
      let derivations ← CBRoleChainBinaryDerivationWire.decodeAll roleMap
        binaryChains source.chains wire.chain_derivations
      let anchored ← wire.anchored.decodeAt
        (bounds.concepts + 1) wire.target_role_count 3
      if heq : 0 < anchored.eqNodeCount then
        let individualRoot ← decodeClassMap bounds.individuals
          anchored.regularNodeCount wire.individual_roots
        let targetSafe := source.toTarget Fin.succ roleMap
          (0 : Fin (bounds.concepts + 1)) binaryChains
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
                let sub ← checkedFinExact "arbitrary-chain subclass"
                  bounds.concepts subRaw
                let sup ← checkedFinExact "arbitrary-chain superclass"
                  bounds.concepts supRaw
                if hsub : (⟨0, heq⟩, .pos (Fin.succ sub.val)) ∈
                    anchored.certificate.anchored.equality.base.labels then
                  if hsup : (⟨0, heq⟩, .negated (Fin.succ sup.val)) ∈
                      anchored.certificate.anchored.equality.base.labels then
                    if hcheck : anchored.certificate.check = true then
                      return {
                        source, source_exact := hsource,
                        targetRoleCount := wire.target_role_count,
                        role_le := hroleLe, binaryChains,
                        derivations := derivations.derivations,
                        anchored, eq_positive := heq, individualRoot,
                        role_clauses_exact := hroles,
                        residual_exact := hresidual,
                        definitions_exact := hdefinitions,
                        nominal_roots_exact :=
                          CBRegularNominalCountermodelWire.nominalRootsB_sound
                            hnominals,
                        sub := sub.val, sup := sup.val,
                        sub_exact := sub.property, sup_exact := sup.property,
                        root_sub := hsub, root_not_sup := hsup,
                        accepted := hcheck }
                    else throw "arbitrary-chain anchored certificate was rejected"
                  else throw "arbitrary-chain countermodel omits the negative query literal"
                else throw "arbitrary-chain countermodel omits the positive query literal"
              else throw "arbitrary-chain individual roots differ from nominal anchors"
            else throw "arbitrary-chain definitions differ from the target projection"
          else throw "arbitrary-chain residual differs from the target projection"
        else throw "arbitrary-chain role clauses differ from the target projection"
      else throw "arbitrary-chain equality state requires at least one node"
    else throw "arbitrary-chain target role bound is smaller than the source bound"
  else throw "arbitrary-chain encoding differs from the exact CB source ontology"

theorem DecodedRegularArbitraryChainCountermodel.refutes
    (decoded : DecodedRegularArbitraryChainCountermodel
      bounds productionSource subRaw supRaw) :
    ∃ (D : Type) (model : TModel D) (element : D),
      (∀ clause ∈ productionSource, valid model clause) ∧
      model.conc subRaw element ∧ ¬model.conc supRaw element := by
  letI : NeZero decoded.anchored.eqNodeCount :=
    ⟨Nat.ne_of_gt decoded.eq_positive⟩
  letI : NeZero decoded.anchored.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.anchored.positive⟩
  obtain ⟨D, model, element, hsource, hsub, hsup⟩ :=
    CBRegularArbitraryChainCountermodel.checked_arbitrary_chain_countermodel
      decoded.anchored.certificate (0 : Fin 3) (1 : Fin 3) (2 : Fin 3)
      (by decide) (by decide) (by decide) decoded.source Fin.succ
      (Fin.castLE decoded.role_le) (0 : Fin (bounds.concepts + 1))
      decoded.binaryChains decoded.derivations decoded.individualRoot
      decoded.sub decoded.sup decoded.role_clauses_exact decoded.residual_exact
      decoded.definitions_exact decoded.nominal_roots_exact
      (by simpa [FiniteEqCertificate.state] using decoded.root_sub)
      (by simpa [FiniteEqCertificate.state] using decoded.root_not_sup)
      decoded.accepted
  refine ⟨D, model, element, ?_, decoded.sub_exact ▸ hsub,
    decoded.sup_exact ▸ hsup⟩
  simpa [decoded.source_exact] using hsource

#print axioms DecodedRegularArbitraryChainCountermodel.refutes

end ContextCalculus.CBRegularArbitraryChainCountermodelWire
