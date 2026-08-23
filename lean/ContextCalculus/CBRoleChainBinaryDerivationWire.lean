import ContextCalculus.CBRoleChainBinaryDerivation
import ContextCalculus.CBTermDerivationWire

/-! # Bounds-checked wire for arbitrary-chain binary derivations -/

namespace ContextCalculus.CBRoleChainBinaryDerivationWire

open Lean ContextCalculus
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding

private def checkedFin (kind : String) (bound value : Nat) :
    Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

inductive WireDerivation where
  | atom (role : Nat)
  | compose (left right : WireDerivation) (rule : Nat)
deriving FromJson, ToJson

structure DecodedDerivation
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (rules : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount))) where
  body : List (Fin sourceRoleCount)
  result : Fin targetRoleCount
  derivation : CBRoleChainBinaryDerivation.Derivation roleMap rules body result

def WireDerivation.decode
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (rules : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount))) :
    WireDerivation → Except String (DecodedDerivation roleMap rules)
  | .atom role => do
      let decoded ← checkedFin "chain-derivation source role"
        sourceRoleCount role
      return {
        body := [decoded]
        result := roleMap decoded
        derivation := .atom decoded }
  | .compose left right ruleIndex => do
      let leftDecoded ← left.decode roleMap rules
      let rightDecoded ← right.decode roleMap rules
      let index ← checkedFin "chain-derivation binary rule" rules.length ruleIndex
      let rule := rules.get index
      if hfirst : rule.first = leftDecoded.result then
        if hsecond : rule.second = rightDecoded.result then
          return {
            body := leftDecoded.body ++ rightDecoded.body
            result := rule.conclusion
            derivation := .compose leftDecoded.derivation rightDecoded.derivation
              rule (rules.get_mem index) hfirst hsecond rfl }
        else throw "chain-derivation rule has the wrong right premise role"
      else throw "chain-derivation rule has the wrong left premise role"

structure DecodedAll
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (rules : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount)))
    (chains : List (RoleChain (Fin sourceRoleCount))) : Type where
  derivations : ∀ chain, chain ∈ chains →
    CBRoleChainBinaryDerivation.Derivation roleMap rules
      chain.body (roleMap chain.sup)

def decodeAll
    (roleMap : Fin sourceRoleCount → Fin targetRoleCount)
    (rules : List
      (CBRegularRoleCountermodel.BinaryChain (Fin targetRoleCount))) :
    (chains : List (RoleChain (Fin sourceRoleCount))) →
    List WireDerivation → Except String (DecodedAll roleMap rules chains)
  | [], [] => .ok {
      derivations := by
        intro chain hchain
        simp at hchain }
  | [], _ :: _ => .error "chain-derivation list has trailing entries"
  | _ :: _, [] => .error "chain-derivation list omits a source chain"
  | chain :: chains, wire :: wires => do
      let decoded ← wire.decode roleMap rules
      if hbody : decoded.body = chain.body then
        if hresult : decoded.result = roleMap chain.sup then
          let tail ← decodeAll roleMap rules chains wires
          let hall : ∀ actual, actual ∈ chain :: chains →
              CBRoleChainBinaryDerivation.Derivation roleMap rules
                actual.body (roleMap actual.sup) := by
            intro actual hactual
            rcases List.mem_cons.mp hactual with hequal | htail
            · subst actual
              simpa only [hbody, hresult] using decoded.derivation
            · exact tail.derivations actual htail
          return { derivations := hall }
        else throw "chain derivation concludes with the wrong super-role"
      else throw "chain derivation covers the wrong source-role body"

end ContextCalculus.CBRoleChainBinaryDerivationWire
