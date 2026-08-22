import ContextCalculus.HypertableauAddressRefinement

/-!
# Combined finite-state and rooted-address wire checker

The ordinary frontier document proves only that addresses are finite and
distinct. This combined document also carries the exact finite HT state. Lean
decodes both under one signature and checks their semantic correspondence.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireAddressRefinementDocument where
  version : Nat
  state : WireCertificate
  frontier : WireAddressFrontier
deriving FromJson, ToJson, Repr

structure DecodedAddressRefinement where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount
  address : Fin nodeCount →
    WitnessAddress (Fin 1) (Fin conceptCount) (Fin roleCount)
  injective : Function.Injective address

def WireAddressRefinementDocument.decode
    (document : WireAddressRefinementDocument) :
    Except String DecodedAddressRefinement := do
  if document.version != 1 then
    throw s!"unsupported HT address-refinement version {document.version}"
  let decoded ← document.state.decodeBase
  if document.frontier.node_count != decoded.nodeCount then
    throw "HT address-refinement node count differs from its state"
  if document.frontier.concept_count != decoded.conceptCount then
    throw "HT address-refinement concept count differs from its state"
  if document.frontier.role_count != decoded.roleCount then
    throw "HT address-refinement role count differs from its state"
  if document.frontier.version != 1 then
    throw s!"unsupported HT frontier wire version {document.frontier.version}"
  let addresses ← document.frontier.addresses.mapM
    (decodeWireWitnessAddress decoded.conceptCount decoded.roleCount)
  if hlength : addresses.length = decoded.nodeCount then
    if hnodup : addresses.Nodup then
      let address : Fin decoded.nodeCount →
          WitnessAddress (Fin 1) (Fin decoded.conceptCount)
            (Fin decoded.roleCount) :=
        fun node => addresses.get (Fin.cast hlength.symm node)
      return {
        nodeCount := decoded.nodeCount
        conceptCount := decoded.conceptCount
        roleCount := decoded.roleCount
        variableCount := decoded.variableCount
        certificate := decoded.certificate
        address := address
        injective := by
          intro left right hequal
          have hcast : Fin.cast hlength.symm left = Fin.cast hlength.symm right :=
            hnodup.injective_get hequal
          have hval := congrArg (fun node => node.val) hcast
          apply Fin.ext
          simpa using hval
      }
    else
      throw "HT address-refinement contains duplicate rooted addresses"
  else
    throw "HT address-refinement address count differs from its state"

def DecodedAddressRefinement.check
    (decoded : DecodedAddressRefinement) : Bool :=
  let state := decoded.certificate.state
  letI : DecidableState state := {
    label := fun node literal => by
      change Decidable ((node, literal) ∈ decoded.certificate.labels)
      infer_instance
    edge := fun role source target => by
      change Decidable ((role, source, target) ∈ decoded.certificate.edges)
      infer_instance
    obligation := fun role filler node => by
      change Decidable ((role, filler, node) ∈ decoded.certificate.obligations)
      infer_instance
  }
  state.checkRootedAddressRefines decoded.address

def WireAddressRefinementDocument.check
    (document : WireAddressRefinementDocument) : Except String Bool := do
  return (← document.decode).check

theorem DecodedAddressRefinement.check_sound
    (decoded : DecodedAddressRefinement)
    (hcheck : decoded.check = true) :
    decoded.certificate.state.RootedAddressRefines decoded.address := by
  let state := decoded.certificate.state
  letI : DecidableState state := {
    label := fun node literal => by
      change Decidable ((node, literal) ∈ decoded.certificate.labels)
      infer_instance
    edge := fun role source target => by
      change Decidable ((role, source, target) ∈ decoded.certificate.edges)
      infer_instance
    obligation := fun role filler node => by
      change Decidable ((role, filler, node) ∈ decoded.certificate.obligations)
      infer_instance
  }
  exact state.checkRootedAddressRefines_sound decoded.address hcheck

theorem WireAddressRefinementDocument.check_sound
    (document : WireAddressRefinementDocument)
    (hcheck : document.check = .ok true) :
    ∃ decoded, document.decode = .ok decoded ∧
      decoded.certificate.state.RootedAddressRefines decoded.address := by
  cases hdecode : document.decode with
  | error message => simp [WireAddressRefinementDocument.check, hdecode] at hcheck
  | ok decoded =>
      have hdecoded : decoded.check = true := by
        simpa [WireAddressRefinementDocument.check, hdecode] using hcheck
      exact ⟨decoded, by simpa using hdecode, decoded.check_sound hdecoded⟩

#print axioms DecodedAddressRefinement.check_sound
#print axioms WireAddressRefinementDocument.check_sound

end ContextCalculus.Hypertableau
