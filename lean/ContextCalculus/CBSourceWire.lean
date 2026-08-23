import ContextCalculus.CBRoleChainEncoding
import ContextCalculus.CBTermDerivationWire

/-!
# Exact production-source binding for CB certificates

The existing CB certificate wires accept a complete nested-term clause list.
This module additionally decodes the normalized typed source constructors and
checks that their verified encoding is exactly that clause list. Acceptance
therefore connects certificate semantics to disjunction, restrictions, role
axioms, equality, nominals, cardinality, and arbitrary role-chain semantics.
-/

namespace ContextCalculus.CBSourceWire

open Lean ContextCalculus CheckerTerm Eqv
open ContextCalculus.CBTermWire
open ContextCalculus.CBRoleChainEncoding

inductive WireSourceClause where
  | gci (body head : List Nat)
  | exR (source role filler : Nat)
  | allR (source role filler : Nat)
  | exL (role filler conclusion : Nat)
  | subR (sub sup : Nat)
  | inverse (role inverse : Nat)
  | functional (role : Nat)
  | nominal (concept individual : Nat)
  | atMost (cardinality role concept : Nat)
deriving DecidableEq, FromJson, ToJson

structure WireRoleChain where
  body : List Nat
  sup : Nat
deriving DecidableEq, FromJson, ToJson

structure WireSourceBinding where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  source_clauses : List WireSourceClause
  role_chains : List WireRoleChain
  ontology : List WireClause
deriving FromJson, ToJson

def WireSourceBinding.bounds (wire : WireSourceBinding) : Bounds :=
  { concepts := wire.concept_count
  , roles := wire.role_count
  , functions := wire.function_count
  , individuals := wire.individual_count }

private def checkedFin (kind : String) (bound value : Nat) : Except String (Fin bound) := do
  let checked ← checkId kind bound value
  if h : checked < bound then return ⟨checked, h⟩
  else throw s!"internal {kind} bounds failure"

def WireSourceClause.decode (bounds : Bounds) : WireSourceClause →
    Except String (OClause (Fin bounds.concepts) (Fin bounds.roles)
      (Fin bounds.individuals))
  | .gci body head =>
      return .gci
        (← body.mapM (checkedFin "source concept" bounds.concepts))
        (← head.mapM (checkedFin "source concept" bounds.concepts))
  | .exR source role filler =>
      return .exR
        (← checkedFin "source concept" bounds.concepts source)
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source concept" bounds.concepts filler)
  | .allR source role filler =>
      return .allR
        (← checkedFin "source concept" bounds.concepts source)
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source concept" bounds.concepts filler)
  | .exL role filler conclusion =>
      return .exL
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source concept" bounds.concepts filler)
        (← checkedFin "source concept" bounds.concepts conclusion)
  | .subR sub sup =>
      return .subR
        (← checkedFin "source role" bounds.roles sub)
        (← checkedFin "source role" bounds.roles sup)
  | .inverse role inverseRole =>
      return .inv
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source role" bounds.roles inverseRole)
  | .functional role =>
      return .func (← checkedFin "source role" bounds.roles role)
  | .nominal concept individual =>
      return .nom
        (← checkedFin "source concept" bounds.concepts concept)
        (← checkedFin "source individual" bounds.individuals individual)
  | .atMost cardinality role concept =>
      return .atMost cardinality
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source concept" bounds.concepts concept)

def WireRoleChain.decode (bounds : Bounds) (wire : WireRoleChain) :
    Except String (RoleChain (Fin bounds.roles)) :=
  return {
    body := ← wire.body.mapM (checkedFin "chain role" bounds.roles)
    sup := ← checkedFin "chain super-role" bounds.roles wire.sup
  }

structure DecodedSourceBinding where
  bounds : Bounds
  source : SourceOntology (Fin bounds.concepts) (Fin bounds.roles)
    (Fin bounds.individuals)
  ontology : List FCL
  exact_encoding : ontology = CBRoleChainEncoding.encode source

def WireSourceBinding.decode (wire : WireSourceBinding) :
    Except String DecodedSourceBinding := do
  if wire.version != 1 then
    throw s!"unsupported CB source-binding version {wire.version}"
  if wire.concept_count = 0 then
    throw "concept_count must be positive"
  let bounds := wire.bounds
  let clauses ← wire.source_clauses.mapM (WireSourceClause.decode bounds)
  let chains ← wire.role_chains.mapM (WireRoleChain.decode bounds)
  let source : SourceOntology (Fin bounds.concepts) (Fin bounds.roles)
      (Fin bounds.individuals) := { clauses, chains }
  let ontology ← wire.ontology.mapM (WireClause.decode bounds)
  if hencoding : ontology = CBRoleChainEncoding.encode source then
    return { bounds, source, ontology, exact_encoding := hencoding }
  else throw "decoded CB ontology differs from the verified source encoding"

def WireSourceBinding.check (wire : WireSourceBinding) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedSourceBinding.Entails (decoded : DecodedSourceBinding)
    (sub sup : Fin decoded.bounds.concepts) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ decoded.ontology, valid model clause) →
      ∀ element, model.conc sub.val element → model.conc sup.val element

theorem DecodedSourceBinding.entails_iff_source (decoded : DecodedSourceBinding)
    (sub sup : Fin decoded.bounds.concepts) :
    decoded.Entails sub sup ↔
      ∀ (D : Type)
        (interpretation : Eqv.Interp D (Fin decoded.bounds.concepts)
          (Fin decoded.bounds.roles) (Fin decoded.bounds.individuals)),
        CBRoleChainEncoding.models interpretation decoded.source → ∀ element,
          interpretation.c sub element → interpretation.c sup element := by
  rw [DecodedSourceBinding.Entails, decoded.exact_encoding]
  exact CBRoleChainEncoding.entailsSub_iff_source decoded.source sub sup

theorem WireSourceBinding.check_sound (wire : WireSourceBinding)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceBinding,
      wire.decode = .ok decoded ∧
        decoded.ontology = CBRoleChainEncoding.encode decoded.source ∧
        ∀ sub sup : Fin decoded.bounds.concepts,
          decoded.Entails sub sup ↔
            ∀ (D : Type)
              (interpretation : Eqv.Interp D (Fin decoded.bounds.concepts)
                (Fin decoded.bounds.roles) (Fin decoded.bounds.individuals)),
              CBRoleChainEncoding.models interpretation decoded.source → ∀ element,
                interpretation.c sub element → interpretation.c sup element := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceBinding.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.exact_encoding,
        decoded.entails_iff_source⟩

private def concept (id : Nat) (term : WireTerm) : WireLiteral :=
  .predicate (.concept id term)

private def acceptedExample : WireSourceBinding where
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 1
  individual_count := 0
  source_clauses := [.gci [0] [1]]
  role_chains := []
  ontology := [⟨[concept 0 (.var 0)], [concept 1 (.var 0)]⟩]

example : acceptedExample.check = .ok true := by native_decide

private def detachedExample : WireSourceBinding :=
  { acceptedExample with ontology := [⟨[], [concept 1 (.var 0)]⟩] }

example : detachedExample.check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide

#print axioms DecodedSourceBinding.entails_iff_source
#print axioms WireSourceBinding.check_sound

end ContextCalculus.CBSourceWire
