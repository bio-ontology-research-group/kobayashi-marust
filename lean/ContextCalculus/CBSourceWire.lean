import ContextCalculus.CBRoleChainEncoding
import ContextCalculus.CBTermDerivationWire
import ContextCalculus.CBFunctionAllocationWire

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
open ContextCalculus.CBFunctionRenaming
open ContextCalculus.CBFunctionAllocationWire

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
  | guardedAtMost (source cardinality role concept : Nat)
deriving DecidableEq, FromJson, ToJson

structure WireRoleChain where
  body : List Nat
  sup : Nat
deriving DecidableEq, FromJson, ToJson

inductive WireRoleAxiom where
  | symmetric (role : Nat)
  | asymmetric (role : Nat)
  | reflexive (role : Nat)
  | irreflexive (role : Nat)
  | inverseFunctional (role : Nat)
  | disjoint (left right : Nat)
deriving DecidableEq, FromJson, ToJson

structure WireSourceBinding where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  source_clauses : List WireSourceClause
  role_chains : List WireRoleChain
  role_axioms : List WireRoleAxiom := []
  ontology : List WireClause
  function_allocation : Option WireFunctionAllocation := none
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
  | .guardedAtMost source cardinality role concept =>
      return .guardedAtMost
        (← checkedFin "source concept" bounds.concepts source)
        cardinality
        (← checkedFin "source role" bounds.roles role)
        (← checkedFin "source concept" bounds.concepts concept)

def WireRoleChain.decode (bounds : Bounds) (wire : WireRoleChain) :
    Except String (RoleChain (Fin bounds.roles)) :=
  return {
    body := ← wire.body.mapM (checkedFin "chain role" bounds.roles)
    sup := ← checkedFin "chain super-role" bounds.roles wire.sup
  }

def WireRoleAxiom.decode (bounds : Bounds) : WireRoleAxiom →
    Except String (RoleAxiom (Fin bounds.roles))
  | .symmetric role =>
      return .symmetric (← checkedFin "symmetric role" bounds.roles role)
  | .asymmetric role =>
      return .asymmetric (← checkedFin "asymmetric role" bounds.roles role)
  | .reflexive role =>
      return .reflexive (← checkedFin "reflexive role" bounds.roles role)
  | .irreflexive role =>
      return .irreflexive (← checkedFin "irreflexive role" bounds.roles role)
  | .inverseFunctional role =>
      return .inverseFunctional
        (← checkedFin "inverse-functional role" bounds.roles role)
  | .disjoint left right =>
      return .disjoint
        (← checkedFin "left disjoint role" bounds.roles left)
        (← checkedFin "right disjoint role" bounds.roles right)

/-- Production clauses are sets of body and head literals: the Rust parser
sorts and deduplicates both lists before saturation. Source encoders retain
constructor order. This relation checks exact equality of the two literal sets
without assigning semantic significance to list order or duplication. -/
def ClauseEquivalent (left right : FCL) : Prop :=
  left.body.toFinset = right.body.toFinset ∧
    left.head.toFinset = right.head.toFinset

instance (left right : FCL) : Decidable (ClauseEquivalent left right) :=
  by unfold ClauseEquivalent; infer_instance

def OntologyEquivalent (left right : List FCL) : Prop :=
  (∀ clause ∈ left, ∃ encoded ∈ right, ClauseEquivalent clause encoded) ∧
    ∀ encoded ∈ right, ∃ clause ∈ left, ClauseEquivalent clause encoded

instance (left right : List FCL) : Decidable (OntologyEquivalent left right) :=
  by unfold OntologyEquivalent; infer_instance

private theorem ClauseEquivalent.mem_body_iff {left right : FCL}
    (hequivalent : ClauseEquivalent left right) (literal : FLit) :
    literal ∈ left.body ↔ literal ∈ right.body := by
  simpa only [List.mem_toFinset] using
    Finset.ext_iff.mp hequivalent.1 literal

private theorem ClauseEquivalent.mem_head_iff {left right : FCL}
    (hequivalent : ClauseEquivalent left right) (literal : FLit) :
    literal ∈ left.head ↔ literal ∈ right.head := by
  simpa only [List.mem_toFinset] using
    Finset.ext_iff.mp hequivalent.2 literal

private theorem ClauseEquivalent.valid_iff (model : TModel D)
    {left right : FCL} (hequivalent : ClauseEquivalent left right) :
    valid model left ↔ valid model right := by
  constructor <;> intro hvalid assignment hbody
  · rcases hvalid assignment (fun literal hliteral =>
      hbody literal ((hequivalent.mem_body_iff literal).mp hliteral)) with
      ⟨literal, hliteral, htrue⟩
    exact ⟨literal, (hequivalent.mem_head_iff literal).mp hliteral, htrue⟩
  · rcases hvalid assignment (fun literal hliteral =>
      hbody literal ((hequivalent.mem_body_iff literal).mpr hliteral)) with
      ⟨literal, hliteral, htrue⟩
    exact ⟨literal, (hequivalent.mem_head_iff literal).mpr hliteral, htrue⟩

structure DecodedSourceBinding where
  bounds : Bounds
  source : SourceOntology (Fin bounds.concepts) (Fin bounds.roles)
    (Fin bounds.individuals)
  ontology : List FCL
  allocation : Nat → Nat
  allocation_injective : Function.Injective allocation
  exact_encoding : OntologyEquivalent ontology (renameOntology allocation
    (CBRoleChainEncoding.encode source))

def WireSourceBinding.decode (wire : WireSourceBinding) :
    Except String DecodedSourceBinding := do
  if wire.version != 1 && wire.version != 2 then
    throw s!"unsupported CB source-binding version {wire.version}"
  if wire.concept_count = 0 then
    throw "concept_count must be positive"
  let bounds := wire.bounds
  let clauses ← wire.source_clauses.mapM (WireSourceClause.decode bounds)
  let chains ← wire.role_chains.mapM (WireRoleChain.decode bounds)
  let roleAxioms ← wire.role_axioms.mapM (WireRoleAxiom.decode bounds)
  let source : SourceOntology (Fin bounds.concepts) (Fin bounds.roles)
      (Fin bounds.individuals) := { clauses, chains, roleAxioms }
  let ontology ← wire.ontology.mapM (WireClause.decode bounds)
  if wire.version = 1 then
    if wire.function_allocation.isSome then
      throw "version-1 CB source binding must not carry a function allocation"
    if hencoding : OntologyEquivalent ontology (CBRoleChainEncoding.encode source) then
      return {
        bounds, source, ontology
        allocation := id
        allocation_injective := Function.injective_id
        exact_encoding := by simpa using hencoding
      }
    else throw "decoded CB ontology differs from the verified source encoding"
  else
    let allocationWire ← match wire.function_allocation with
      | some allocation => pure allocation
      | none => throw "version-2 CB source binding has no function allocation"
    let allocation ← allocationWire.decode
    if hcanonical : allocation.canonicalCount = source.clauses.length then
      if hproduction : allocation.productionCount = bounds.functions then
        if hencoding : OntologyEquivalent ontology (renameOntology allocation.rename
            (CBRoleChainEncoding.encode source)) then
          return {
            bounds, source, ontology
            allocation := allocation.rename
            allocation_injective := allocation.rename_injective
            exact_encoding := hencoding
          }
        else throw "decoded CB ontology differs from the allocated verified source encoding"
      else throw "CB function allocation production count differs from function_count"
    else throw "CB function allocation does not cover the canonical source namespace"

def WireSourceBinding.check (wire : WireSourceBinding) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedSourceBinding.Entails (decoded : DecodedSourceBinding)
    (sub sup : Fin decoded.bounds.concepts) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ decoded.ontology, valid model clause) →
      ∀ element, model.conc sub.val element → model.conc sup.val element

private theorem entails_of_equivalent {ontology encoded : List FCL}
    (hequivalent : OntologyEquivalent ontology encoded) (sub sup : Nat) :
    (∀ (D : Type) (model : TModel D),
      (∀ clause ∈ ontology, valid model clause) →
        ∀ element, model.conc sub element → model.conc sup element) ↔
    (∀ (D : Type) (model : TModel D),
      (∀ clause ∈ encoded, valid model clause) →
        ∀ element, model.conc sub element → model.conc sup element) := by
  constructor <;> intro hentails D model hmodels element hsub
  · exact hentails D model (fun clause hclause =>
      let ⟨encodedClause, hencoded, hclauseEquivalent⟩ :=
        hequivalent.1 clause hclause
      (hclauseEquivalent.valid_iff model).2
        (hmodels encodedClause hencoded)) element hsub
  · exact hentails D model (fun clause hclause =>
      let ⟨ontologyClause, hontology, hclauseEquivalent⟩ :=
        hequivalent.2 clause hclause
      (hclauseEquivalent.valid_iff model).1
        (hmodels ontologyClause hontology)) element hsub

theorem DecodedSourceBinding.entails_iff_source (decoded : DecodedSourceBinding)
    (sub sup : Fin decoded.bounds.concepts) :
    decoded.Entails sub sup ↔
      ∀ (D : Type)
        (interpretation : Eqv.Interp D (Fin decoded.bounds.concepts)
          (Fin decoded.bounds.roles) (Fin decoded.bounds.individuals)),
        CBRoleChainEncoding.models interpretation decoded.source → ∀ element,
          interpretation.c sub element → interpretation.c sup element := by
  rw [DecodedSourceBinding.Entails,
    entails_of_equivalent decoded.exact_encoding sub.val sup.val]
  change CBFunctionRenaming.Entails
      (renameOntology decoded.allocation (CBRoleChainEncoding.encode decoded.source))
      sub.val sup.val ↔ _
  rw [CBFunctionRenaming.entails_rename_iff decoded.allocation
    decoded.allocation_injective]
  exact CBRoleChainEncoding.entailsSub_iff_source decoded.source sub sup

noncomputable def DecodedSourceBinding.productionModel
    (decoded : DecodedSourceBinding)
    (interpretation : Eqv.Interp D (Fin decoded.bounds.concepts)
      (Fin decoded.bounds.roles) (Fin decoded.bounds.individuals))
    (hmodels : CBRoleChainEncoding.models interpretation decoded.source)
    (default : D) : TModel D :=
  pushforwardModel decoded.allocation
    (CBRoleChainEncoding.extendModel decoded.source interpretation hmodels default)

theorem DecodedSourceBinding.models_production (decoded : DecodedSourceBinding)
    (interpretation : Eqv.Interp D (Fin decoded.bounds.concepts)
      (Fin decoded.bounds.roles) (Fin decoded.bounds.individuals))
    (hmodels : CBRoleChainEncoding.models interpretation decoded.source)
    (default : D) :
    ∀ clause ∈ decoded.ontology,
      valid (decoded.productionModel interpretation hmodels default) clause := by
  intro clause hclause
  rcases decoded.exact_encoding.1 clause hclause with
    ⟨encodedClause, hencoded, hequivalent⟩
  rcases List.mem_map.mp hencoded with ⟨sourceClause, hsourceClause, rfl⟩
  apply (hequivalent.valid_iff _).2
  exact (valid_pushforward_iff decoded.allocation decoded.allocation_injective
    (CBRoleChainEncoding.extendModel decoded.source interpretation hmodels default)
    sourceClause).2
    (CBRoleChainEncoding.models_extend decoded.source interpretation hmodels default
      sourceClause hsourceClause)

theorem WireSourceBinding.check_sound (wire : WireSourceBinding)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceBinding,
      wire.decode = .ok decoded ∧
        OntologyEquivalent decoded.ontology (renameOntology decoded.allocation
          (CBRoleChainEncoding.encode decoded.source)) ∧
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

private def role (id : Nat) (source target : WireTerm) : WireLiteral :=
  .predicate (.role id source target)

private def allocatedExample : WireSourceBinding where
  version := 2
  concept_count := 2
  role_count := 1
  function_count := 2
  individual_count := 0
  source_clauses := [.exR 0 0 1]
  role_chains := []
  ontology :=
    [ ⟨[concept 0 (.var 0)], [role 0 (.var 0) (.app 1 (.var 0))]⟩
    , ⟨[concept 0 (.var 0)], [concept 1 (.app 1 (.var 0))]⟩ ]
  function_allocation := some {
    version := 1
    canonical_count := 1
    production_count := 2
    allocation := [1]
  }

example : allocatedExample.check = .ok true := by native_decide

private def duplicateAllocationExample : WireSourceBinding where
  version := 2
  concept_count := 2
  role_count := 0
  function_count := 2
  individual_count := 0
  source_clauses := [.gci [0] [1], .gci [1] [0]]
  role_chains := []
  ontology :=
    [ ⟨[concept 0 (.var 0)], [concept 1 (.var 0)]⟩
    , ⟨[concept 1 (.var 0)], [concept 0 (.var 0)]⟩ ]
  function_allocation := some {
    version := 1
    canonical_count := 2
    production_count := 2
    allocation := [1, 1]
  }

example : duplicateAllocationExample.check =
    .error "CB function allocation reuses a production Skolem id" := by
  native_decide

private def sparseNonExistentialExample : WireSourceBinding where
  version := 2
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  source_clauses := [.gci [0] [1]]
  role_chains := []
  ontology := [⟨[concept 0 (.var 0)], [concept 1 (.var 0)]⟩]
  function_allocation := some {
    version := 1
    canonical_count := 1
    production_count := 0
    allocation := [0]
  }

example : sparseNonExistentialExample.check = .ok true := by native_decide

private def sparseMixedExample : WireSourceBinding where
  version := 2
  concept_count := 2
  role_count := 1
  function_count := 1
  individual_count := 0
  source_clauses := [.gci [0] [1], .exR 0 0 1]
  role_chains := []
  ontology :=
    [ ⟨[concept 0 (.var 0)], [concept 1 (.var 0)]⟩
    , ⟨[concept 0 (.var 0)], [role 0 (.var 0) (.app 0 (.var 0))]⟩
    , ⟨[concept 0 (.var 0)], [concept 1 (.app 0 (.var 0))]⟩ ]
  function_allocation := some {
    version := 1
    canonical_count := 2
    production_count := 1
    allocation := [1, 0]
  }

example : sparseMixedExample.check = .ok true := by native_decide

private def malformedSentinelExample : WireSourceBinding :=
  { sparseNonExistentialExample with
    function_allocation := some {
      version := 1
      canonical_count := 1
      production_count := 0
      allocation := [2]
    } }

example : malformedSentinelExample.check =
    .error "CB function allocation entry is neither bounded nor its canonical sentinel" := by
  native_decide

private def roleAxiomExample (roleAxiomWire : WireRoleAxiom)
    (encoded : WireClause) : WireSourceBinding where
  version := 1
  concept_count := 1
  role_count := 2
  function_count := 0
  individual_count := 0
  source_clauses := []
  role_chains := []
  role_axioms := [roleAxiomWire]
  ontology := [encoded]

private def symmetricExample := roleAxiomExample (.symmetric 0)
  ⟨[role 0 (.var 0) (.var (-1))], [role 0 (.var (-1)) (.var 0)]⟩

private def asymmetricExample := roleAxiomExample (.asymmetric 0)
  ⟨[role 0 (.var 0) (.var (-1)), role 0 (.var (-1)) (.var 0)], []⟩

private def reflexiveExample := roleAxiomExample (.reflexive 0)
  ⟨[], [role 0 (.var 0) (.var 0)]⟩

private def irreflexiveExample := roleAxiomExample (.irreflexive 1)
  ⟨[role 1 (.var 0) (.var 0)], []⟩

private def inverseFunctionalExample := roleAxiomExample (.inverseFunctional 0)
  ⟨[role 0 (.var (-1)) (.var 0), role 0 (.var (-2)) (.var 0)],
    [.equality (.var (-1)) (.var (-2))]⟩

private def disjointExample := roleAxiomExample (.disjoint 0 1)
  ⟨[role 0 (.var 0) (.var (-1)), role 1 (.var 0) (.var (-1))], []⟩

example : symmetricExample.check = .ok true := by native_decide
example : asymmetricExample.check = .ok true := by native_decide
example : reflexiveExample.check = .ok true := by native_decide
example : irreflexiveExample.check = .ok true := by native_decide
example : inverseFunctionalExample.check = .ok true := by native_decide
example : disjointExample.check = .ok true := by native_decide

private def interleavedSourceExample : WireSourceBinding where
  version := 1
  concept_count := 3
  role_count := 1
  function_count := 0
  individual_count := 0
  source_clauses := [.gci [0] [1], .gci [1] [2]]
  role_chains := []
  role_axioms := [.reflexive 0]
  ontology :=
    [ ⟨[concept 0 (.var 0)], [concept 1 (.var 0)]⟩
    , ⟨[], [role 0 (.var 0) (.var 0)]⟩
    , ⟨[concept 1 (.var 0)], [concept 2 (.var 0)]⟩ ]

/-- Frontend axiom order may interleave semantic constructor families. The
checker retains exact multiplicity and clause structure while accepting that
semantically irrelevant list permutation. -/
example : interleavedSourceExample.check = .ok true := by native_decide

private def tamperRoleAxiomExample (wire : WireSourceBinding) : WireSourceBinding :=
  { wire with ontology := [] }

example : (tamperRoleAxiomExample symmetricExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide
example : (tamperRoleAxiomExample asymmetricExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide
example : (tamperRoleAxiomExample reflexiveExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide
example : (tamperRoleAxiomExample irreflexiveExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide
example : (tamperRoleAxiomExample inverseFunctionalExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide
example : (tamperRoleAxiomExample disjointExample).check =
    .error "decoded CB ontology differs from the verified source encoding" := by
  native_decide

#print axioms DecodedSourceBinding.entails_iff_source
#print axioms WireSourceBinding.check_sound

end ContextCalculus.CBSourceWire
