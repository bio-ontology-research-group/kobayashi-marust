import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauNativeABoxDecision
import ContextCalculus.HypertableauWire
import ContextCalculus.HypertableauCardinalityDistinctWire

/-!
# Checked native-ABox projection wire

This module mirrors the numeric `NativeAboxJson` payload consumed by KM's
hypertableau.  All concept, role, nominal, and individual identifiers are
decoded inside Lean.  Acceptance also requires the production invariants:
complete metadata, one or more singleton proxies per individual, nominal
membership for every proxy, and globally unique proxy ownership.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNativeIndividual where
  proxies : List Nat
  assertions : List Nat
deriving FromJson, ToJson, Repr

structure WireNativeABox where
  complete : Bool
  concepts : List String
  roles : List String
  nominals : List Nat
  individuals : List WireNativeIndividual
  different : List (Nat × Nat)
  role_assertions : List (List Nat)
  negative_role_assertions : List (List Nat)
deriving FromJson, ToJson, Repr

structure DecodedNativeIndividual (conceptCount : Nat) where
  proxies : List (Fin conceptCount)
  assertions : List (Fin conceptCount)

def WireNativeIndividual.decode (conceptCount : Nat)
    (wire : WireNativeIndividual) : Except String (DecodedNativeIndividual conceptCount) := do
  return {
    proxies := ← wire.proxies.mapM (checkedFin "native ABox proxy" conceptCount)
    assertions := ← wire.assertions.mapM
      (checkedFin "native ABox assertion" conceptCount)
  }

def decodeNativePair (individualCount : Nat) (pair : Nat × Nat) :
    Except String (Fin individualCount × Fin individualCount) := do
  return (← checkedFin "native ABox individual" individualCount pair.1,
    ← checkedFin "native ABox individual" individualCount pair.2)

def decodeNativeRoleAssertion (roleCount individualCount : Nat)
    (assertion : List Nat) :
    Except String (Fin roleCount × Fin individualCount × Fin individualCount) :=
  match assertion with
  | [role, source, target] => do
      return (← checkedFin "native ABox role" roleCount role,
        ← checkedFin "native ABox source individual" individualCount source,
        ← checkedFin "native ABox target individual" individualCount target)
  | _ => throw "native ABox role assertion must contain exactly three identifiers"

def decodedNativeABox
    (individuals : List (DecodedNativeIndividual conceptCount))
    (different : List (Fin individuals.length × Fin individuals.length))
    (roles negativeRoles :
      List (Fin roleCount × Fin individuals.length × Fin individuals.length)) :
    NativeABox (Fin individuals.length) (Fin conceptCount) (Fin roleCount) where
  proxies individual := (individuals.get individual).proxies
  assertions individual := (individuals.get individual).assertions
  different := different
  roleAssertions := roles
  negativeRoleAssertions := negativeRoles

structure DecodedNativeABox where
  concepts : List String
  roles : List String
  nominals : List (Fin concepts.length)
  individuals : List (DecodedNativeIndividual concepts.length)
  different : List (Fin individuals.length × Fin individuals.length)
  roleAssertions :
    List (Fin roles.length × Fin individuals.length × Fin individuals.length)
  negativeRoleAssertions :
    List (Fin roles.length × Fin individuals.length × Fin individuals.length)
  complete : Bool
  complete_true : complete = true
  concepts_nodup : concepts.Nodup
  roles_nodup : roles.Nodup
  proxies_nonempty : ∀ individual ∈ individuals, individual.proxies ≠ []
  proxies_nominal : ∀ proxy ∈ individuals.flatMap (·.proxies), proxy ∈ nominals
  proxies_unique : (individuals.flatMap (·.proxies)).Nodup

def DecodedNativeABox.abox (decoded : DecodedNativeABox) :
    NativeABox (Fin decoded.individuals.length)
      (Fin decoded.concepts.length) (Fin decoded.roles.length) :=
  decodedNativeABox decoded.individuals decoded.different decoded.roleAssertions
    decoded.negativeRoleAssertions

def DecodedNativeABox.primaryProxy (decoded : DecodedNativeABox)
    (individual : Fin decoded.individuals.length) : Fin decoded.concepts.length :=
  let entry := decoded.individuals.get individual
  entry.proxies.head (decoded.proxies_nonempty entry (List.get_mem decoded.individuals individual))

theorem DecodedNativeABox.primaryProxy_mem (decoded : DecodedNativeABox)
    (individual : Fin decoded.individuals.length) :
    decoded.primaryProxy individual ∈ decoded.abox.proxies individual := by
  apply List.head_mem

def DecodedNativeABox.negativeRoleClauses (decoded : DecodedNativeABox) :
    List (Clause (Fin 2) (Fin decoded.concepts.length) (Fin decoded.roles.length)) :=
  decoded.negativeRoleAssertions.map fun assertion =>
    negativeRoleAssertionClause
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      assertion.1 0 1

def DecodedNativeABox.seededInB (decoded : DecodedNativeABox)
    (state : FiniteDistinctEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount) : Bool :=
  ((List.finRange decoded.individuals.length).all fun individual =>
    ((decoded.abox.proxies individual ++ decoded.abox.assertions individual).all
      fun concept => decide
        ((root individual, Lit.pos concept) ∈ state.base.base.labels))) &&
  (decoded.roleAssertions.all fun assertion => decide
    ((assertion.1, root assertion.2.1, root assertion.2.2) ∈
      state.base.base.edges)) &&
  (decoded.different.all fun pair => decide
    ((root pair.1, root pair.2) ∈ state.apart))

def DecodedNativeABox.initialLabels (decoded : DecodedNativeABox)
    (root : Fin decoded.individuals.length → Fin nodeCount) :
    List (Fin nodeCount × Lit (Fin decoded.concepts.length)) :=
  (List.finRange decoded.individuals.length).flatMap fun individual =>
    (decoded.abox.proxies individual ++ decoded.abox.assertions individual).map
      fun concept => (root individual, .pos concept)

def DecodedNativeABox.initialEdges (decoded : DecodedNativeABox)
    (root : Fin decoded.individuals.length → Fin nodeCount) :
    List (Fin decoded.roles.length × Fin nodeCount × Fin nodeCount) :=
  decoded.roleAssertions.map fun assertion =>
    (assertion.1, root assertion.2.1, root assertion.2.2)

/-- Exact initial-state check used for refutation roots. Unlike `seededInB`,
this rejects every additional derived fact and every initial equality. -/
def DecodedNativeABox.exactEqSeedB (decoded : DecodedNativeABox)
    (state : FiniteEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount) : Bool :=
  decide (state.base.labels = decoded.initialLabels root) &&
  decide (state.base.edges = decoded.initialEdges root) &&
  decide (state.base.obligations = []) && decide (state.equalities = [])

theorem DecodedNativeABox.exactEqSeedB_sound
    (decoded : DecodedNativeABox)
    (state : FiniteEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount)
    (hcheck : decoded.exactEqSeedB state root = true) :
    decoded.abox.ExactEqSeed state.state root := by
  simp only [DecodedNativeABox.exactEqSeedB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hlabels, hedges⟩, hobligations⟩, hequalities⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node literal
    rw [FiniteEqCertificate.state, FiniteSatCertificate.state, hlabels]
    simp only [DecodedNativeABox.initialLabels, List.mem_flatMap,
      List.mem_finRange, true_and, List.mem_map]
    constructor
    · rintro ⟨individual, concept, hconcept, hequal⟩
      injection hequal with hnode hliteral
      exact ⟨individual, concept, hnode.symm, hconcept, hliteral.symm⟩
    · rintro ⟨individual, concept, rfl, hconcept, rfl⟩
      exact ⟨individual, concept, hconcept, rfl⟩
  · intro role source target
    rw [FiniteEqCertificate.state, FiniteSatCertificate.state, hedges]
    simp only [DecodedNativeABox.initialEdges, List.mem_map]
    constructor
    · rintro ⟨assertion, hassertion, hequal⟩
      have hrole := congrArg Prod.fst hequal
      have hrest := congrArg Prod.snd hequal
      have hsource := congrArg Prod.fst hrest
      have htarget := congrArg Prod.snd hrest
      exact ⟨assertion, hassertion, hrole.symm, hsource.symm, htarget.symm⟩
    · rintro ⟨assertion, hassertion, rfl, rfl, rfl⟩
      exact ⟨assertion, hassertion, rfl⟩
  · simpa [FiniteEqCertificate.state, FiniteSatCertificate.state, hobligations]
  · simp only [FiniteEqCertificate.state, hequalities, List.not_mem_nil]
    intro left right
    constructor
    · intro hequiv
      induction hequiv with
      | rel _ _ hfalse => exact False.elim hfalse
      | refl _ => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · intro hequal
      subst right
      exact Relation.EqvGen.refl left

theorem DecodedNativeABox.seededInB_eq_true_iff
    (decoded : DecodedNativeABox)
    (state : FiniteDistinctEqCertificate nodeCount decoded.concepts.length
      decoded.roles.length variableCount)
    (root : Fin decoded.individuals.length → Fin nodeCount) :
    decoded.seededInB state root = true ↔ decoded.abox.SeededIn state.state root := by
  simp only [DecodedNativeABox.seededInB, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, NativeABox.SeededIn, FiniteDistinctEqCertificate.state,
    FiniteEqCertificate.state, FiniteSatCertificate.state,
    decodedNativeABox, DecodedNativeABox.abox]
  constructor
  · rintro ⟨⟨hlabels, hedges⟩, hapart⟩
    refine ⟨?_, ?_, ?_⟩
    · intro individual concept hconcept
      exact hlabels individual (List.mem_finRange individual) concept hconcept
    · intro assertion hassertion
      exact hedges assertion hassertion
    · intro pair hpair
      exact hapart pair hpair
  · rintro ⟨hlabels, hedges, hapart⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro individual _ concept hconcept
      exact hlabels individual concept hconcept
    · intro assertion hassertion
      exact hedges assertion hassertion
    · intro pair hpair
      exact hapart pair hpair

theorem DecodedNativeABox.models_negativeRoleClauses_iff
    (decoded : DecodedNativeABox)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain)
    (hsingletons : decoded.abox.ProxySingletons I value) :
    I.models decoded.negativeRoleClauses ↔ decoded.abox.NegativeRoles I value := by
  constructor
  · intro hmodels assertion hassertion
    have hclause := hmodels
      (negativeRoleAssertionClause
        (decoded.primaryProxy assertion.2.1)
        (decoded.primaryProxy assertion.2.2)
        assertion.1 0 1)
      (List.mem_map.mpr ⟨assertion, hassertion, rfl⟩)
    exact (models_negativeRoleAssertionClause_iff decoded.abox I value hsingletons
      assertion.2.1 assertion.2.2
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      (decoded.primaryProxy_mem assertion.2.1)
      (decoded.primaryProxy_mem assertion.2.2)
      assertion.1 0 1 (by decide)).1 hclause
  · intro hnegative clause hclause
    rcases List.mem_map.mp hclause with ⟨assertion, hassertion, rfl⟩
    exact (models_negativeRoleAssertionClause_iff decoded.abox I value hsingletons
      assertion.2.1 assertion.2.2
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      (decoded.primaryProxy_mem assertion.2.1)
      (decoded.primaryProxy_mem assertion.2.2)
      assertion.1 0 1 (by decide)).2 (hnegative assertion hassertion)

theorem DecodedNativeABox.models_append_negativeRoleClauses_iff
    (decoded : DecodedNativeABox)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain)
    (hsingletons : decoded.abox.ProxySingletons I value)
    (ontology : List
      (Clause (Fin 2) (Fin decoded.concepts.length) (Fin decoded.roles.length))) :
    I.models (ontology ++ decoded.negativeRoleClauses) ↔
      I.models ontology ∧ decoded.abox.NegativeRoles I value := by
  constructor
  · intro hmodels
    refine ⟨?_, (decoded.models_negativeRoleClauses_iff I value hsingletons).1 ?_⟩
    · intro clause hclause
      exact hmodels clause (List.mem_append_left _ hclause)
    · intro clause hclause
      exact hmodels clause (List.mem_append_right _ hclause)
  · rintro ⟨hontology, hnegative⟩ clause hclause
    rcases List.mem_append.mp hclause with hsource | hguard
    · exact hontology clause hsource
    · exact (decoded.models_negativeRoleClauses_iff I value hsingletons).2
        hnegative clause hguard

def WireNativeABox.decode (wire : WireNativeABox) : Except String DecodedNativeABox := do
  if hcomplete : wire.complete = true then
    if hconcepts : wire.concepts.Nodup then
      if hroles : wire.roles.Nodup then
        let nominals ← wire.nominals.mapM
          (checkedFin "native ABox nominal" wire.concepts.length)
        let individuals ← wire.individuals.mapM
          (WireNativeIndividual.decode wire.concepts.length)
        if hnonempty : ∀ individual ∈ individuals, individual.proxies ≠ [] then
          let proxies := individuals.flatMap (·.proxies)
          if hnominal : ∀ proxy ∈ proxies, proxy ∈ nominals then
            if hunique : proxies.Nodup then
              let different ← wire.different.mapM
                (decodeNativePair individuals.length)
              let roleAssertions ← wire.role_assertions.mapM
                (decodeNativeRoleAssertion wire.roles.length individuals.length)
              let negativeRoleAssertions ← wire.negative_role_assertions.mapM
                (decodeNativeRoleAssertion wire.roles.length individuals.length)
              return {
                concepts := wire.concepts
                roles := wire.roles
                nominals
                individuals
                different
                roleAssertions
                negativeRoleAssertions
                complete := wire.complete
                complete_true := hcomplete
                concepts_nodup := hconcepts
                roles_nodup := hroles
                proxies_nonempty := hnonempty
                proxies_nominal := hnominal
                proxies_unique := hunique
              }
            else throw "native ABox proxy has duplicate ownership"
          else throw "native ABox proxy is absent from nominals"
        else throw "native ABox individual has no singleton proxy"
      else throw "native ABox role-name table contains duplicates"
    else throw "native ABox concept-name table contains duplicates"
  else throw "incomplete native ABox payload"

def WireNativeABox.check (wire : WireNativeABox) : Except String Bool := do
  let _ ← wire.decode
  return true

/-- Joint payload used to prove that a concrete finite HT state retains every
named-root fact. `roots` is ordered exactly like `abox.individuals`. -/
structure WireNativeABoxSeed where
  abox : WireNativeABox
  node_count : Nat
  variable_count : Nat
  roots : List Nat
  ontology : List WireClause
  state : WireDistinctEqState
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxSeed where
  abox : DecodedNativeABox
  nodeCount : Nat
  variableCount : Nat
  node_nonzero : nodeCount ≠ 0
  roots : Fin abox.individuals.length → Fin nodeCount
  roots_injective : Function.Injective roots
  ontology : List (Clause (Fin variableCount)
    (Fin abox.concepts.length) (Fin abox.roles.length))
  state : FiniteDistinctEqCertificate nodeCount abox.concepts.length
    abox.roles.length variableCount
  seeded : abox.abox.SeededIn state.state roots
  apart_check : state.apartSeparatedB = true
  apart_separated : ∀ pair ∈ state.apart,
    ¬state.base.state.equiv pair.1 pair.2

def requireNodeZero (nodeCount : Nat) : Except String (Fin nodeCount) :=
  if hnode : 0 < nodeCount then .ok ⟨0, hnode⟩
  else .error "native ABox finite state must contain query root zero"

def WireNativeABoxSeed.decode (wire : WireNativeABoxSeed) :
    Except String DecodedNativeABoxSeed := do
  let abox ← wire.abox.decode
  let nodeZero ← requireNodeZero wire.node_count
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count abox.concepts.length abox.roles.length)
  let decodedRoots ← wire.roots.mapM
    (checkedFin "native ABox root" wire.node_count)
  if hrootLength : decodedRoots.length = abox.individuals.length then
    if hrootNodup : decodedRoots.Nodup then
      let roots : Fin abox.individuals.length → Fin wire.node_count :=
        fun index => decodedRoots.get (hrootLength.symm ▸ index)
      have hrootsInjective : Function.Injective roots := by
        intro left right hequal
        have hindices := hrootNodup.get_inj_iff.mp hequal
        have hcast := congrArg (Fin.cast hrootLength) hindices
        simpa only [finCast_transport_back] using hcast
      let state ← wire.state.decode wire.node_count abox.concepts.length
        abox.roles.length wire.variable_count ontology
      if hvalid : state.base.equalityClosureValidB = true then
        if hapart : state.apartSeparatedB = true then
          if hseeded : abox.seededInB state roots = true then
            return {
              abox
              nodeCount := wire.node_count
              variableCount := wire.variable_count
              node_nonzero := Nat.ne_of_gt (Nat.zero_lt_of_lt nodeZero.isLt)
              roots
              roots_injective := hrootsInjective
              ontology
              state
              seeded := (abox.seededInB_eq_true_iff state roots).1 hseeded
              apart_check := hapart
              apart_separated := state.apartSeparatedB_sound hvalid hapart
            }
          else throw "finite HT state omits a native ABox seed fact"
        else throw "finite HT state merges an explicitly different individual"
      else throw "finite HT state has invalid equality representatives"
    else throw "native ABox roots must be pairwise distinct"
  else throw s!"native ABox root map has {decodedRoots.length} entries, expected {abox.individuals.length}"

def WireNativeABoxSeed.check (wire : WireNativeABoxSeed) : Except String Bool := do
  let _ ← wire.decode
  return true

/-- Exact initial state used as the root of an ABox-aware equality refutation.
Terminal SAT states use `DecodedNativeABoxSeed` instead because they may contain
arbitrarily many soundly derived facts. -/
structure DecodedNativeABoxInitial where
  seed : DecodedNativeABoxSeed
  exact_initial : seed.abox.abox.ExactEqSeed seed.state.base.state seed.roots

def WireNativeABoxSeed.decodeInitial (wire : WireNativeABoxSeed) :
    Except String DecodedNativeABoxInitial := do
  let expectedRoots := (List.range wire.abox.individuals.length).map (· + 1)
  unless wire.roots == expectedRoots do
    throw "native ABox refutation roots must be ordered nodes 1 through N"
  let seed ← wire.decode
  if hexact : seed.abox.exactEqSeedB seed.state.base seed.roots = true then
    return {
      seed
      exact_initial := seed.abox.exactEqSeedB_sound seed.state.base
        seed.roots hexact
    }
  else throw "finite HT refutation root is not the exact native ABox seed"

def WireNativeABoxSeed.checkInitial (wire : WireNativeABoxSeed) :
    Except String Bool := do
  let _ ← wire.decodeInitial
  return true

theorem DecodedNativeABoxInitial.initializes (decoded : DecodedNativeABoxInitial) :
    decoded.seed.abox.abox.InitializesEqState decoded.seed.state.base.state :=
  decoded.exact_initial.initializes decoded.seed.abox.abox decoded.seed.state.base.state
    decoded.seed.roots decoded.seed.roots_injective

/-- Untrusted exact initial state plus a complete finite equality refutation. -/
structure WireNativeABoxRefutation where
  initial : WireNativeABoxSeed
  tree : WireEqRefutationTree
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxRefutation where
  initial : DecodedNativeABoxInitial
  tree : FiniteEqRefutationTree initial.seed.nodeCount
    initial.seed.abox.concepts.length initial.seed.abox.roles.length
    initial.seed.variableCount
  checked : tree.check initial.seed.state.base = true

def WireNativeABoxRefutation.decode (wire : WireNativeABoxRefutation) :
    Except String DecodedNativeABoxRefutation := do
  let initial ← wire.initial.decodeInitial
  let tree ← wire.tree.decode initial.seed.nodeCount
    initial.seed.abox.concepts.length initial.seed.abox.roles.length
    initial.seed.variableCount initial.seed.ontology
  if hcheck : tree.check initial.seed.state.base = true then
    return { initial, tree, checked := hcheck }
  else throw "native ABox equality refutation did not close"

def WireNativeABoxRefutation.check (wire : WireNativeABoxRefutation) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedNativeABoxRefutation.unsatisfiable
    (decoded : DecodedNativeABoxRefutation) :
    ¬decoded.initial.seed.abox.abox.SatisfiableWith
      decoded.initial.seed.state.base.base.ontology :=
  decoded.tree.check_native_abox_unsatisfiable
    decoded.initial.seed.state.base decoded.initial.seed.abox.abox
    decoded.initial.initializes decoded.checked

theorem WireNativeABoxSeed.check_sound (wire : WireNativeABoxSeed)
    (decoded : DecodedNativeABoxSeed) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true) :
    decoded.abox.abox.SeededIn decoded.state.state decoded.roots :=
  decoded.seeded

theorem DecodedNativeABoxSeed.checkEqSat_native_satisfiable
    (decoded : DecodedNativeABoxSeed)
    (hcheck : decoded.state.base.checkEqSat = true)
    (hsingletons : decoded.abox.abox.ProxySingletons
      decoded.state.base.state.quotientCanonical
      (fun individual => Quotient.mk decoded.state.base.state.nodeSetoid
        (decoded.roots individual)))
    (hnegative : decoded.abox.abox.NegativeRoles
      decoded.state.base.state.quotientCanonical
      (fun individual => Quotient.mk decoded.state.base.state.nodeSetoid
        (decoded.roots individual))) :
    decoded.abox.abox.SatisfiableWith decoded.state.base.base.ontology := by
  letI : Nonempty (Fin decoded.nodeCount) :=
    ⟨⟨0, Nat.pos_of_ne_zero decoded.node_nonzero⟩⟩
  exact decoded.state.checkEqSat_native_satisfiable decoded.abox.abox
    decoded.roots decoded.seeded hcheck decoded.apart_check hsingletons hnegative

theorem DecodedNativeABox.models_iff_seed
    (decoded : DecodedNativeABox)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain) :
    decoded.abox.models I value ↔
      (nativeABoxSeed decoded.abox).RealizedBy I value ∧
        decoded.abox.ProxySingletons I value ∧ decoded.abox.NegativeRoles I value := by
  exact (nativeABoxSeed_realized_iff decoded.abox I value).symm

theorem WireNativeABox.check_sound (wire : WireNativeABox)
    (decoded : DecodedNativeABox) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain) :
    decoded.abox.models I value ↔
      (nativeABoxSeed decoded.abox).RealizedBy I value ∧
        decoded.abox.ProxySingletons I value ∧ decoded.abox.NegativeRoles I value := by
  exact decoded.models_iff_seed I value

section Tests

private def validExample : WireNativeABox where
  complete := true
  concepts := ["a", "b", "A"]
  roles := ["r"]
  nominals := [0, 1]
  individuals := [
    { proxies := [0], assertions := [2] },
    { proxies := [1], assertions := [] }
  ]
  different := [(0, 1)]
  role_assertions := [[0, 0, 1]]
  negative_role_assertions := [[0, 1, 0]]

example : validExample.check = .ok true := by native_decide

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected ({ validExample with complete := false }).check = true := by native_decide
example : rejected ({ validExample with nominals := [0] }).check = true := by native_decide
example : rejected ({ validExample with
    individuals := [{ proxies := [], assertions := [] }] }).check = true := by native_decide
example : rejected ({ validExample with
    individuals := [
      { proxies := [0], assertions := [] },
      { proxies := [0], assertions := [] }
    ] }).check = true := by native_decide
example : rejected ({ validExample with different := [(0, 2)] }).check = true := by native_decide
example : rejected ({ validExample with role_assertions := [[1, 0, 1]] }).check = true := by native_decide
example : rejected ({ validExample with role_assertions := [[0, 1]] }).check = true := by native_decide

private def validSeedExample : WireNativeABoxSeed where
  abox := validExample
  node_count := 3
  variable_count := 2
  roots := [1, 2]
  ontology := []
  state := {
    base := {
      labels := [
        { node := 1, literal := { concept := 0, neg := false } },
        { node := 1, literal := { concept := 2, neg := false } },
        { node := 2, literal := { concept := 1, neg := false } }
      ]
      edges := [{ role := 0, source := 1, target := 2 }]
      obligations := []
      equalities := []
      representatives := [0, 1, 2]
      representative_paths := [[], [], []]
    }
    apart := [{ left := 1, right := 2 }]
  }

example : validSeedExample.check = .ok true := by native_decide
example : validSeedExample.checkInitial = .ok true := by native_decide
example : rejected ({ validSeedExample with roots := [0] }).check = true := by native_decide
example : rejected ({ validSeedExample with roots := [1, 1] }).check = true := by native_decide
example : rejected ({ validSeedExample with state :=
    { validSeedExample.state with base :=
      { validSeedExample.state.base with labels :=
        validSeedExample.state.base.labels.drop 1 } } }).check = true := by native_decide
example : rejected ({ validSeedExample with state :=
    { validSeedExample.state with base :=
      { validSeedExample.state.base with
        equalities := [{ left := 1, right := 2 }]
        representatives := [0, 1, 1]
        representative_paths := [[], [], [1]] } } }).check = true := by native_decide
example : rejected ({ validSeedExample with state :=
    { validSeedExample.state with base :=
      { validSeedExample.state.base with labels :=
        validSeedExample.state.base.labels ++
          [({ node := 2, literal := { concept := 2, neg := false } } : WireLabel)] } } }).checkInitial = true := by
  native_decide

private def validRefutationExample : WireNativeABoxRefutation where
  initial := { validSeedExample with ontology := [
    { body := [.concept { concept := 2, neg := false } 0], head := [] }
  ] }
  tree := .branch 0 [1, 0] []

example : validRefutationExample.check = .ok true := by native_decide
example : rejected ({ validRefutationExample with tree := .clash }).check = true := by
  native_decide

#print axioms DecodedNativeABox.models_iff_seed
#print axioms DecodedNativeABox.models_negativeRoleClauses_iff
#print axioms DecodedNativeABox.models_append_negativeRoleClauses_iff
#print axioms DecodedNativeABox.seededInB_eq_true_iff
#print axioms WireNativeABox.check_sound
#print axioms WireNativeABoxSeed.check_sound
#print axioms DecodedNativeABoxSeed.checkEqSat_native_satisfiable
#print axioms DecodedNativeABoxInitial.initializes
#print axioms DecodedNativeABoxRefutation.unsatisfiable

end Tests

end ContextCalculus.Hypertableau
