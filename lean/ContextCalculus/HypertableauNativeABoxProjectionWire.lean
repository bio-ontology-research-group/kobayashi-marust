import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauDirectProjectionWire
import ContextCalculus.HypertableauMixedProjectionWire
import ContextCalculus.HypertableauBundleProjectionWire
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

def DecodedNativeABox.negativeRoleClausesAt (decoded : DecodedNativeABox)
    (variableCount : Nat) (hvariables : 2 ≤ variableCount) :
    List (Clause (Fin variableCount)
      (Fin decoded.concepts.length) (Fin decoded.roles.length)) :=
  decoded.negativeRoleAssertions.map fun assertion =>
    negativeRoleAssertionClause
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      assertion.1 (Fin.castLE hvariables 0) (Fin.castLE hvariables 1)

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

theorem DecodedNativeABox.models_negativeRoleClausesAt_iff
    (decoded : DecodedNativeABox)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain)
    (hsingletons : decoded.abox.ProxySingletons I value)
    (hvariables : 2 ≤ variableCount) :
    I.models (decoded.negativeRoleClausesAt variableCount hvariables) ↔
      decoded.abox.NegativeRoles I value := by
  constructor
  · intro hmodels assertion hassertion
    have hclause := hmodels
      (negativeRoleAssertionClause
        (decoded.primaryProxy assertion.2.1)
        (decoded.primaryProxy assertion.2.2)
        assertion.1 (Fin.castLE hvariables 0) (Fin.castLE hvariables 1))
      (List.mem_map.mpr ⟨assertion, hassertion, rfl⟩)
    exact (models_negativeRoleAssertionClause_iff decoded.abox I value hsingletons
      assertion.2.1 assertion.2.2
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      (decoded.primaryProxy_mem assertion.2.1)
      (decoded.primaryProxy_mem assertion.2.2)
      assertion.1 (Fin.castLE hvariables 0) (Fin.castLE hvariables 1)
      (by simp)).1 hclause
  · intro hnegative clause hclause
    rcases List.mem_map.mp hclause with ⟨assertion, hassertion, rfl⟩
    exact (models_negativeRoleAssertionClause_iff decoded.abox I value hsingletons
      assertion.2.1 assertion.2.2
      (decoded.primaryProxy assertion.2.1)
      (decoded.primaryProxy assertion.2.2)
      (decoded.primaryProxy_mem assertion.2.1)
      (decoded.primaryProxy_mem assertion.2.2)
      assertion.1 (Fin.castLE hvariables 0) (Fin.castLE hvariables 1)
      (by simp)).2 (hnegative assertion hassertion)

theorem DecodedNativeABox.models_append_negativeRoleClausesAt_iff
    (decoded : DecodedNativeABox)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (value : Fin decoded.individuals.length → Domain)
    (hsingletons : decoded.abox.ProxySingletons I value)
    (hvariables : 2 ≤ variableCount)
    (ontology : List (Clause (Fin variableCount)
      (Fin decoded.concepts.length) (Fin decoded.roles.length))) :
    I.models (ontology ++ decoded.negativeRoleClausesAt variableCount hvariables) ↔
      I.models ontology ∧ decoded.abox.NegativeRoles I value := by
  constructor
  · intro hmodels
    refine ⟨?_, (decoded.models_negativeRoleClausesAt_iff I value hsingletons
      hvariables).1 ?_⟩
    · intro clause hclause
      exact hmodels clause (List.mem_append_left _ hclause)
    · intro clause hclause
      exact hmodels clause (List.mem_append_right _ hclause)
  · rintro ⟨hontology, hnegative⟩ clause hclause
    rcases List.mem_append.mp hclause with hsource | hguard
    · exact hontology clause hsource
    · exact (decoded.models_negativeRoleClausesAt_iff I value hsingletons
        hvariables).2 hnegative clause hguard

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

/-- One checked document connecting direct source clauses, native ABox
semantics, the exact normalized initial state, and the closed equality search. -/
structure WireDirectNativeABoxRefutation where
  source : List WireDirectSourceClause
  refutation : WireNativeABoxRefutation
deriving FromJson, ToJson, Repr

structure DecodedDirectNativeABoxRefutation where
  refutation : DecodedNativeABoxRefutation
  variable_ge_two : 2 ≤ refutation.initial.seed.variableCount
  source : List (Clause (Fin refutation.initial.seed.variableCount)
    (Fin refutation.initial.seed.abox.concepts.length)
    (Fin refutation.initial.seed.abox.roles.length))
  exact_projection : source ++ refutation.initial.seed.abox.negativeRoleClausesAt
      refutation.initial.seed.variableCount variable_ge_two =
    refutation.initial.seed.state.base.base.ontology

structure AtLeastTwoVariables (variableCount : Nat) where
  second : Fin variableCount
  proof : 2 ≤ variableCount

def requireAtLeastTwoVariables (variableCount : Nat) :
    Except String (AtLeastTwoVariables variableCount) :=
  if hvariables : 2 ≤ variableCount then
    .ok ⟨⟨1, Nat.lt_of_lt_of_le (by decide) hvariables⟩, hvariables⟩
  else .error "native ABox refutation requires at least two clause variables"

def WireDirectNativeABoxRefutation.decode
    (wire : WireDirectNativeABoxRefutation) :
    Except String DecodedDirectNativeABoxRefutation := do
  let refutation ← wire.refutation.decode
  let variableWitness ← requireAtLeastTwoVariables refutation.initial.seed.variableCount
  let hvariables := variableWitness.proof
  let source ← wire.source.mapM (WireDirectSourceClause.decode
    refutation.initial.seed.variableCount
    refutation.initial.seed.abox.concepts refutation.initial.seed.abox.roles)
  if hequal : source ++ refutation.initial.seed.abox.negativeRoleClausesAt
      refutation.initial.seed.variableCount hvariables =
      refutation.initial.seed.state.base.base.ontology then
    return { refutation, variable_ge_two := hvariables, source, exact_projection := hequal }
  else throw "direct source conversion differs from the native ABox refutation ontology"

def WireDirectNativeABoxRefutation.check
    (wire : WireDirectNativeABoxRefutation) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectNativeABoxRefutation.source_unsatisfiable
    (decoded : DecodedDirectNativeABoxRefutation) :
    ¬decoded.refutation.initial.seed.abox.abox.SatisfiableWith decoded.source := by
  rintro ⟨Domain, I, value, hdomain, hsource, habox⟩
  apply decoded.refutation.unsatisfiable
  refine ⟨Domain, I, value, hdomain, ?_, habox⟩
  rw [← decoded.exact_projection]
  exact (decoded.refutation.initial.seed.abox.models_append_negativeRoleClausesAt_iff
    I value habox.1 decoded.variable_ge_two decoded.source).2
      ⟨hsource, habox.2.2.2.2⟩

/-- Mixed direct/Skolem-pair source composed with the same exact native-ABox
decision boundary. The target ontology is reconstructed inside Lean. -/
structure WireMixedNativeABoxRefutation where
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  refutation : WireNativeABoxRefutation
deriving FromJson, ToJson, Repr

structure DecodedMixedNativeABoxRefutation where
  refutation : DecodedNativeABoxRefutation
  variable_ge_two : 2 ≤ refutation.initial.seed.variableCount
  functions : List String
  direct : List (Clause (Fin refutation.initial.seed.variableCount)
    (Fin refutation.initial.seed.abox.concepts.length)
    (Fin refutation.initial.seed.abox.roles.length))
  pairs : List (SkolemPairSpec (Fin refutation.initial.seed.variableCount)
    (Fin refutation.initial.seed.abox.concepts.length)
    (Fin refutation.initial.seed.abox.roles.length) (Fin functions.length))
  unique_functions : (skolemPairFunctions pairs).Nodup
  exact_projection :
    (skolemProjectionOntology direct pairs ++
      refutation.initial.seed.abox.negativeRoleClausesAt
        refutation.initial.seed.variableCount variable_ge_two).toFinset =
      refutation.initial.seed.state.base.base.ontology.toFinset

def WireMixedNativeABoxRefutation.decode
    (wire : WireMixedNativeABoxRefutation) :
    Except String DecodedMixedNativeABoxRefutation := do
  let refutation ← wire.refutation.decode
  let variableWitness ← requireAtLeastTwoVariables refutation.initial.seed.variableCount
  let hvariables := variableWitness.proof
  if _hfunctions : wire.functions.Nodup then
    let direct ← wire.direct.mapM (WireDirectSourceClause.decode
      refutation.initial.seed.variableCount refutation.initial.seed.abox.concepts
      refutation.initial.seed.abox.roles)
    let pairs ← wire.pairs.mapM (WireSkolemPair.decode
      refutation.initial.seed.variableCount refutation.initial.seed.abox.concepts
      refutation.initial.seed.abox.roles wire.functions)
    if hunique : (skolemPairFunctions pairs).Nodup then
      if hequal : (skolemProjectionOntology direct pairs ++
          refutation.initial.seed.abox.negativeRoleClausesAt
            refutation.initial.seed.variableCount hvariables).toFinset =
          refutation.initial.seed.state.base.base.ontology.toFinset then
        return {
          refutation
          variable_ge_two := hvariables
          functions := wire.functions
          direct
          pairs
          unique_functions := hunique
          exact_projection := hequal
        }
      else throw "mixed source conversion differs from the native ABox refutation ontology"
    else throw "mixed native ABox projection reuses a Skolem function"
  else throw "mixed native ABox function-name table contains duplicates"

def WireMixedNativeABoxRefutation.check
    (wire : WireMixedNativeABoxRefutation) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedNativeABoxRefutation.source_unsatisfiable
    (decoded : DecodedMixedNativeABoxRefutation) :
    ¬∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.refutation.initial.seed.abox.concepts.length)
          (Fin decoded.refutation.initial.seed.abox.roles.length))
        (value : Fin decoded.refutation.initial.seed.abox.individuals.length → Domain),
      Nonempty Domain ∧ decoded.refutation.initial.seed.abox.abox.models I value ∧
      ∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
        I.models decoded.direct ∧ ModelsSkolemPairs I functions decoded.pairs := by
  rintro ⟨Domain, I, value, hdomain, habox, functions, hdirect, hpairs⟩
  letI : Nonempty Domain := hdomain
  let base : SkolemInterp Domain (Fin decoded.functions.length) :=
    ⟨fun _ _ => Classical.choice hdomain⟩
  have hprojected : I.models (skolemProjectionOntology decoded.direct decoded.pairs) :=
    (mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
      decoded.unique_functions).1 ⟨functions, hdirect, hpairs⟩
  have happended : I.models (skolemProjectionOntology decoded.direct decoded.pairs ++
      decoded.refutation.initial.seed.abox.negativeRoleClausesAt
        decoded.refutation.initial.seed.variableCount decoded.variable_ge_two) :=
    (decoded.refutation.initial.seed.abox.models_append_negativeRoleClausesAt_iff
      I value habox.1 decoded.variable_ge_two
      (skolemProjectionOntology decoded.direct decoded.pairs)).2
        ⟨hprojected, habox.2.2.2.2⟩
  have htarget : I.models decoded.refutation.initial.seed.state.base.base.ontology :=
    (models_iff_of_toFinset_eq I _ _ decoded.exact_projection).1 happended
  exact decoded.refutation.unsatisfiable
    ⟨Domain, I, value, hdomain, htarget, habox⟩

structure WireBundleNativeABoxRefutation where
  source_concepts : List String
  functions : List String
  direct : List WireDirectSourceClause
  bundles : List WireSkolemBundle
  domain_extras : List WireBundleDomainExtra
  abox_source_map : List Nat
  refutation : WireNativeABoxRefutation
deriving FromJson, ToJson, Repr

def decodeConceptMap (kind : String) (sourceCount targetCount : Nat)
    (values : List Nat) : Except String (Fin targetCount → Fin sourceCount) := do
  let decoded ← values.mapM (checkedFin kind sourceCount)
  if hlength : decoded.length = targetCount then
    return fun index => decoded.get (hlength.symm ▸ index)
  else throw s!"{kind} has {decoded.length} entries, expected {targetCount}"

def NativeABox.conceptsEmbeddedB
    (abox : NativeABox (Fin individualCount) TargetConcept Role)
    [DecidableEq TargetConcept]
    (sourceOf : TargetConcept → SourceConcept)
    (embedding : SourceConcept → TargetConcept) : Bool :=
  (List.finRange individualCount).all fun individual =>
    (abox.proxies individual ++ abox.assertions individual).all fun concept =>
      decide (embedding (sourceOf concept) = concept)

theorem NativeABox.conceptsEmbeddedB_sound
    (abox : NativeABox (Fin individualCount) TargetConcept Role)
    [DecidableEq TargetConcept]
    (sourceOf : TargetConcept → SourceConcept)
    (embedding : SourceConcept → TargetConcept)
    (hcheck : abox.conceptsEmbeddedB sourceOf embedding = true) :
    ∀ individual concept,
      concept ∈ abox.proxies individual ++ abox.assertions individual →
      embedding (sourceOf concept) = concept := by
  simp only [NativeABox.conceptsEmbeddedB, List.all_eq_true,
    List.mem_finRange, decide_eq_true_eq] at hcheck
  intro individual concept hconcept
  exact hcheck individual trivial concept hconcept

structure DecodedBundleNativeABoxRefutation where
  refutation : DecodedNativeABoxRefutation
  variable_ge_two : 2 ≤ refutation.initial.seed.variableCount
  sourceConcepts : List String
  functions : List String
  sourceTargets : Fin sourceConcepts.length →
    Fin refutation.initial.seed.abox.concepts.length
  direct : List (Clause (Fin refutation.initial.seed.variableCount)
    (Fin sourceConcepts.length) (Fin refutation.initial.seed.abox.roles.length))
  bundles : List (DecodedWireBundle (Fin refutation.initial.seed.variableCount)
    (Fin sourceConcepts.length) (Fin refutation.initial.seed.abox.roles.length)
    (Fin functions.length) (Fin refutation.initial.seed.abox.concepts.length))
  domainExtras : List (IndexedBundleDomainSpec (Fin sourceConcepts.length)
    (Fin refutation.initial.seed.abox.roles.length) bundles.length)
  nonemptyBundles : bundles ≠ []
  uniqueFunctions :
    (skolemPairFunctions (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup
  embeddingInjective : Function.Injective
    (bundleConceptEmbedding sourceTargets bundles)
  rboxSource : Fin refutation.initial.seed.variableCount
  rboxTarget : Fin refutation.initial.seed.variableCount
  rboxDistinct : rboxSource ≠ rboxTarget
  pathPremises : ∀ spec ∈ domainExtras, ∀ clause ∈
    roleInclusionPathClauses
      (decodedBundleSpecs bundles spec.bundle).role spec.path rboxSource rboxTarget,
    clause ∈ direct
  domainPremises : ∀ spec ∈ domainExtras,
    roleDomainClause (spec.superRole (decodedBundleSpecs bundles)) spec.domain
      rboxSource rboxTarget ∈ direct
  sourceOf : Fin refutation.initial.seed.abox.concepts.length →
    Fin sourceConcepts.length
  abox_embedded : ∀ individual concept,
    concept ∈ refutation.initial.seed.abox.abox.proxies individual ++
      refutation.initial.seed.abox.abox.assertions individual →
    bundleConceptEmbedding sourceTargets bundles
      (.inr (sourceOf concept)) = concept
  exact_ontology :
    (renameOntology (bundleConceptEmbedding sourceTargets bundles)
      (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
        indexedBundleDomainOntology (decodedBundleSpecs bundles) domainExtras) ++
      refutation.initial.seed.abox.negativeRoleClausesAt
        refutation.initial.seed.variableCount variable_ge_two).toFinset =
      refutation.initial.seed.state.base.base.ontology.toFinset

def WireBundleNativeABoxRefutation.decode
    (wire : WireBundleNativeABoxRefutation) :
    Except String DecodedBundleNativeABoxRefutation := do
  let refutation ← wire.refutation.decode
  let variableWitness ← requireAtLeastTwoVariables refutation.initial.seed.variableCount
  let hvariables := variableWitness.proof
  if _hsourceConcepts : wire.source_concepts.Nodup then
    if _hfunctions : wire.functions.Nodup then
      let sourceTargets ← checkedNameEmbedding "source concept in target"
        wire.source_concepts refutation.initial.seed.abox.concepts
      let direct ← wire.direct.mapM (WireDirectSourceClause.decode
        refutation.initial.seed.variableCount wire.source_concepts
        refutation.initial.seed.abox.roles)
      let bundles ← wire.bundles.mapM (WireSkolemBundle.decode
        refutation.initial.seed.variableCount wire.source_concepts
        refutation.initial.seed.abox.concepts refutation.initial.seed.abox.roles
        wire.functions)
      if hnonempty : bundles ≠ [] then
        let rboxSource : Fin refutation.initial.seed.variableCount :=
          ⟨0, lt_of_lt_of_le Nat.zero_lt_two hvariables⟩
        let rboxTarget : Fin refutation.initial.seed.variableCount := ⟨1, hvariables⟩
        have hrboxDistinct : rboxSource ≠ rboxTarget := by
          intro hequal
          have hval := congrArg Fin.val hequal
          simp [rboxSource, rboxTarget] at hval
        let domainExtras ← wire.domain_extras.mapM
          (WireBundleDomainExtra.decode wire.source_concepts
            refutation.initial.seed.abox.roles bundles.length)
        if hunique : (skolemPairFunctions
            (indexedBundlePairs (decodedBundleSpecs bundles))).Nodup then
          if hinjective : (bundleEmbeddingValues sourceTargets bundles).Nodup then
            if hpaths : ∀ spec ∈ domainExtras, ∀ clause ∈
                roleInclusionPathClauses
                  (decodedBundleSpecs bundles spec.bundle).role spec.path
                    rboxSource rboxTarget,
                clause ∈ direct then
              if hdomains : ∀ spec ∈ domainExtras,
                  roleDomainClause
                    (spec.superRole (decodedBundleSpecs bundles)) spec.domain
                      rboxSource rboxTarget ∈ direct then
                let sourceOf ← decodeConceptMap "native ABox source concept"
                  wire.source_concepts.length
                  refutation.initial.seed.abox.concepts.length wire.abox_source_map
                if hembedded : refutation.initial.seed.abox.abox.conceptsEmbeddedB
                    sourceOf (fun source =>
                      bundleConceptEmbedding sourceTargets bundles (.inr source)) = true then
                  if hequal :
                      (renameOntology (bundleConceptEmbedding sourceTargets bundles)
                        (indexedBundleOntology direct (decodedBundleSpecs bundles) ++
                          indexedBundleDomainOntology
                            (decodedBundleSpecs bundles) domainExtras) ++
                        refutation.initial.seed.abox.negativeRoleClausesAt
                          refutation.initial.seed.variableCount hvariables).toFinset =
                        refutation.initial.seed.state.base.base.ontology.toFinset then
                    return {
                      refutation
                      variable_ge_two := hvariables
                      sourceConcepts := wire.source_concepts
                      functions := wire.functions
                      sourceTargets
                      direct
                      bundles
                      domainExtras
                      nonemptyBundles := hnonempty
                      uniqueFunctions := hunique
                      embeddingInjective :=
                        bundleConceptEmbedding_injective_of_nodup
                          sourceTargets bundles hinjective
                      rboxSource
                      rboxTarget
                      rboxDistinct := hrboxDistinct
                      pathPremises := hpaths
                      domainPremises := hdomains
                      sourceOf
                      abox_embedded :=
                        refutation.initial.seed.abox.abox.conceptsEmbeddedB_sound
                          sourceOf (fun source =>
                            bundleConceptEmbedding sourceTargets bundles (.inr source))
                          hembedded
                      exact_ontology := hequal
                    }
                  else throw "bundle source conversion differs from the native ABox refutation ontology"
                else throw "native ABox concept is not an embedded bundle source concept"
              else throw "bundle domain premise is absent from the source ontology"
            else throw "bundle role-inclusion path is absent from the source ontology"
          else throw "bundle definers collide with each other or source concepts"
        else throw "bundle native ABox projection reuses a Skolem function"
      else throw "bundle native ABox projection contains no bundles"
    else throw "bundle native ABox function-name table contains duplicates"
  else throw "bundle native ABox source concept-name table contains duplicates"

def WireBundleNativeABoxRefutation.check
    (wire : WireBundleNativeABoxRefutation) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleNativeABoxRefutation.source_unsatisfiable
    (decoded : DecodedBundleNativeABoxRefutation) :
    ¬∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.sourceConcepts.length)
          (Fin decoded.refutation.initial.seed.abox.roles.length))
        (functions : SkolemInterp Domain (Fin decoded.functions.length))
        (value : Fin decoded.refutation.initial.seed.abox.individuals.length → Domain),
      Nonempty Domain ∧ I.models decoded.direct ∧
      ModelsBundles I functions (decodedBundleSpecs decoded.bundles) ∧
      (decoded.refutation.initial.seed.abox.abox.mapConcepts decoded.sourceOf).models
        I value := by
  rintro ⟨Domain, I, functions, value, hdomain, hdirect, hbundles, habox⟩
  let targetCore := renameOntology
    (bundleConceptEmbedding decoded.sourceTargets decoded.bundles)
    (indexedBundleOntology decoded.direct (decodedBundleSpecs decoded.bundles) ++
      indexedBundleDomainOntology (decodedBundleSpecs decoded.bundles)
        decoded.domainExtras)
  let projection : DecodedBundleProjection := {
    variableCount := decoded.refutation.initial.seed.variableCount
    sourceConcepts := decoded.sourceConcepts
    concepts := decoded.refutation.initial.seed.abox.concepts
    roles := decoded.refutation.initial.seed.abox.roles
    functions := decoded.functions
    sourceTargets := decoded.sourceTargets
    direct := decoded.direct
    bundles := decoded.bundles
    domainExtras := decoded.domainExtras
    target := targetCore
    nonemptyBundles := decoded.nonemptyBundles
    uniqueFunctions := decoded.uniqueFunctions
    embeddingInjective := decoded.embeddingInjective
    rboxSource := decoded.rboxSource
    rboxTarget := decoded.rboxTarget
    rboxDistinct := decoded.rboxDistinct
    pathPremises := decoded.pathPremises
    domainPremises := decoded.domainPremises
    exactProjection := rfl
  }
  obtain ⟨J, hcore, htargetABox⟩ :=
    projection.source_model_to_target_model_preserving_nativeABox
      decoded.refutation.initial.seed.abox.abox decoded.sourceOf
      decoded.abox_embedded I functions value hdirect hbundles habox
  have happended : J.models (targetCore ++
      decoded.refutation.initial.seed.abox.negativeRoleClausesAt
        decoded.refutation.initial.seed.variableCount decoded.variable_ge_two) :=
    (decoded.refutation.initial.seed.abox.models_append_negativeRoleClausesAt_iff
      J value htargetABox.1 decoded.variable_ge_two targetCore).2
        ⟨hcore, htargetABox.2.2.2.2⟩
  have htarget : J.models decoded.refutation.initial.seed.state.base.base.ontology :=
    (models_iff_of_toFinset_eq J _ _ decoded.exact_ontology).1 happended
  exact decoded.refutation.unsatisfiable
    ⟨Domain, J, value, hdomain, htarget, htargetABox⟩

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

private def validDirectNativeRefutation : WireDirectNativeABoxRefutation where
  source := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := []
  }]
  refutation := { validRefutationExample with initial :=
    { validRefutationExample.initial with abox :=
      { validRefutationExample.initial.abox with
        concepts := ["a", "b", "A"]
        negative_role_assertions := [] } } }

example : validDirectNativeRefutation.check = .ok true := by native_decide
example : rejected ({ validDirectNativeRefutation with source := [] }).check = true := by
  native_decide

private def validMixedNativeRefutation : WireMixedNativeABoxRefutation where
  functions := ["f"]
  direct := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := []
  }]
  pairs := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    source := "x"
    function := "f"
    role := "r"
    filler := "C"
    neg := false
  }]
  refutation := { validRefutationExample with initial :=
    { validRefutationExample.initial with
      abox := { validRefutationExample.initial.abox with
        concepts := ["a", "b", "A", "C"]
        negative_role_assertions := [] }
      ontology := [
        { body := [.concept { concept := 2, neg := false } 0], head := [] },
        { body := [.concept { concept := 2, neg := false } 0]
          head := [.exists_ 0 { concept := 3, neg := false } 0] }
      ] } }

example : validMixedNativeRefutation.check = .ok true := by native_decide
example : rejected ({ validMixedNativeRefutation with pairs := [] }).check = true := by
  native_decide

private def validBundleNativeRefutation : WireBundleNativeABoxRefutation where
  source_concepts := ["a", "b", "A", "C"]
  functions := ["f"]
  direct := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := []
  }]
  bundles := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    source := "x"
    function := "f"
    role := "r"
    fillers := [⟨"C", false⟩]
    definer := "D"
  }]
  domain_extras := []
  abox_source_map := [0, 1, 2, 0, 3]
  refutation := { validRefutationExample with initial :=
    { validRefutationExample.initial with
      abox := { validRefutationExample.initial.abox with
        concepts := ["a", "b", "A", "D", "C"]
        negative_role_assertions := [] }
      ontology := [
        { body := [.concept { concept := 2, neg := false } 0], head := [] },
        { body := [.concept { concept := 2, neg := false } 0]
          head := [.exists_ 0 { concept := 3, neg := false } 0] },
        { body := [.concept { concept := 3, neg := false } 0]
          head := [.concept { concept := 4, neg := false } 0] }
      ] } }

example : validBundleNativeRefutation.check = .ok true := by native_decide
example : rejected ({ validBundleNativeRefutation with
    abox_source_map := [0, 1, 3, 0, 3] }).check = true := by native_decide

#print axioms DecodedNativeABox.models_iff_seed
#print axioms DecodedNativeABox.models_negativeRoleClauses_iff
#print axioms DecodedNativeABox.models_append_negativeRoleClauses_iff
#print axioms DecodedNativeABox.seededInB_eq_true_iff
#print axioms WireNativeABox.check_sound
#print axioms WireNativeABoxSeed.check_sound
#print axioms DecodedNativeABoxSeed.checkEqSat_native_satisfiable
#print axioms DecodedNativeABoxInitial.initializes
#print axioms DecodedNativeABoxRefutation.unsatisfiable
#print axioms DecodedDirectNativeABoxRefutation.source_unsatisfiable
#print axioms DecodedMixedNativeABoxRefutation.source_unsatisfiable
#print axioms DecodedBundleNativeABoxRefutation.source_unsatisfiable

end Tests

end ContextCalculus.Hypertableau
