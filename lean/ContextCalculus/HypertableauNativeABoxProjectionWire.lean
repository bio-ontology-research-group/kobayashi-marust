import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauWire

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

#print axioms DecodedNativeABox.models_iff_seed
#print axioms DecodedNativeABox.models_negativeRoleClauses_iff
#print axioms DecodedNativeABox.models_append_negativeRoleClauses_iff
#print axioms WireNativeABox.check_sound

end Tests

end ContextCalculus.Hypertableau
