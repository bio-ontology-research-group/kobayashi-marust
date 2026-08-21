import ContextCalculus.HypertableauNativeABoxProjectionWire
import ContextCalculus.HypertableauCardinalityWire

/-!
# Executable native-ABox quotient-model side conditions

The native-ABox SAT theorem requires singleton nominal proxies and absence of
every negative role assertion in the accepted quotient interpretation.  This
module gives those two semantic obligations finite Boolean checks over the
decoded equality state.
-/

namespace ContextCalculus.Hypertableau

open Lean

def DecodedNativeABoxSeed.proxySingletonsB
    (decoded : DecodedNativeABoxSeed) : Bool :=
  (List.finRange decoded.abox.individuals.length).all fun individual =>
    (decoded.abox.abox.proxies individual).all fun proxy =>
      (List.finRange decoded.nodeCount).all fun node =>
        decoded.state.base.quotientPositiveB node proxy ==
          decoded.state.base.closedRelatedB node (decoded.roots individual)

theorem DecodedNativeABoxSeed.proxySingletonsB_sound
    (decoded : DecodedNativeABoxSeed)
    (hvalid : decoded.state.base.equalityClosureValidB = true)
    (hcheck : decoded.proxySingletonsB = true) :
    decoded.abox.abox.ProxySingletons
      decoded.state.base.state.quotientCanonical
      (fun individual => Quotient.mk decoded.state.base.state.nodeSetoid
        (decoded.roots individual)) := by
  simp only [DecodedNativeABoxSeed.proxySingletonsB, List.all_eq_true,
    List.mem_finRange, true_implies, beq_iff_eq] at hcheck
  intro individual proxy hproxy candidate
  refine Quotient.inductionOn candidate fun node => ?_
  have hnode := hcheck individual proxy hproxy node
  rw [Bool.eq_iff_iff] at hnode
  rw [decoded.state.base.quotientPositiveB_eq_true hvalid node proxy,
    decoded.state.base.closedRelatedB_eq_true hvalid node
      (decoded.roots individual)] at hnode
  simpa only [Quotient.eq] using hnode

def DecodedNativeABoxSeed.negativeRolesB
    (decoded : DecodedNativeABoxSeed) : Bool :=
  decoded.abox.negativeRoleAssertions.all fun assertion =>
    !decoded.state.base.quotientRoleB assertion.1
      (decoded.roots assertion.2.1) (decoded.roots assertion.2.2)

theorem DecodedNativeABoxSeed.negativeRolesB_sound
    (decoded : DecodedNativeABoxSeed)
    (hvalid : decoded.state.base.equalityClosureValidB = true)
    (hcheck : decoded.negativeRolesB = true) :
    decoded.abox.abox.NegativeRoles
      decoded.state.base.state.quotientCanonical
      (fun individual => Quotient.mk decoded.state.base.state.nodeSetoid
        (decoded.roots individual)) := by
  simp only [DecodedNativeABoxSeed.negativeRolesB, List.all_eq_true] at hcheck
  intro assertion hassertion
  have hfalse := hcheck assertion hassertion
  intro hrole
  have htrue := (decoded.state.base.quotientRoleB_eq_true hvalid assertion.1
    (decoded.roots assertion.2.1) (decoded.roots assertion.2.2)).mpr hrole
  simp [htrue] at hfalse

/-- A finite equality quotient that retains the complete native ABox and passes
the two model-side checks omitted by the generic equality certificate. -/
structure WireNativeABoxSatCertificate where
  seed : WireNativeABoxSeed
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxSatCertificate where
  seed : DecodedNativeABoxSeed
  sat : seed.state.base.checkEqSat = true
  singleton_proxies : seed.proxySingletonsB = true
  negative_roles : seed.negativeRolesB = true

def WireNativeABoxSatCertificate.decode
    (wire : WireNativeABoxSatCertificate) :
    Except String DecodedNativeABoxSatCertificate := do
  let seed ← wire.seed.decode
  if hsat : seed.state.base.checkEqSat = true then
    if hsingletons : seed.proxySingletonsB = true then
      if hnegative : seed.negativeRolesB = true then
        return {
          seed
          sat := hsat
          singleton_proxies := hsingletons
          negative_roles := hnegative
        }
      else throw "native ABox quotient violates a negative role assertion"
    else throw "native ABox proxy is not singleton in the quotient model"
  else throw "native ABox quotient is not a saturated finite equality model"

def WireNativeABoxSatCertificate.check
    (wire : WireNativeABoxSatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedNativeABoxSatCertificate.satisfiable
    (decoded : DecodedNativeABoxSatCertificate) :
    decoded.seed.abox.abox.SatisfiableWith
      decoded.seed.state.base.base.ontology := by
  letI : Nonempty (Fin decoded.seed.nodeCount) :=
    ⟨⟨0, Nat.pos_of_ne_zero decoded.seed.node_nonzero⟩⟩
  exact decoded.seed.state.checkEqSat_native_satisfiable
    decoded.seed.abox.abox decoded.seed.roots decoded.seed.seeded decoded.sat
    decoded.seed.apart_check
    (decoded.seed.proxySingletonsB_sound
      (by
        have hparts := decoded.sat
        simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hparts
        exact hparts.1.1.1.1)
      decoded.singleton_proxies)
    (decoded.seed.negativeRolesB_sound
      (by
        have hparts := decoded.sat
        simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hparts
        exact hparts.1.1.1.1)
      decoded.negative_roles)

inductive WireNativeABoxDecisionEvidence where
  | sat (certificate : WireNativeABoxSatCertificate)
  | unsat (refutation : WireNativeABoxRefutation)
deriving FromJson, ToJson, Repr

structure WireNativeABoxDecisionCertificate where
  version : Nat
  evidence : WireNativeABoxDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedNativeABoxDecision where
  | sat (certificate : DecodedNativeABoxSatCertificate)
  | unsat (refutation : DecodedNativeABoxRefutation)

def WireNativeABoxDecisionCertificate.decode
    (wire : WireNativeABoxDecisionCertificate) :
    Except String DecodedNativeABoxDecision := do
  if wire.version != 1 then
    throw s!"unsupported native ABox decision certificate version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireNativeABoxDecisionCertificate.check
    (wire : WireNativeABoxDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedNativeABoxDecision.SemanticallyValid :
    DecodedNativeABoxDecision → Prop
  | .sat certificate => certificate.seed.abox.abox.SatisfiableWith
      certificate.seed.state.base.base.ontology
  | .unsat refutation => ¬refutation.initial.seed.abox.abox.SatisfiableWith
      refutation.initial.seed.state.base.base.ontology

theorem DecodedNativeABoxDecision.semantic_valid
    (decoded : DecodedNativeABoxDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.satisfiable
  | unsat refutation => exact refutation.unsatisfiable

/-! ## Native ABox with cardinality

The cardinality route must check all parts in one quotient interpretation.  In
particular, checking an ontology model, an ABox model, and cardinality models
separately would not establish that a single interpretation satisfies their
conjunction.  The certificate below deliberately shares one decoded seed.
-/

structure WireNativeABoxCardinalitySatCertificate where
  seed : WireNativeABoxSeed
  definitions : List WireCardinalityDef
  exact_maximums : List Nat := []
  exact_definitions : List Nat := []
deriving FromJson, ToJson, Repr

structure DecodedNativeABoxCardinalitySatCertificate where
  seed : DecodedNativeABoxSeed
  definitions : List
    (CardinalityDef (Fin seed.abox.concepts.length) (Fin seed.abox.roles.length))
  exactDefinitions : List
    (CardinalityDef (Fin seed.abox.concepts.length) (Fin seed.abox.roles.length))
  cardinality : seed.state.base.checkEqSatWithCardinality definitions = true
  exact : seed.state.base.checkCardinalityDefsExact exactDefinitions = true
  singleton_proxies : seed.proxySingletonsB = true
  negative_roles : seed.negativeRolesB = true

def WireNativeABoxCardinalitySatCertificate.decode
    (wire : WireNativeABoxCardinalitySatCertificate) :
    Except String DecodedNativeABoxCardinalitySatCertificate := do
  let seed ← wire.seed.decode
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode seed.abox.concepts.length seed.abox.roles.length)
  let exactMaximums ← wire.exact_maximums.mapM fun index => do
    match definitions[index]? with
    | none => throw s!"exact maximum definition index {index} is out of range"
    | some definition =>
        if definition.kind = CardinalityKind.maximum then
          pure definition
        else
          throw s!"exact maximum definition index {index} names a minimum definition"
  let exactDefinitions ← wire.exact_definitions.mapM fun index =>
    match definitions[index]? with
    | none => throw s!"exact cardinality definition index {index} is out of range"
    | some definition => pure definition
  let exactDefinitions := exactDefinitions ++ exactMaximums
  if hcardinality :
      seed.state.base.checkEqSatWithCardinality definitions = true then
    if hexact : seed.state.base.checkCardinalityDefsExact exactDefinitions = true then
      if hsingletons : seed.proxySingletonsB = true then
        if hnegative : seed.negativeRolesB = true then
          return {
            seed
            definitions
            exactDefinitions
            cardinality := hcardinality
            exact := hexact
            singleton_proxies := hsingletons
            negative_roles := hnegative
          }
        else throw "native ABox quotient violates a negative role assertion"
      else throw "native ABox proxy is not singleton in the quotient model"
    else throw "native ABox quotient violates an exact cardinality definition"
  else throw "native ABox quotient does not model its cardinality definitions"

def WireNativeABoxCardinalitySatCertificate.check
    (wire : WireNativeABoxCardinalitySatCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedNativeABoxCardinalitySatCertificate.canonical_model
    (decoded : DecodedNativeABoxCardinalitySatCertificate) :
    ∃ value : Fin decoded.seed.abox.individuals.length →
        decoded.seed.state.base.state.QuotientDomain,
      Nonempty decoded.seed.state.base.state.QuotientDomain ∧
      decoded.seed.state.base.state.quotientCanonical.models
        decoded.seed.state.base.base.ontology ∧
      decoded.seed.state.base.state.quotientCanonical.modelsCardinalityDefs
        decoded.definitions ∧
      decoded.seed.abox.abox.models
        decoded.seed.state.base.state.quotientCanonical value := by
  letI : Nonempty (Fin decoded.seed.nodeCount) :=
    ⟨⟨0, Nat.pos_of_ne_zero decoded.seed.node_nonzero⟩⟩
  have hparts := decoded.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  let nodeValue : Fin decoded.seed.nodeCount →
      decoded.seed.state.base.state.QuotientDomain :=
    fun node ↦ Quotient.mk decoded.seed.state.base.state.nodeSetoid node
  have hsatParts := hparts.1
  simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hsatParts
  have hvalid : decoded.seed.state.base.equalityClosureValidB = true :=
    hsatParts.1.1.1.1
  have hbaseRealized : decoded.seed.state.base.state.RealizedBy
      decoded.seed.state.base.state.quotientCanonical nodeValue :=
    decoded.seed.state.base.checkEqSat_realizes hparts.1
  have hapartSound := decoded.seed.state.apartSeparatedB_sound
    hvalid decoded.seed.apart_check
  have hdistinctRealized : decoded.seed.state.state.RealizedBy
      decoded.seed.state.base.state.quotientCanonical nodeValue := by
    refine ⟨hbaseRealized, ?_⟩
    intro left right hlisted hequal
    exact hapartSound (left, right) hlisted (Quotient.exact hequal)
  letI : Nonempty decoded.seed.state.base.state.QuotientDomain :=
    ⟨Quotient.mk decoded.seed.state.base.state.nodeSetoid
      (Classical.choice (inferInstance : Nonempty (Fin decoded.seed.nodeCount)))⟩
  refine ⟨nodeValue ∘ decoded.seed.roots, inferInstance,
    decoded.seed.state.base.checkEqSat_models hparts.1,
    decoded.seed.state.base.checkCardinalityDefs_sound decoded.definitions hparts.2,
    ?_⟩
  exact decoded.seed.abox.abox.models_of_seeded decoded.seed.state.state
    decoded.seed.roots decoded.seed.state.base.state.quotientCanonical nodeValue
    decoded.seed.seeded hdistinctRealized
    (decoded.seed.proxySingletonsB_sound hvalid decoded.singleton_proxies)
    (decoded.seed.negativeRolesB_sound hvalid decoded.negative_roles)

theorem DecodedNativeABoxCardinalitySatCertificate.satisfiable
    (decoded : DecodedNativeABoxCardinalitySatCertificate) :
    decoded.seed.abox.abox.SatisfiableWithCardinality
      decoded.seed.state.base.base.ontology decoded.definitions := by
  rcases decoded.canonical_model with
    ⟨value, hdomain, hontology, hdefinitions, habox⟩
  exact ⟨decoded.seed.state.base.state.QuotientDomain,
    decoded.seed.state.base.state.quotientCanonical, value,
    hdomain, hontology, hdefinitions, habox⟩

theorem DecodedNativeABoxCardinalitySatCertificate.models_exact_definitions
    (decoded : DecodedNativeABoxCardinalitySatCertificate) :
    decoded.seed.state.base.state.quotientCanonical.modelsCardinalityDefsExact
      decoded.exactDefinitions := by
  have hparts := decoded.cardinality
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true, FiniteEqCertificate.checkEqSat] at hparts
  exact decoded.seed.state.base.checkCardinalityDefsExact_sound
    hparts.1.1.1.1.1 decoded.exactDefinitions decoded.exact

inductive WireNativeABoxCardinalityDecisionEvidence where
  | sat (certificate : WireNativeABoxCardinalitySatCertificate)
  | unsat (refutation : WireNativeABoxCardinalityRefutation)
deriving FromJson, ToJson, Repr

structure WireNativeABoxCardinalityDecisionCertificate where
  version : Nat
  evidence : WireNativeABoxCardinalityDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedNativeABoxCardinalityDecision where
  | sat (certificate : DecodedNativeABoxCardinalitySatCertificate)
  | unsat (refutation : DecodedNativeABoxCardinalityRefutation)

def WireNativeABoxCardinalityDecisionCertificate.decode
    (wire : WireNativeABoxCardinalityDecisionCertificate) :
    Except String DecodedNativeABoxCardinalityDecision := do
  if wire.version != 1 then
    throw s!"unsupported native ABox cardinality decision certificate version {wire.version}"
  match wire.evidence with
  | .sat certificate => return .sat (← certificate.decode)
  | .unsat refutation => return .unsat (← refutation.decode)

def WireNativeABoxCardinalityDecisionCertificate.check
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedNativeABoxCardinalityDecision.SemanticallyValid :
    DecodedNativeABoxCardinalityDecision → Prop
  | .sat certificate => certificate.seed.abox.abox.SatisfiableWithCardinality
      certificate.seed.state.base.base.ontology certificate.definitions
  | .unsat refutation =>
      ¬refutation.initial.initial.seed.abox.abox.SatisfiableWithCardinality
        refutation.initial.initial.seed.state.base.base.ontology refutation.definitions

theorem DecodedNativeABoxCardinalityDecision.semantic_valid
    (decoded : DecodedNativeABoxCardinalityDecision) : decoded.SemanticallyValid := by
  cases decoded with
  | sat certificate => exact certificate.satisfiable
  | unsat refutation => exact refutation.unsatisfiable

#print axioms DecodedNativeABoxSeed.proxySingletonsB_sound
#print axioms DecodedNativeABoxSeed.negativeRolesB_sound
#print axioms DecodedNativeABoxSatCertificate.satisfiable
#print axioms DecodedNativeABoxDecision.semantic_valid
#print axioms DecodedNativeABoxCardinalitySatCertificate.satisfiable
#print axioms DecodedNativeABoxCardinalitySatCertificate.canonical_model
#print axioms DecodedNativeABoxCardinalitySatCertificate.models_exact_definitions
#print axioms DecodedNativeABoxCardinalityDecision.semantic_valid

end ContextCalculus.Hypertableau
