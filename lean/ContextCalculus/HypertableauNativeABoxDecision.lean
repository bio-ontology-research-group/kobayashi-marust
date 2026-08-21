import ContextCalculus.HypertableauNativeABoxProjection
import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauCardinalityDistinctCertificate
import ContextCalculus.HypertableauCardinalityRuntimeSearch

/-!
# Native-ABox hypertableau decision semantics

This module states the actual model-existence proposition for a normalized
TBox together with KM's native named-individual ABox. It then composes a checked
finite equality model, native-root seed preservation, explicit inequality
separation, singleton proxies, and negative role assertions into one witness of
that proposition.
-/

namespace ContextCalculus.Hypertableau

def NativeABox.SatisfiableWith
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ I.models ontology ∧ abox.models I value

def NativeABox.SatisfiableWithCardinality
    (abox : NativeABox Individual Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role)
      (value : Individual → Domain),
    Nonempty Domain ∧ I.models ontology ∧
      I.modelsCardinalityDefs definitions ∧ abox.models I value

/-- Semantic contract for an initial equality-refutation state. Every model of
the source ABox can be extended to values for all finite search nodes that
realize the exact initial state. A wire checker will establish this contract
from the ordered native roots and the absence of non-ABox seed facts. -/
def NativeABox.InitializesEqState
    (abox : NativeABox Individual Concept Role)
    (state : EqState Node Concept Role) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role)
      [Nonempty Domain] (value : Individual → Domain),
    abox.models I value → ∃ nodeValue : Node → Domain,
      state.RealizedBy I nodeValue

def NativeABox.ExactEqSeed
    (abox : NativeABox Individual Concept Role)
    (state : EqState Node Concept Role) (root : Individual → Node) : Prop :=
  (∀ node literal, state.base.label node literal ↔
    ∃ individual concept,
      node = root individual ∧
      concept ∈ abox.proxies individual ++ abox.assertions individual ∧
      literal = .pos concept) ∧
  (∀ role source target, state.base.edge role source target ↔
    ∃ assertion ∈ abox.roleAssertions,
      role = assertion.1 ∧ source = root assertion.2.1 ∧
        target = root assertion.2.2) ∧
  (∀ role filler node, ¬state.base.obligation role filler node) ∧
  (∀ left right, state.equiv left right ↔ left = right)

def NativeABox.ExactDistinctSeed
    (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role)
    (root : Individual → Node) : Prop :=
  abox.ExactEqSeed state.base root ∧
  ∀ left right, state.apart left right →
    ∃ pair ∈ abox.different,
      (left = root pair.1 ∧ right = root pair.2) ∨
      (left = root pair.2 ∧ right = root pair.1)

def NativeABox.InitializesDistinctState
    (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role) : Prop :=
  ∀ (Domain : Type) (I : Interp Domain Concept Role)
      [Nonempty Domain] (value : Individual → Domain),
    abox.models I value → ∃ nodeValue : Node → Domain,
      state.RealizedBy I nodeValue

theorem NativeABox.ExactDistinctSeed.initializes
    (abox : NativeABox Individual Concept Role)
    (state : DistinctEqState Node Concept Role) (root : Individual → Node)
    (hroot : Function.Injective root)
    (hexact : abox.ExactDistinctSeed state root) :
    abox.InitializesDistinctState state := by
  intro Domain I _ value habox
  classical
  let fallback : Domain := Classical.choice (inferInstance : Nonempty Domain)
  let nodeValue : Node → Domain := Function.extend root value (fun _ => fallback)
  have hrootValue : ∀ individual, nodeValue (root individual) = value individual :=
    fun individual => hroot.extend_apply value (fun _ => fallback) individual
  have hbase : state.base.RealizedBy I nodeValue := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro node literal hlabel
      rcases (hexact.1.1 node literal).1 hlabel with
        ⟨individual, concept, rfl, hconcept, rfl⟩
      rcases List.mem_append.mp hconcept with hproxy | hassertion
      · simpa [Interp.satLit, hrootValue] using
          (habox.1 individual concept hproxy (value individual)).2 rfl
      · simpa [Interp.satLit, hrootValue] using
          habox.2.1 individual concept hassertion
    · intro role source target hedge
      rcases (hexact.1.2.1 role source target).1 hedge with
        ⟨assertion, hassertion, rfl, rfl, rfl⟩
      simpa [hrootValue] using habox.2.2.2.1 assertion hassertion
    · intro role filler node hobligation
      exact (hexact.1.2.2.1 role filler node hobligation).elim
    · intro left right hequivalent
      exact congrArg nodeValue ((hexact.1.2.2.2 left right).1 hequivalent)
  refine ⟨nodeValue, ⟨hbase, ?_⟩⟩
  intro left right hapart hequal
  rcases hexact.2 left right hapart with
    ⟨pair, hpair, horientation⟩
  have hdifferent := habox.2.2.1 pair hpair
  rcases horientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdifferent (by simpa [hrootValue] using hequal)
  · exact hdifferent (by simpa [hrootValue] using hequal.symm)

theorem NativeABox.ExactEqSeed.initializes
    (abox : NativeABox Individual Concept Role)
    (state : EqState Node Concept Role) (root : Individual → Node)
    (hroot : Function.Injective root) (hexact : abox.ExactEqSeed state root) :
    abox.InitializesEqState state := by
  intro Domain I _ value habox
  classical
  let fallback : Domain := Classical.choice (inferInstance : Nonempty Domain)
  let nodeValue : Node → Domain := Function.extend root value (fun _ => fallback)
  have hrootValue : ∀ individual, nodeValue (root individual) = value individual :=
    fun individual => hroot.extend_apply value (fun _ => fallback) individual
  refine ⟨nodeValue, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · intro node literal hlabel
    rcases (hexact.1 node literal).1 hlabel with
      ⟨individual, concept, rfl, hconcept, rfl⟩
    rcases List.mem_append.mp hconcept with hproxy | hassertion
    · simpa [Interp.satLit, hrootValue] using
        (habox.1 individual concept hproxy (value individual)).2 rfl
    · simpa [Interp.satLit, hrootValue] using
        habox.2.1 individual concept hassertion
  · intro role source target hedge
    rcases (hexact.2.1 role source target).1 hedge with
      ⟨assertion, hassertion, rfl, rfl, rfl⟩
    simpa [hrootValue] using habox.2.2.2.1 assertion hassertion
  · intro role filler node hobligation
    exact (hexact.2.2.1 role filler node hobligation).elim
  · intro left right hequivalent
    exact congrArg nodeValue ((hexact.2.2.2 left right).1 hequivalent)

theorem FiniteEqRefutationTree.check_native_abox_unsatisfiable
    (tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (hinitial : abox.InitializesEqState certificate.state)
    (hcheck : tree.check certificate = true) :
    ¬abox.SatisfiableWith certificate.base.ontology := by
  rintro ⟨Domain, I, value, hdomain, hmodels, habox⟩
  letI : Nonempty Domain := hdomain
  rcases hinitial Domain I value habox with ⟨nodeValue, hrealized⟩
  exact tree.check_unsatisfiable certificate hcheck
    ⟨Domain, I, nodeValue, hmodels, hrealized⟩

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_native_abox_unsatisfiable
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (hinitial : abox.InitializesDistinctState certificate.state)
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount))
        (value : Individual → Domain),
      Nonempty Domain ∧ I.models certificate.base.base.ontology ∧
        I.modelsCardinalityDefs definitions ∧ abox.models I value := by
  rintro ⟨Domain, I, value, hdomain, hmodels, hcardinality, habox⟩
  letI : Nonempty Domain := hdomain
  rcases hinitial Domain I value habox with ⟨nodeValue, hrealized⟩
  exact tree.checkClosed_unsatisfiable definitions certificate hcheck
    ⟨Domain, I, nodeValue, hmodels, hcardinality, hrealized⟩

def FiniteDistinctEqCertificate.apartSeparatedB
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  certificate.apart.all fun pair =>
    decide (certificate.base.representative pair.1 ≠
      certificate.base.representative pair.2)

theorem FiniteDistinctEqCertificate.apartSeparatedB_sound
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.base.equalityClosureValidB = true)
    (hcheck : certificate.apartSeparatedB = true) :
    ∀ pair ∈ certificate.apart,
      ¬certificate.base.state.equiv pair.1 pair.2 := by
  simp only [FiniteDistinctEqCertificate.apartSeparatedB, List.all_eq_true,
    decide_eq_true_eq] at hcheck
  intro pair hpair hequivalent
  exact hcheck pair hpair
    ((certificate.base.equalityClosureValidB_sound hvalid pair.1 pair.2).1
      hequivalent)

theorem FiniteDistinctEqCertificate.checkEqSat_native_satisfiable
    [Nonempty (Fin nodeCount)]
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (root : Individual → Fin nodeCount)
    (hseeded : abox.SeededIn certificate.state root)
    (hcheck : certificate.base.checkEqSat = true)
    (hapart : certificate.apartSeparatedB = true)
    (hsingletons : abox.ProxySingletons
      certificate.base.state.quotientCanonical
      (fun individual => Quotient.mk certificate.base.state.nodeSetoid
        (root individual)))
    (hnegative : abox.NegativeRoles
      certificate.base.state.quotientCanonical
      (fun individual => Quotient.mk certificate.base.state.nodeSetoid
        (root individual))) :
    abox.SatisfiableWith certificate.base.base.ontology := by
  let nodeValue : Fin nodeCount → certificate.base.state.QuotientDomain :=
    fun node => Quotient.mk certificate.base.state.nodeSetoid node
  have hbaseRealized : certificate.base.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue :=
    certificate.base.checkEqSat_realizes hcheck
  have hparts := hcheck
  simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hparts
  have hvalid : certificate.base.equalityClosureValidB = true :=
    hparts.1.1.1.1
  have hapartSound := certificate.apartSeparatedB_sound hvalid hapart
  have hdistinctRealized : certificate.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue := by
    refine ⟨hbaseRealized, ?_⟩
    intro left right hlisted hequal
    exact hapartSound (left, right) hlisted (Quotient.exact hequal)
  letI : Nonempty certificate.base.state.QuotientDomain :=
    ⟨Quotient.mk certificate.base.state.nodeSetoid
      (Classical.choice (inferInstance : Nonempty (Fin nodeCount)))⟩
  refine ⟨certificate.base.state.QuotientDomain,
    certificate.base.state.quotientCanonical,
    nodeValue ∘ root, inferInstance,
    certificate.base.checkEqSat_models hcheck, ?_⟩
  exact abox.models_of_seeded certificate.state root
    certificate.base.state.quotientCanonical nodeValue hseeded
    hdistinctRealized hsingletons hnegative

/-- The positive cardinality decision branch uses the same checked quotient
model as native-ABox SAT. The additional checker conjunct proves all
cardinality definitions in that exact interpretation. -/
theorem FiniteDistinctEqCertificate.checkEqSatWithCardinality_native_satisfiable
    [Nonempty (Fin nodeCount)]
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (abox : NativeABox Individual (Fin conceptCount) (Fin roleCount))
    (root : Individual → Fin nodeCount)
    (hseeded : abox.SeededIn certificate.state root)
    (hcheck : certificate.base.checkEqSatWithCardinality definitions = true)
    (hapart : certificate.apartSeparatedB = true)
    (hsingletons : abox.ProxySingletons
      certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
        (root individual)))
    (hnegative : abox.NegativeRoles
      certificate.base.state.quotientCanonical
      (fun individual ↦ Quotient.mk certificate.base.state.nodeSetoid
        (root individual))) :
    abox.SatisfiableWithCardinality certificate.base.base.ontology definitions := by
  have hparts := hcheck
  simp only [FiniteEqCertificate.checkEqSatWithCardinality,
    Bool.and_eq_true] at hparts
  let nodeValue : Fin nodeCount → certificate.base.state.QuotientDomain :=
    fun node ↦ Quotient.mk certificate.base.state.nodeSetoid node
  have hbaseRealized : certificate.base.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue :=
    certificate.base.checkEqSat_realizes hparts.1
  have hsatParts := hparts.1
  simp only [FiniteEqCertificate.checkEqSat, Bool.and_eq_true] at hsatParts
  have hvalid : certificate.base.equalityClosureValidB = true :=
    hsatParts.1.1.1.1
  have hapartSound := certificate.apartSeparatedB_sound hvalid hapart
  have hdistinctRealized : certificate.state.RealizedBy
      certificate.base.state.quotientCanonical nodeValue := by
    refine ⟨hbaseRealized, ?_⟩
    intro left right hlisted hequal
    exact hapartSound (left, right) hlisted (Quotient.exact hequal)
  letI : Nonempty certificate.base.state.QuotientDomain :=
    ⟨Quotient.mk certificate.base.state.nodeSetoid
      (Classical.choice (inferInstance : Nonempty (Fin nodeCount)))⟩
  refine ⟨certificate.base.state.QuotientDomain,
    certificate.base.state.quotientCanonical,
    nodeValue ∘ root, inferInstance,
    certificate.base.checkEqSat_models hparts.1,
    certificate.base.checkCardinalityDefs_sound definitions hparts.2, ?_⟩
  exact abox.models_of_seeded certificate.state root
    certificate.base.state.quotientCanonical nodeValue hseeded
    hdistinctRealized hsingletons hnegative

#print axioms FiniteDistinctEqCertificate.checkEqSat_native_satisfiable
#print axioms FiniteDistinctEqCertificate.checkEqSatWithCardinality_native_satisfiable
#print axioms FiniteDistinctEqCertificate.apartSeparatedB_sound
#print axioms FiniteEqRefutationTree.check_native_abox_unsatisfiable
#print axioms NativeABox.ExactEqSeed.initializes
#print axioms NativeABox.ExactDistinctSeed.initializes
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_native_abox_unsatisfiable

end ContextCalculus.Hypertableau
